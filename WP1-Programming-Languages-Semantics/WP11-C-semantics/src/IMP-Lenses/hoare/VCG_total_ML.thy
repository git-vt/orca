section \<open>ML-level Verification Condition Generator for Total Correctness\<close>

theory VCG_total_ML
  imports utp_hoare_total
begin

text \<open>@{text \<open>infixl\<close>} rather than @{text \<open>infixr\<close>} for @{text seq} may work better for tactics\<close>
no_notation useq (infixr ";;" 51)
notation useq (infixl ";;" 51)

text \<open>@{thm seq_hoare_r_t}, @{thm assigns_hoare_r_t}, @{thm while_invr_hoare_r_t}, and
@{thm cond_hoare_r_t} are handled separately as they could cause conflicts/failed proofs later on.\<close>
lemmas vcg_rules = skip_hoare_r_t assigns_hoare_r'_t assert_hoare_r_t assume_hoare_r_t
while_hoare_r_t while_hoare_r'_t
lemmas unfold_thms = lens_indep_def

text \<open>Examples of breaking down theorems as terms\<close>
ML \<open>
val hoare_rd = @{thm hoare_rd_def};
hoare_rd |> Thm.concl_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst;

val seqr = @{thm seqr.rep_eq};
seqr |> Thm.concl_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst;

val rassume_c = @{thm rassume_c_def};
rassume_c |> Thm.concl_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst
\<close>

(* Need to start with seq splitting, applying the `seq_hoare_r_t[of _ _ true]` step when an
assumption is the last command in a goal; then we can apply other rules and such. When we encounter
while loops and if statements we have to try seq splitting again after while/if application as those
statements can have nested sequences of commands (including more while/if statements). *)

(* FIRST' isn't necessary if you only have one tactic to try; it's meant for lists of tactics.
However, it seems the below setups would need to be revised some other way to use without FIRST'.*)
ML \<open>
fun pprint_term ctxt term = Pretty.writeln (Syntax.pretty_term ctxt term)
fun pprint_cterm ctxt cterm = pprint_term ctxt (Thm.term_of cterm)

fun dest_hoare_rd (Const (@{const_name hoare_rd}, _) $ _ $ P $ _) = P
  | dest_hoare_rd t = raise TERM ("dest_hoare_rd", [t]);

(* ML-level version of `seq_hoare_r_t[of _ _ true]`; there's also (Drule.)infer_instantiate', but
that requires a proof context. *)
val seq_hoare_r_t' =
  Thm.instantiate' [SOME @{ctyp 'a}] [NONE, NONE, SOME @{cterm true}] @{thm seq_hoare_r_t}

(* Splits up programs using seq_hoare_r_t; applies  `seq_hoare_r_t[of _ _ true]` when an assumption
is the last command in a goal.
Subgoal.focus elements: {prems, params, asms, concl, context, schematics} *)
fun vcg_seq_split ctxt goal = (REPEAT o CHANGED) (Subgoal.FOCUS (fn {concl, ...} =>
  case concl |> Thm.term_of |> HOLogic.dest_Trueprop |> dest_hoare_rd of
    Const (@{const_name seqr}, _) $ _ $
      (Const (@{const_name rassume_c}, _) $ _)
        => resolve_tac ctxt [seq_hoare_r_t'] goal |
    _ => resolve_tac ctxt @{thms seq_hoare_r_t} goal)
  ctxt goal)

(* Handles applying most Hoare rules, with the specific exclusion of seq_hoare_r_t and
assigns_hoare_r_t [though one version calls through to it just in case]
(try match_tac (equivalent to `intro`) rather than resolve_tac (equivalent to `rule`)?)
Using Subgoal.FOCUS
messes up the behavior when goals should merge due to certain rules like the skip rule, etc. that
work fine when FOCUS is not used. *)
fun vcg_rule_tac ctxt goal = (REPEAT o CHANGED) (resolve_tac ctxt @{thms vcg_rules} goal)

fun vcg_rule_wc_tac ctxt goal = (REPEAT o CHANGED) (Subgoal.FOCUS (fn {concl, ...} =>
  case concl |> Thm.term_of |> HOLogic.dest_Trueprop |> dest_hoare_rd of
    Const (@{const_name While_inv}, _) $ _ $ _ $ _
      => (resolve_tac ctxt @{thms while_invr_hoare_r_t} goal THEN vcg_seq_split ctxt goal) |
    Const (@{const_name trop}, _) $
      Const (@{const_name If}, _) $ _ $ _ $ _
        => (resolve_tac ctxt @{thms cond_hoare_r_t} goal THEN (* need to handle both cond goals *)
            vcg_seq_split ctxt goal THEN
            vcg_seq_split ctxt (goal + 1)) |
    _ => no_tac)
  ctxt goal)

(* Equivalent to `apply (insert assms)`;
not needed for rule application, only some {rel,pred}_* usage *)
fun vcg_insert_assms_tac ctxt = (ALLGOALS o FIRST')
                                [Method.insert_tac ctxt (Assumption.all_prems_of ctxt)]

(* Must come before certain usages of {rel,pred}_*  *)
fun vcg_unfold_tac ctxt = unfold_tac ctxt @{thms unfold_thms}

val vcg_tac =(*  vcg_rule_tac THEN' *)
              vcg_insert_assms_tac THEN'
              (* apply rules, but with specific handling for the assumes/etc. cases;
              may also want to stick with partial rule application so we can
              do {pred,rel}_* on the way THEN' *)
              vcg_unfold_tac (* THEN'
              do stuff with {pred,rel}_* *)
\<close>

lemma increment_manual:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x \<Midarrow> 0;;
  (&x =\<^sub>u 0 \<and> &y =\<^sub>u 5)\<^sup>\<top>\<^sup>C;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x \<Midarrow> &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>D"
  apply (insert assms)
  apply (rule seq_hoare_r_t)
   apply (rule seq_hoare_r_t[of _ _ true])
    apply rel_auto (* seq rule gives us a value of true in postcondition, which is trivial *)
   apply (rule assume_hoare_r_t)
    apply (rule skip_hoare_r_t)
   apply rel_auto
  apply (rule while_invr_hoare_r_t)
    apply (rule assigns_hoare_r_t)
    unfolding lens_indep_def
    apply pred_auto
   apply pred_auto
  apply pred_auto
  done

lemma increment_tactic:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x \<Midarrow> 0;;
  (&x =\<^sub>u 0 \<and> &y =\<^sub>u 5)\<^sup>\<top>\<^sup>C;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x \<Midarrow> &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>D"
  apply (tactic \<open>vcg_seq_split @{context} 1\<close>)
  apply rel_auto
  apply (tactic \<open>vcg_rule_tac @{context} 1\<close>)
  apply rel_auto
  apply (tactic \<open>vcg_rule_wc_tac @{context} 1\<close>)
  apply rel_auto
oops
term "II"
ML \<open>
@{term "while b invr i do c od"};
pprint_cterm @{context} @{cterm "\<lbrace>p\<rbrace>C;;c\<^sup>\<top>\<^sup>C\<lbrace>q\<rbrace>\<^sub>D"}
\<close>

end
