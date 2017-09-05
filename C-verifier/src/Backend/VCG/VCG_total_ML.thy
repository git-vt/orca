section \<open>ML-level Verification Condition Generator for Total Correctness\<close>

theory VCG_total_ML
  imports "../../Midend-IVL/Isabelle-UTP-Extended/hoare/HoareLogic/TotalCorrectness/Abrupt/utp_hoare_total"
begin

text \<open>@{text \<open>infixl\<close>} rather than @{text \<open>infixr\<close>} for @{text seq} may work better for tactics\<close>
no_notation useq (infixr ";;" 51)
notation useq (infixl ";;" 51)

text \<open>The below definition helps in asserting independence for a group of lenses, as otherwise the
number of assumptions required increases greatly. The original formulation was @{text \<open>\<longrightarrow> a \<bowtie> b\<close>}
but that didn't seem to work so plain conjunction was chosen instead.\<close>
definition \<open>lens_indep_all lenses \<equiv> \<forall>a b. a \<in> lenses \<and> b \<in> lenses \<and> a \<noteq> b \<and> a \<bowtie> b\<close>
(* Definition \<open>lens_indep_all lenses \<equiv> \<forall>a b. {a, b} \<subset> lenses \<and> a \<bowtie> b\<close> is shorter but doesn't work
as well. *)

text \<open>@{thm seq_hoare_r_t} is handled separately as naïve application could cause conflicts/failed
proofs later on.\<close>
lemmas vcg_rules = skip_abr_hoare_r_t assigns_abr_hoare_r'_t assigns_abr_hoare_r_t assert_hoare_r_t
assume_hoare_r_t cond_abr_hoare_r_t cond_hoare_r_t while_invr_hoare_r_t while_hoare_r_t
while_hoare_r'_t
lemmas unfold_thms = lens_indep_def lens_indep_all_def
lemmas others_to_insert = mod_pos_pos_trivial

text \<open>Examples of breaking down theorem conclusions as terms\<close>
ML \<open>
val hoare_rd = @{thm hoare_rd_def};
hoare_rd |> Thm.concl_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst;

val seqr = @{thm seqr.rep_eq};
seqr |> Thm.concl_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst;

val rassume_abr = @{thm rassume_abr_def};
rassume_abr |> Thm.concl_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst;
\<close>

(* FIRST' isn't necessary if you only have one tactic to try; it's meant for lists of tactics. *)
ML \<open>
fun pprint_term ctxt term = Pretty.writeln (Syntax.pretty_term ctxt term)
fun pprint_cterm ctxt cterm = pprint_term ctxt (Thm.term_of cterm)

(* Extracts the program from a Hoare triple. *)
fun dest_hoare_rd (Const (@{const_name hoare_rd}, _) $ _ $ P $ _) = P
  | dest_hoare_rd t = raise TERM ("dest_hoare_rd", [t]);

(* ML-level version of `seq_hoare_r_t[of _ _ true]`; there's also (Drule.)infer_instantiate', but
that requires a proof context. *)
val seq_hoare_r_t' =
  Thm.instantiate' [SOME @{ctyp 'a}] [NONE, NONE, SOME @{cterm true}] @{thm seq_hoare_r_t}

(* Equivalent to `apply (insert assms)`; not needed for rule application, only some {rel,pred}_*
usage *)
fun vcg_insert_assms_tac ctxt = ALLGOALS (Method.insert_tac ctxt (Assumption.all_prems_of ctxt))
fun vcg_insert_others_tac ctxt = ALLGOALS (Method.insert_tac ctxt @{thms others_to_insert})

(* Must come before certain usages of {rel,pred}_*; may be simplest to unfold early on after
assumptions have been inserted. *)
(* TODO: allow supplying extra theorems to the tactic. *)
fun vcg_unfold_tac ctxt = unfold_tac ctxt @{thms unfold_thms}

(* Splits up programs using seq_hoare_r_t; applies  `seq_hoare_r_t[of _ _ true]` when an assumption
is the last command in a goal.
Subgoal.focus elements: {prems, params, asms, concl, context, schematics} *)
fun vcg_seq_split ctxt goal = Subgoal.FOCUS (fn {concl, ...} =>
  case concl |> Thm.term_of |> HOLogic.dest_Trueprop (* |> dest_hoare_rd *) of
    Const (@{const_name hoare_rd}, _) $ _ $
      (Const (@{const_name seqr}, _) $ _ $
        (Const (@{const_name rassume_abr}, _) $ _)) $_
          => resolve_tac ctxt [seq_hoare_r_t'] goal |
    _ => resolve_tac ctxt @{thms seq_hoare_r_t} goal)
  ctxt goal

(* Handles applying most Hoare rules, with the specific exclusion of seq_hoare_r_t
(try match_tac (equivalent to `intro`) rather than resolve_tac (equivalent to `rule`)?)
Using Subgoal.FOCUS messes up the behavior when goals should merge due to certain rules like the
skip rule, etc. that work fine when FOCUS is not used, so we stick with handling that here. *)
(* fun vcg_rule_tac ctxt goal = (REPEAT o CHANGED) (resolve_tac ctxt @{thms vcg_rules} goal) *)
fun vcg_rule_tac ctxt = resolve_tac ctxt @{thms vcg_rules}

fun vcg_rules_tac ctxt = (REPEAT o CHANGED oo FIRST') [vcg_seq_split ctxt, vcg_rule_tac ctxt]
fun vcg_rules_tac' ctxt = vcg_rules_tac ctxt 1

fun vcg_rules_all_tac ctxt = (ALLGOALS o REPEAT_ALL_NEW)
  (CHANGED o FIRST' [vcg_seq_split ctxt, vcg_rule_tac ctxt]) (* TRY doesn't seem of benefit *)
fun vcg_rules_all_tac' ctxt = ALLGOALS (fn goal => (REPEAT o CHANGED) (* TRY doesn't help *)
  (FIRST' [vcg_seq_split ctxt, vcg_rule_tac ctxt] goal))

val vcg_pre_tac = vcg_insert_assms_tac THEN' vcg_insert_others_tac THEN' vcg_unfold_tac
val vcg_tac = vcg_pre_tac (* THEN'
              (* apply rules, but with specific handling for the assumes/etc. cases;
              may also want to stick with partial rule application so we can
              do {pred,rel}_* on the way THEN' *)
              do stuff with {pred,rel}_* *)

(* TODO: Figure out how to determine when all goals are predicates or otherwise not dischargable
normally; at that point we need to start inserting assumptions/etc. and unfolding lemmas.  *)
\<close>

text \<open>Tries discharging the leading subgoals with UTP *_auto methods, stops when it cannot. The
failure is necessary to backtrack in cases where the VCG is applied to subgoals that have schematic
variables and thus results in nasty transfer rules; we have to defer those subgoals and try again
later after hopefully instantiating the schematic variables with the discharging of other subgoals.

I'd prefer calling this from the ML level using case matching on
@{text \<open>Const (@{const_name taut}, _) $ _\<close>} but the ML interface for methods is not trivial to
integrate with regular tactics.\<close>
method vcg_auto = (pred_auto|rel_auto); fail
method vcg_autos = vcg_auto+

end
