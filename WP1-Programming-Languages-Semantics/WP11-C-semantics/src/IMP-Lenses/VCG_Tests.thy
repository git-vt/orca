section \<open>Verification Condition Testing\<close>

theory VCG_Tests
  imports Hoare
begin

subsection \<open>Tactics for Theorem Proving\<close>
text \<open>The tactics below are used to prove the validity of complex Hoare triples/expressions
semi-automatically.\<close>

lemmas subst_exp_thms = Const.abs_eq uop.abs_eq bop.abs_eq trop.abs_eq qtop.abs_eq drop_bexp.abs_eq
imp_var.abs_eq subst.abs_eq Ex_expr.abs_eq All_expr.abs_eq
lemmas simp_thms = subst_upd_var_def lens_indep_def

(* FIRST' isn't necessary if you only have one tactic to try; it's meant for lists of tactics.
However, it seems the below setups would need to be revised some other way to use without FIRST'.*)
ML \<open>
fun vcg_match_tac ctxt = (ALLGOALS o REPEAT_ALL_NEW) (CHANGED o TRY o FIRST'
                         [match_tac ctxt @{thms vcg}]);
fun vcg_assms_insert_tac ctxt = (ALLGOALS o FIRST')
                                [Method.insert_tac ctxt (Assumption.all_prems_of ctxt)];
fun vcg_simp_tac ctxt = (ALLGOALS o asm_full_simp_tac) (ctxt addsimps @{thms simp_thms});
(* fun vcg_simp_loop_tac ctxt = ALLGOALS (REPEAT o CHANGED o TRY o FIRST'
                             [asm_full_simp_tac ctxt]); *)
fun vcg_subst_exp_tac ctxt = (ALLGOALS o REPEAT_ALL_NEW) (CHANGED o TRY o FIRST'
                             [EqSubst.eqsubst_tac ctxt [0] @{thms subst_exp_thms}]);

val vcg_tac = vcg_match_tac THEN'
              vcg_assms_insert_tac THEN'
              vcg_simp_tac THEN'
              vcg_subst_exp_tac THEN'
              vcg_simp_tac;

fun vcg_subst_tac ctxt = (ALLGOALS o REPEAT_ALL_NEW) (CHANGED o TRY o FIRST'
                         [EqSubst.eqsubst_tac ctxt [0] @{thms vcg}]);

fun se_subst_tac ctxt = (ALLGOALS o REPEAT_ALL_NEW) (CHANGED o TRY o FIRST'
                        [EqSubst.eqsubst_tac ctxt [0] @{thms symbolic_exec_subst}]);

fun transfer_tac ctxt = ALLGOALS (Transfer.transfer_tac true ctxt);

val se_vcg_tac = ((se_subst_tac THEN' vcg_tac) ORELSE' vcg_tac) (* ORELSE' transfer_tac *);

val hoare_solver_tac = transfer_tac THEN' vcg_simp_tac;
\<close>

lemma 
  "\<lbrace>(VAR var) =\<^sub>e \<guillemotleft>0::int\<guillemotright>\<rbrace>
    var :== exp; IF b THEN C\<^sub>1 ELSE C\<^sub>2
   \<lbrace>(VAR var) =\<^sub>e \<guillemotleft>1\<guillemotright>\<rbrace>"
  apply (tactic "se_vcg_tac @{context}")
oops

lemma "\<lbrace>P\<rbrace>SKIP ; C \<lbrace>Q\<rbrace>"
    apply (tactic "se_vcg_tac @{context}")
oops

lemma
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0::int\<guillemotright>\<rbrace>
          X :== ((VAR X) +\<^sub>e \<guillemotleft>1\<guillemotright>)
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>1\<guillemotright>\<rbrace>"
  by (tactic \<open>vcg_tac @{context}\<close>)

lemma if_true:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0::int\<guillemotright>\<rbrace>
         IF TRUE THEN SKIP ELSE X :== ((VAR X) +\<^sub>e \<guillemotleft>1\<guillemotright>)
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0\<guillemotright>\<rbrace>"
  by (tactic \<open>vcg_tac @{context}\<close>)

lemma if_false:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0::int\<guillemotright>\<rbrace>
         IF FALSE THEN SKIP ELSE X :== ((VAR X) +\<^sub>e \<guillemotleft>1\<guillemotright>)
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>1\<guillemotright>\<rbrace>"
  by (tactic \<open>vcg_tac @{context}\<close>)

lemma swap_test:
  assumes "weak_lens X" and "weak_lens Y" and "weak_lens T"
      and "X \<bowtie> Y" and "X \<bowtie> T" and "Y \<bowtie> T"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0::int\<guillemotright> \<and>\<^sub>e (VAR Y) =\<^sub>e \<guillemotleft>1::int\<guillemotright>\<rbrace>
         T :== (VAR X);
         X :== (VAR Y);
         Y :== (VAR T)
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>1::int\<guillemotright> \<and>\<^sub>e (VAR Y) =\<^sub>e \<guillemotleft>0::int\<guillemotright>\<rbrace>"
  using assms unfolding lens_indep_def subst_upd_var_def
  by hoare_solver
  (* by (tactic \<open>vcg_tac @{context}\<close>) *)
(* The sequential rule needs intermediate condition specifications for the generated schematic
variables; seL4 examples do this manually, as shown in
seL4/verification/l4v/tools/c-parser/testfiles/breakcontinue.thy. Dropping via transfer achieves
the result, but it's not necessarily as efficient as using introduction rules. *)

end
