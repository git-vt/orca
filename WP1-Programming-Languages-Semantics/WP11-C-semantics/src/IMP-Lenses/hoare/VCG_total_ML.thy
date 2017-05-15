section \<open>ML-level Verification Condition Generator for Total Correctness\<close>

theory VCG_total_ML
  imports utp_hoare_total
begin

lemmas subst_exp_thms = uop.abs_eq bop.abs_eq trop.abs_eq qtop.abs_eq subst.abs_eq
lemmas simp_thms = lens_indep_def

(* FIRST' isn't necessary if you only have one tactic to try; it's meant for lists of tactics.
However, it seems the below setups would need to be revised some other way to use without FIRST'.*)
ML \<open>
@{cterm "(1::nat) + 2"};
let
  val chead = @{cterm "P :: unit \<Rightarrow> nat \<Rightarrow> bool"}
  val cargs = [@{cterm "()"}, @{cterm "3::nat"}]
in
  Drule.list_comb (chead, cargs)
end;

(* Equivalent to `apply (insert assms)`;
not needed for rule application, only some {rel,pred}_* usage *)
fun vcg_assms_insert_tac ctxt = (ALLGOALS o FIRST')
                                [Method.insert_tac ctxt (Assumption.all_prems_of ctxt)];

(* fun vcg_match_tac ctxt = (ALLGOALS o REPEAT_ALL_NEW) (CHANGED o TRY o FIRST'
                         [match_tac ctxt @{thms (* vcg *)_}]); *)
fun vcg_simp_tac ctxt = (ALLGOALS o asm_full_simp_tac) (ctxt addsimps @{thms simp_thms});
fun vcg_subst_exp_tac ctxt = (ALLGOALS o REPEAT_ALL_NEW) (CHANGED o TRY o FIRST'
                             [EqSubst.eqsubst_tac ctxt [0] @{thms subst_exp_thms}]);

val vcg_tac = (* vcg_match_tac THEN' *)
              vcg_assms_insert_tac THEN'
              vcg_simp_tac THEN'
              vcg_subst_exp_tac THEN'
              vcg_simp_tac;

fun vcg_subst_tac ctxt = (ALLGOALS o REPEAT_ALL_NEW) (CHANGED o TRY o FIRST'
                         [EqSubst.eqsubst_tac ctxt [0] @{thms (* vcg *)_}]);

fun transfer_tac ctxt = ALLGOALS (Transfer.transfer_tac true ctxt);

val hoare_solver_tac = transfer_tac THEN' vcg_simp_tac;
\<close>

end
