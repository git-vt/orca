section \<open>Verification Condition Testing\<close>

theory VCG_Tests
  imports Hoare
begin

subsection \<open>Tactics for Theorem Proving\<close>
text \<open>The tactics below are used to prove the validity of complex Hoare triples/expressions
semi-automatically.\<close>

lemmas subst_exp_thms = Const.abs_eq bop.abs_eq drop_bexp.abs_eq subst.abs_eq uop.abs_eq
(* subst_upd_var_def lens_indep_def *)

ML \<open>
fun vcg_match_tac ctxt = (ALLGOALS o REPEAT_ALL_NEW) (CHANGED o TRY o FIRST'
                         [match_tac ctxt @{thms vcg}]);
fun vcg_assms_insert_tac ctxt = (ALLGOALS) (FIRST'
                                [Method.insert_tac ctxt (Assumption.all_prems_of ctxt)]);
fun vcg_simp_tac ctxt = asm_full_simp_tac ctxt 1;
fun vcg_simp_loop_tac ctxt = (ALLGOALS) (REPEAT o CHANGED o TRY o FIRST'
                              [asm_full_simp_tac ctxt]);
fun vcg_subst_exp_tac ctxt = (ALLGOALS o REPEAT_ALL_NEW) (CHANGED o TRY o FIRST'
                             [EqSubst.eqsubst_tac ctxt [0] @{thms subst_exp_thms}]);

val vcg_tac = vcg_match_tac THEN'
              vcg_assms_insert_tac THEN'
              vcg_simp_tac THEN'
              vcg_subst_exp_tac THEN'
              vcg_simp_loop_tac;

val vcg_tacx = vcg_match_tac THEN'
              vcg_assms_insert_tac THEN'
              vcg_simp_tac THEN'
              vcg_subst_exp_tac THEN'
              vcg_simp_tac;
\<close>

lemma
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0::int\<guillemotright>\<rbrace> X :== ((VAR X) +\<^sub>e \<guillemotleft>1\<guillemotright>) \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>1\<guillemotright>\<rbrace>"
  by (tactic \<open>vcg_tac @{context}\<close>)

lemma if_true:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0::int\<guillemotright>\<rbrace>
         IF TRUE THEN SKIP ELSE (X :== ((VAR X) +\<^sub>e \<guillemotleft>1\<guillemotright>))
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0\<guillemotright>\<rbrace>"
  by (tactic \<open>vcg_tac @{context}\<close>)

lemma if_false:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0::int\<guillemotright>\<rbrace>
         IF TRUE THEN SKIP ELSE (X :== ((VAR X) +\<^sub>e \<guillemotleft>1\<guillemotright>))
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0\<guillemotright>\<rbrace>"
  by (tactic \<open>vcg_tac @{context}\<close>)

lemma swap_test:
  assumes "weak_lens X" and "weak_lens Y" and "weak_lens T"
  and "X \<bowtie> Y" and "X \<bowtie> T" and "Y \<bowtie> T"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0::int\<guillemotright> \<and>\<^sub>e (VAR Y) =\<^sub>e \<guillemotleft>1::int\<guillemotright>\<rbrace>
         T :== (VAR X);
         X :== (VAR Y);
         Y :== (VAR T)
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>1::int\<guillemotright> \<and>\<^sub>e (VAR Y) =\<^sub>e \<guillemotleft>0::int\<guillemotright>\<rbrace>"
  apply (tactic \<open>vcg_tacx @{context}\<close>)
oops (* The sequential rule needs intermediate condition specifications for the generated schematic
variables; seL4 examples do this manually, as shown in
seL4/verification/l4v/tools/c-parser/testfiles/breakcontinue.thy *)

end
