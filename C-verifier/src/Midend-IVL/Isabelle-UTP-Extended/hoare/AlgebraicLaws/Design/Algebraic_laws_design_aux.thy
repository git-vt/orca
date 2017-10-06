section \<open>Algebraic laws of programming\<close>

text \<open>In this section we introduce the semantic rules related to the different
      statements of IMP. In the literature this also known as the algebraic laws of programming.
      In our framework we will use these rules in order to optimize a given program written in our
      language, and this before any deductive proof verification activity or formal testing.\<close>

theory Algebraic_laws_design_aux
  imports "../../../theories/Design/utp_designs_more"
begin
  
section \<open>Algebraic laws AUX\<close>

subsection \<open>simpset\<close>
named_theorems udes_comp and udes_cond 
declare urel_comp [udes_comp]
declare urel_cond [udes_cond]  

    
subsection \<open>ok alphabet behavior\<close>
 

lemma unrest_pre_out\<alpha>_abr[unrest]: "out\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>D\<^sub><"
  by (rel_auto)

lemma unrest_post_in\<alpha>_abr[unrest]: "in\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>D\<^sub>>"
  by (rel_auto)

lemma unrest_ok_abrupt_rel_uexpr_lift_cpa[unrest]:
  "$ok \<sharp> \<lceil>P\<rceil>\<^sub>D" "$ok\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>D"
  by (pred_auto)+

lemma unrest_ok_abrupt_rel_usubst_lift_cpa[unrest]:
  "$ok\<acute> \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D" "$ok \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D"
  by rel_auto+

lemma unrest_in_out_rel_ok_abrupt_res_abr [unrest]:
  "$ok \<sharp> (P \<restriction>\<^sub>\<alpha> ok)" "$ok\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> ok)"
  by (simp_all add: rel_var_res_def unrest)

lemma rel_usubst_lift_cpa_in_out_abrupt_ok[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> ($ok) = ($ok)" "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> (\<not>$ok) = (\<not>$ok)"
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> ($ok\<acute>) = ($ok\<acute>)"  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> (\<not>$ok\<acute>) = (\<not>$ok\<acute>)"
  by (simp_all add: usubst unrest)

lemma abrupt_ok_simpl[unrest]:
  "(\<not>$ok;; (P \<turnstile> Q)) = (\<not>$ok)" 
  by rel_auto+

lemma in_ok:
  "($ok) = (utp_expr.var (ok ;\<^sub>L fst\<^sub>L)) "
  by rel_auto
    
lemma out_ok:
  "($ok\<acute>) = (utp_expr.var (ok ;\<^sub>L snd\<^sub>L)) "
  by rel_auto
    
subsection \<open>Healthiness condition behavior\<close>

subsection \<open>Signature behavior\<close>

lemma skip_des_def:
  "II = (\<lceil>II\<rceil>\<^sub>D \<and> $abrupt =\<^sub>u $abrupt\<acute> \<and> $ok =\<^sub>u $ok\<acute>)"
  by rel_auto
   
lemma skip_lift_des_def:
  "\<lceil>II\<rceil>\<^sub>D = ($\<Sigma>\<^sub>D\<acute> =\<^sub>u $\<Sigma>\<^sub>D)"
  by rel_auto 

lemma rel_usubst_lift_des_uexpr_lift_des[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> \<lceil>P\<rceil>\<^sub>D = \<lceil>\<sigma> \<dagger> P\<rceil>\<^sub>D"
  by rel_auto

lemma usubst_lift_des_assigns_lift_des[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>D \<dagger> \<lceil>\<langle>\<rho>\<rangle>\<^sub>a\<rceil>\<^sub>D = \<lceil>\<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>D"
  by (simp add: usubst)

lemma usubst_lift_des_pre_uexpr_lift_des[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>D \<dagger> \<lceil>b\<rceil>\<^sub>D\<^sub>< = \<lceil>\<sigma> \<dagger> b\<rceil>\<^sub>D\<^sub><"
  by (simp add: usubst)

lemma rel_usubst_lift_des_design[usubst]:
  "(\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> (Q \<turnstile> P)) = (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> Q) \<turnstile> (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> P)"
  by (simp add: usubst unrest)

lemma rel_usubst_des_skip_des[usubst]:
  "(\<sigma> \<dagger> II) = ((\<sigma> \<dagger> \<lceil>II\<rceil>\<^sub>D) \<and> (\<sigma> \<dagger> $ok) =\<^sub>u (\<sigma> \<dagger> $ok\<acute>))"
  by rel_auto

lemma usubst_lift_des_skip_lift_des[usubst]:
  "(\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>D \<dagger> \<lceil>II\<rceil>\<^sub>D) = \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>D"
  unfolding skip_r_def
  by (simp add: usubst_lift_des_assigns_lift_des)

declare utp_designs.design_top_left_zero[udes_comp]

lemma assigns_lift_cpa_comp_rel_cpa[udes_comp]:
  assumes "$ok \<sharp> P"
  shows  "(\<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>D;; P) = (\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>D \<dagger> P)"
  apply (insert assms)
  apply rel_auto
  apply blast
done

declare utp_designs.assigns_d_comp[udes_comp]

lemma usubst_cpa_des_cond_abr[usubst]:
  "\<lbrakk> $ok \<sharp> \<sigma>; $ok\<acute> \<sharp> \<sigma> \<rbrakk> \<Longrightarrow>
    \<sigma> \<dagger> (R \<turnstile> bif\<^sub>D b then P else Q eif) =
    (\<sigma> \<dagger> R \<turnstile> (\<sigma> \<dagger> P \<triangleleft> \<sigma> \<dagger> \<lceil>b\<rceil>\<^sub>D\<^sub>< \<triangleright> \<sigma> \<dagger> Q))"
  by (simp add: usubst)
        
    

end
