
section "Auxiliary algebraic laws for abrupt designs"
theory algebraic_laws_fault_aux
imports "../../../theories/Fault/utp_fault_designs"
 
begin
named_theorems uflt_simpl and uflt_cond and uflt_comp and uflt_lens
subsection {*THM setup*}
declare design_condr[urel_cond] 


subsection {*abrupt alphabet behavior*}

lemma assigns_flt_alpha:
  "(fault :== (\<not> &fault)) = (\<lceil>II\<rceil>\<^sub>F\<^sub>L\<^sub>T \<and>  $fault\<acute> =\<^sub>u (\<not>$fault) \<and> $ok =\<^sub>u $ok\<acute>)"
  "(ok :== (\<not> &ok)) = (\<lceil>II\<rceil>\<^sub>F\<^sub>L\<^sub>T \<and>  $fault\<acute> =\<^sub>u $fault \<and> $ok =\<^sub>u (\<not>$ok\<acute>))"
  by rel_auto+

lemma vwb_of_fault[simp]: 
  "vwb_lens ok" "vwb_lens fault"
  by simp_all

lemma unrest_pre_out\<alpha>_flt[unrest]: "out\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub><"
  by (transfer, auto simp add: out\<alpha>_def lens_prod_def)
 
lemma unrest_post_in\<alpha>_flt[unrest]: "in\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub>>"
  by (transfer, auto simp add: in\<alpha>_def lens_prod_def)

lemma unrest_ok_fault_rel_uexpr_lift_cpf[unrest]:
  "$ok \<sharp> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T" "$ok\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T"
  "$fault \<sharp> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T" "$fault\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T"
  by (pred_auto)+

lemma unrest_ok_fault_rel_usubst_lift_cpf[unrest]:
  "$ok\<acute> \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T" "$ok \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T"
  "$fault\<acute> \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T" "$fault \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T"               
  by rel_auto+

lemma unrest_in_out_rel_ok_fault_res_flt [unrest]:
  "$ok \<sharp> (P \<restriction>\<^sub>\<alpha> ok)" "$ok\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> ok)"  
  "$fault \<sharp> (P \<restriction>\<^sub>\<alpha> fault)" "$fault\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> fault)"
  by (simp_all add: rel_var_res_def unrest)

lemma uflt_alphabet_unrest[unrest]:(*FIXEME:These laws should be generated automatically by alphabet backend since all the fields of alphabet are independant*)
  "$ok\<acute> \<sharp> $fault\<acute>" "$ok \<sharp> $fault"
  "$ok\<acute> \<sharp> $x" "$ok \<sharp> $fault\<acute>"
  "$fault\<acute> \<sharp> $ok\<acute>" "$fault \<sharp> $ok "
  "$fault \<sharp> $ok\<acute>" "$fault\<acute> \<sharp> $x"
  by pred_simp+

lemma cpf_ord [usubst]:
  "$ok \<prec>\<^sub>v $ok\<acute>" "$abrupt \<prec>\<^sub>v $abrupt\<acute>" "$ok \<prec>\<^sub>v $abrupt\<acute>" 
  "$ok \<prec>\<^sub>v $abrupt" "$ok\<acute> \<prec>\<^sub>v $abrupt\<acute>" "$ok\<acute> \<prec>\<^sub>v $abrupt" 
  by (simp_all add: var_name_ord_def)

lemma rel_usubst_lift_cpf_in_out_fault_ok[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T \<dagger> $fault = $fault" "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T \<dagger> (\<not>$fault) = (\<not>$fault)"
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T \<dagger> ($ok) = ($ok)" "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T \<dagger> (\<not>$ok) = (\<not>$ok)" 
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T \<dagger> ($fault\<acute>) = (($fault\<acute>))" "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T \<dagger> (\<not>$fault\<acute>) = (\<not>$fault\<acute>)"
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T \<dagger> ($ok\<acute>) = ($ok\<acute>)"  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T \<dagger> (\<not>$ok\<acute>) = (\<not>$ok\<acute>)" 
  by (simp_all add: usubst unrest)

lemma abrupt_ok_simpl[uflt_comp]:
  "($fault ;; Simpl\<^sub>F\<^sub>L\<^sub>T P) = $fault" "(\<not>$ok ;; Simpl\<^sub>F\<^sub>L\<^sub>T P) = (\<not>$ok)" 
  "($fault ;; (P \<turnstile> Q)) = $fault" "(\<not>$ok ;; (P \<turnstile> Q)) = (\<not>$ok)"
  "(\<not>$fault ;; Simpl\<^sub>F\<^sub>L\<^sub>T P) = (\<not>$fault)" "(\<not>$ok ;; Simpl\<^sub>F\<^sub>L\<^sub>T P) = (\<not>$ok)" 
  "(\<not>$fault ;; (P \<turnstile> Q)) = (\<not>$fault)" "(\<not>$ok ;; (P \<turnstile> Q)) = (\<not>$ok)"
  "($fault\<acute> ;; Simpl\<^sub>F\<^sub>L\<^sub>T P) = $fault\<acute>" 
  "(\<not>$fault\<acute> ;; Simpl\<^sub>F\<^sub>L\<^sub>T P) = (\<not>$fault\<acute>)" 
  by rel_auto+

lemma simpl_flt_in_ok:
  "Simpl\<^sub>F\<^sub>L\<^sub>T ($ok) = ((\<not>$fault \<and> ($ok \<Rightarrow>$ok\<acute>)) \<or> (II))" 
  by rel_auto

lemma  simpl_flt_our_ok:
  "Simpl\<^sub>F\<^sub>L\<^sub>T ($ok\<acute>) = ((\<not>$fault \<and> ($ok \<Rightarrow>$ok\<acute>)) \<or> (II))" 
  by rel_auto

lemma simpl_flt_in_abrupt:
  "Simpl\<^sub>F\<^sub>L\<^sub>T ($fault) = ((\<not>$fault \<and> ($ok \<Rightarrow>($ok\<acute> \<and> $fault))) \<or> ($fault \<and> II))" 
  by rel_auto

lemma simpl_flt_alt_def:
  "Simpl\<^sub>F\<^sub>L\<^sub>T (P) = ((\<not>$fault \<and> ($ok \<Rightarrow>($ok\<acute> \<and> P))) \<or> ($fault \<and> II))" 
  by rel_auto

subsection {*Healthiness condition behavior*}

lemma rel_usubst_cpf_c3_flt[usubst]: 
  assumes "$ok \<sharp> \<sigma>" "$ok\<acute> \<sharp> \<sigma> "
  shows "\<sigma> \<dagger> C3_flt(P) = (\<sigma> \<dagger> P \<triangleleft> \<sigma> \<dagger> (\<not>$fault) \<triangleright> (\<sigma> \<dagger> II))"
  using assms unfolding C3_flt_def  
  by (simp add: usubst) 

lemma Simpl_flt_idem[simp]: "Simpl\<^sub>F\<^sub>L\<^sub>T(Simpl\<^sub>F\<^sub>L\<^sub>T(P)) = Simpl\<^sub>F\<^sub>L\<^sub>T(P)"
  by (rel_auto)

lemma simpl_flt_Idempotent: "Idempotent Simpl\<^sub>F\<^sub>L\<^sub>T"
  by (simp add: Idempotent_def)

lemma Simpl_flt_mono: "P \<sqsubseteq> Q \<Longrightarrow> Simpl\<^sub>F\<^sub>L\<^sub>T(P) \<sqsubseteq> Simpl\<^sub>F\<^sub>L\<^sub>T(Q)"
  by (rel_auto)

lemma simpl_flt_Monotonic: "Monotonic Simpl\<^sub>F\<^sub>L\<^sub>T"
  by (simp add: Monotonic_def Simpl_flt_mono)

lemma simpl_flt_def: 
  "Simpl\<^sub>F\<^sub>L\<^sub>T(P) = ((\<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> P) \<triangleleft> \<not>$fault \<triangleright>  II)"
  unfolding C3_flt_def ..

lemma simpl_flt_condr[uflt_simpl]: 
  "Simpl\<^sub>F\<^sub>L\<^sub>T(P \<triangleleft> b \<triangleright> Q) = (Simpl\<^sub>F\<^sub>L\<^sub>T(P) \<triangleleft> b \<triangleright> Simpl\<^sub>F\<^sub>L\<^sub>T(Q))"
  unfolding simpl_flt_def 
  by (simp add: urel_cond)

lemma simpl_abr_skip_abr[uflt_simpl]: 
  "Simpl\<^sub>F\<^sub>L\<^sub>T(SKIP\<^sub>F\<^sub>L\<^sub>T) = (SKIP\<^sub>F\<^sub>L\<^sub>T)"
  by (simp add: urel_cond urel_defs) 
       
lemma simpl_flt_assign_flt[uflt_simpl]: 
  "Simpl\<^sub>F\<^sub>L\<^sub>T(\<langle>\<sigma>\<rangle>\<^sub>F\<^sub>L\<^sub>T) = (\<langle>\<sigma>\<rangle>\<^sub>F\<^sub>L\<^sub>T)"
  by (simp add: urel_cond urel_defs)

lemma simpl_flt_form: 
  "Simpl\<^sub>F\<^sub>L\<^sub>T(P) = (((\<not>$fault) \<and> (\<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> (P)))  \<or> ($fault \<and> II))"
  by rel_auto 

lemma abrupt_simpl_flt[uflt_simpl]:
  "($fault \<and> Simpl\<^sub>F\<^sub>L\<^sub>T(P)) = ($fault \<and>II)"
   by rel_auto

lemma nabrupt_simpl_flt[uflt_simpl]:
  "(\<not>$fault \<and> Simpl\<^sub>F\<^sub>L\<^sub>T(P)) = (\<not>$fault \<and> (\<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> (P)))"
  by (rel_auto)

definition design_flt_sup :: "('\<alpha>,'\<beta>) rel_cpf set \<Rightarrow> ('\<alpha>,'\<beta>) rel_cpf" ("\<Sqinter>\<^sub>F\<^sub>L\<^sub>T_" [900] 900) where
"\<Sqinter>\<^sub>F\<^sub>L\<^sub>T A = (if (A = {}) then \<top>\<^sub>F\<^sub>L\<^sub>T else \<Sqinter> A)"

lemma simpl_flt_Continuous: "Continuous Simpl\<^sub>F\<^sub>L\<^sub>T"
  unfolding Continuous_def SUP_def apply rel_simp
  unfolding  SUP_def 
  apply transfer apply auto 
done

lemma simpl_flt_R3_conj: 
  "Simpl\<^sub>F\<^sub>L\<^sub>T(P \<and> Q) = (Simpl\<^sub>F\<^sub>L\<^sub>T(P) \<and> Simpl\<^sub>F\<^sub>L\<^sub>T(Q))"
  by (rel_auto)

lemma simpl_flt_disj: 
  "Simpl\<^sub>F\<^sub>L\<^sub>T(P \<or> Q) = (Simpl\<^sub>F\<^sub>L\<^sub>T(P) \<or> Simpl\<^sub>F\<^sub>L\<^sub>T(Q))"
  by (rel_auto)

lemma Simpl_flt_USUP:
  assumes "A \<noteq> {}"
  shows "Simpl\<^sub>F\<^sub>L\<^sub>T(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> Simpl\<^sub>F\<^sub>L\<^sub>T(P(i)))"
  using assms by (rel_auto)

lemma design_flt_sup_non_empty [simp]:  
  "A \<noteq> {} \<Longrightarrow> \<Sqinter>\<^sub>F\<^sub>L\<^sub>T A = \<Sqinter> A"
  by (simp add: design_flt_sup_def)

subsection {*Signature behavior*}

lemma design_top_flt:
  "(P \<turnstile> Q) \<sqsubseteq> \<top>\<^sub>F\<^sub>L\<^sub>T"
  by (rel_auto)

lemma design_flt_sup_empty [simp]: 
  "\<Sqinter>\<^sub>F\<^sub>L\<^sub>T {} = \<top>\<^sub>F\<^sub>L\<^sub>T"
  by (simp add: design_flt_sup_def)


abbreviation design_inf :: "('\<alpha>, '\<beta>) rel_des set \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" ("\<Squnion>\<^sub>F\<^sub>L\<^sub>T_" [900] 900) where
"\<Squnion>\<^sub>F\<^sub>L\<^sub>T A \<equiv> \<Squnion> A"

lemma design_bottom_flt:
  "\<bottom>\<^sub>F\<^sub>L\<^sub>T \<sqsubseteq> (P \<turnstile> Q)"
  by simp

lemma Simpl_flt_UINF:
  assumes "A \<noteq> {}"
  shows "Simpl\<^sub>F\<^sub>L\<^sub>T(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> Simpl\<^sub>F\<^sub>L\<^sub>T(P(i)))"
  using assms by (rel_auto)

lemma skip_cpf_def:
  "II = (\<lceil>II\<rceil>\<^sub>F\<^sub>L\<^sub>T \<and> $fault =\<^sub>u $fault\<acute> \<and> $ok =\<^sub>u $ok\<acute>)" 
  by rel_auto

lemma skip_lift_flt_def:
  "\<lceil>II\<rceil>\<^sub>F\<^sub>L\<^sub>T = ($\<Sigma>\<^sub>F\<^sub>L\<^sub>T\<acute> =\<^sub>u $\<Sigma>\<^sub>F\<^sub>L\<^sub>T)"
  by rel_auto

lemma seqr_fault_true [usubst]: 
  "(P ;; Q) \<^sub>f\<^sub>t = (P \<^sub>f\<^sub>t ;; Q)"
  by (rel_auto)

lemma seqr_fault_false [usubst]: 
  "(P ;; Q) \<^sub>f\<^sub>f = (P \<^sub>f\<^sub>f ;; Q)"
  by (rel_auto)

lemma rel_usubst_lift_cpf_uexpr_lift_cpf[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T \<dagger> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T = \<lceil>\<sigma> \<dagger> P\<rceil>\<^sub>F\<^sub>L\<^sub>T" 
  by rel_auto

lemma usubst_lift_cpf_assigns_lift_cpf [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>F\<^sub>L\<^sub>T \<dagger> \<lceil>\<langle>\<rho>\<rangle>\<^sub>a\<rceil>\<^sub>F\<^sub>L\<^sub>T = \<lceil>\<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>F\<^sub>L\<^sub>T" 
  by (simp add: usubst)

lemma usubst_lift_cpf_pre_uexpr_lift_cpf[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>F\<^sub>L\<^sub>T \<dagger> \<lceil>b\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub>< = \<lceil>\<sigma> \<dagger> b\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub><" 
  by (simp add: usubst)

lemma rel_usubst_lift_cpf_design[usubst]: 
  "(\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T \<dagger> (Q \<turnstile> P)) = (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T \<dagger> Q) \<turnstile> (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T \<dagger> P)"
  by (simp add: usubst unrest)

lemma usubst_cpf_true[usubst]: 
  "\<sigma> \<dagger> \<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T = \<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T" 
  by rel_auto

lemma usubst_cpf_false[usubst]: 
  "\<sigma> \<dagger> \<lceil>false\<rceil>\<^sub>F\<^sub>L\<^sub>T = \<lceil>false\<rceil>\<^sub>F\<^sub>L\<^sub>T" 
  by rel_auto

lemma rel_usubst_cpf_skip_cpf[usubst]: 
  "(\<sigma> \<dagger> II) = ((\<sigma> \<dagger> \<lceil>II\<rceil>\<^sub>F\<^sub>L\<^sub>T) \<and> \<sigma> \<dagger> $fault =\<^sub>u \<sigma> \<dagger> $fault\<acute> \<and> \<sigma> \<dagger> $ok =\<^sub>u \<sigma> \<dagger> $ok\<acute>)" 
  by (simp add: usubst unrest skip_cpf_def)

lemma usubst_lift_cpf_skip_lift_cpf[usubst]: 
  "(\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>F\<^sub>L\<^sub>T \<dagger> \<lceil>II\<rceil>\<^sub>F\<^sub>L\<^sub>T) = \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>F\<^sub>L\<^sub>T" 
  unfolding skip_r_def
  by (simp add: usubst_lift_cpf_assigns_lift_cpf)

lemma usubst_cpf_skip_cpf [usubst]:
  assumes "$ok \<sharp> \<sigma>" "$ok\<acute> \<sharp> \<sigma> "
  shows 
  "(\<sigma> \<dagger> SKIP\<^sub>F\<^sub>L\<^sub>T) = (\<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> (\<sigma> \<dagger> (\<not>$fault\<acute> \<and> \<lceil>II\<rceil>\<^sub>F\<^sub>L\<^sub>T)) \<triangleleft> \<sigma> \<dagger> (\<not>$fault) \<triangleright> (\<sigma> \<dagger> (II)))"
  using assms unfolding skip_flt_def
  by (simp add: usubst)  

lemma usubst_cpf_assigns_cpf [usubst]:
  assumes "$ok \<sharp> \<sigma>" "$ok\<acute> \<sharp> \<sigma> "
  shows 
  "\<sigma> \<dagger> \<langle>\<rho>\<rangle>\<^sub>F\<^sub>L\<^sub>T = (\<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> (\<sigma> \<dagger> ((\<not>$fault\<acute>) \<and> \<lceil>\<langle>\<rho>\<rangle>\<^sub>a\<rceil>\<^sub>F\<^sub>L\<^sub>T)) \<triangleleft> \<sigma> \<dagger> (\<not>$fault) \<triangleright>  (\<sigma> \<dagger> (II)))"  
  using assms unfolding assigns_flt_def
  by (simp add: usubst)

lemma c3_flt_comp_left_distr:
  "(C3_flt (P) ;; R) = ((P;;R) \<triangleleft> \<not>$fault \<triangleright> (II ;; R))"
  apply pred_simp
  apply rel_simp
  apply fastforce
done

lemma c3_flt_comp_semir:
  "(C3_flt(P) ;; C3_flt(R)) = C3_flt (P ;; C3_flt(R))"
  by rel_auto

lemma c3_flt_comp_simpl[uflt_comp]:
  "(C3_flt(P) ;; C3_flt(R)) = ((P ;; C3_flt(R)) \<triangleleft> \<not>$fault \<triangleright> (II))"
  by rel_auto

lemma simpl_flt_comp_semir:
  "(Simpl\<^sub>F\<^sub>L\<^sub>T(P) ;; Simpl\<^sub>F\<^sub>L\<^sub>T(R)) = Simpl\<^sub>F\<^sub>L\<^sub>T ((\<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> P) ;; Simpl\<^sub>F\<^sub>L\<^sub>T(R))"
  by rel_auto

theorem design_top_flt_left_zero[uflt_comp]: 
  "(\<top>\<^sub>F\<^sub>L\<^sub>T ;; (P \<turnstile> Q)) = \<top>\<^sub>F\<^sub>L\<^sub>T"
  by (rel_auto)

theorem Simpl_flt_top_flt_left_zero[uflt_comp]: 
  "(\<top>\<^sub>F\<^sub>L\<^sub>T ;; Simpl\<^sub>F\<^sub>L\<^sub>T (P)) = \<top>\<^sub>F\<^sub>L\<^sub>T"
  by (rel_auto)

lemma assigns_lift_cpf_comp_rel_cpf[uflt_comp]:
  assumes "$ok \<sharp> P" "$fault \<sharp> P"
  shows  "(\<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>F\<^sub>L\<^sub>T ;; P) = (\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>F\<^sub>L\<^sub>T \<dagger> P)"
  apply (insert assms)
  apply pred_simp 
  apply rel_blast 
done

lemma lift_des_skip_dr_unit_flt [uflt_comp]:
  "(\<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T ;; \<lceil>II\<rceil>\<^sub>F\<^sub>L\<^sub>T) = \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T"
  "(\<lceil>II\<rceil>\<^sub>F\<^sub>L\<^sub>T ;; \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T) = \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T"
  by (rel_auto)+

lemma skip_cpf_left_comp_simpl[uflt_comp]:
  "(SKIP\<^sub>F\<^sub>L\<^sub>T ;; Simpl\<^sub>F\<^sub>L\<^sub>T(R)) = (Simpl\<^sub>F\<^sub>L\<^sub>T(R))"
  by rel_auto

lemma skip_cpf_right_comp_simpl[uflt_comp]:
  "(Simpl\<^sub>F\<^sub>L\<^sub>T(R) ;; SKIP\<^sub>F\<^sub>L\<^sub>T) = (Simpl\<^sub>F\<^sub>L\<^sub>T(R))"
  by rel_auto

lemma assign_flt_alt_def: 
  "\<langle>\<sigma>\<rangle>\<^sub>F\<^sub>L\<^sub>T = Simpl\<^sub>F\<^sub>L\<^sub>T (\<not>$fault\<acute> \<and> \<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> II\<rceil>\<^sub>F\<^sub>L\<^sub>T)"
  by rel_auto

lemma assign_flt_left_comp_c3[uflt_comp]:
  "\<langle>a\<rangle>\<^sub>F\<^sub>L\<^sub>T ;; C3_flt (P \<turnstile> Q) = C3_flt (\<lceil>a\<rceil>\<^sub>s\<^sub>F\<^sub>L\<^sub>T \<dagger> (P \<turnstile>  Q))"
  by rel_auto

lemma assigns_flt_comp[uflt_comp]: 
  "(\<langle>f\<rangle>\<^sub>F\<^sub>L\<^sub>T ;; \<langle>g\<rangle>\<^sub>F\<^sub>L\<^sub>T) = \<langle>g \<circ> f\<rangle>\<^sub>F\<^sub>L\<^sub>T"
  by rel_auto

lemma usubst_cpf_des_cond_flt [usubst]:
  "\<lbrakk>$ok \<sharp> \<sigma>; $ok\<acute> \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> 
    \<sigma> \<dagger> (R \<turnstile> bif b then P else Q eif) = 
    (\<sigma> \<dagger> R \<turnstile>  (\<sigma> \<dagger> P \<triangleleft> \<sigma> \<dagger> \<lceil>b\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub>< \<triangleright> \<sigma> \<dagger> Q))"
  by (simp add: usubst)

lemma comp_cond_flt_left_distr[uflt_comp]:
  "((bif b then Simpl\<^sub>F\<^sub>L\<^sub>T P else Simpl\<^sub>F\<^sub>L\<^sub>T Q eif) ;; Simpl\<^sub>F\<^sub>L\<^sub>T R) = 
    (bif b then (Simpl\<^sub>F\<^sub>L\<^sub>T P ;; Simpl\<^sub>F\<^sub>L\<^sub>T R) else (Simpl\<^sub>F\<^sub>L\<^sub>T Q ;; Simpl\<^sub>F\<^sub>L\<^sub>T R) eif)"
  apply pred_simp 
  apply rel_simp
done

lemma if_mono:
  "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (bif b then P\<^sub>1 else Q\<^sub>1 eif) \<sqsubseteq> (bif b then P\<^sub>2 else Q\<^sub>2 eif)"
  by rel_auto

lemma design_post_seqr_rcond_left_not_ivar[urel_cond]:
  "S \<turnstile> (\<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> (\<lceil>R\<rceil>\<^sub>F\<^sub>L\<^sub>T \<and> $x\<acute>) ;; P \<triangleleft> \<not> $x \<triangleright> Q) = 
   S \<turnstile> (\<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> (\<lceil>R\<rceil>\<^sub>F\<^sub>L\<^sub>T \<and> $x\<acute>);; Q)"
  apply pred_simp
  apply fastforce 
done

lemma  design_post_seqr_rcond_left_ivar [urel_cond]:
  "S \<turnstile> (\<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> (\<lceil>R\<rceil>\<^sub>F\<^sub>L\<^sub>T \<and>  $x\<acute>) ;; P \<triangleleft> $x \<triangleright> Q) = 
   S \<turnstile> (\<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> (\<lceil>R\<rceil>\<^sub>F\<^sub>L\<^sub>T \<and>  $x\<acute>);; P)"
  apply pred_simp
  apply fastforce 
done

subsection {*While abrupt usubst*}

subsection {*block abrupt usubst*}

subsection {*Catch abrupt usubst*}

end