
section "Auxiliary algebraic laws for abrupt designs"
theory algebraic_laws_abrupt_aux
imports "../theories/utp_abrupt_designs"

begin

subsection {*Unrestriction behavior*}

lemma unrest_pre_out\<alpha>_abr [unrest]: "out\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><"
  by (transfer, auto simp add: out\<alpha>_def lens_prod_def)
 
lemma unrest_post_in\<alpha>_abr [unrest]: "in\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>>"
  by (transfer, auto simp add: in\<alpha>_def lens_prod_def)

lemma unrest_ok_abrupt_lift_rel_uexpr_cpa [unrest]:
  "$ok \<sharp> \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R" "$ok\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  "$abrupt \<sharp> \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R" "$abrupt\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  by (pred_auto)+

lemma unrest_ok_abrupt_lift_usubst_cpa [unrest]:
  "$ok\<acute> \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R" "$ok \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R"
  "$abrupt\<acute> \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R" "$abrupt \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R"               
  by rel_auto+

lemma unrest_ok_abrupt_lift_rel_usubst_cpa [unrest]:
  "$ok\<acute> \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R" "$ok \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R"
  "$abrupt\<acute> \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R" "$abrupt \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R"               
  by rel_auto+

lemma unrest_pre_in_var_abr [unrest]:
  "$abrupt \<sharp> \<lceil>p1\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><" " $ok \<sharp> \<lceil>p1\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><"
  "$abrupt \<sharp> \<lceil>p1\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>>" " $ok \<sharp> \<lceil>p1\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>>"
  by (transfer, simp)+
 
lemma unrest_in_out_rel_ok_abrupt_res_abr [unrest]:
  "$ok \<sharp> (P \<restriction>\<^sub>\<alpha> ok)" "$ok\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> ok)"  
  "$abrupt \<sharp> (P \<restriction>\<^sub>\<alpha> abrupt)" "$abrupt\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> abrupt)"
  by (simp_all add: rel_var_res_def unrest)

subsection {*Substitution behavior*}

lemma seqr_abrupt_true [usubst]: "(P ;; Q) \<^sub>a\<^sub>t = (P \<^sub>a\<^sub>t ;; Q)"
  by (rel_auto)

lemma seqr_abrupt_false [usubst]: "(P ;; Q) \<^sub>a\<^sub>f = (P \<^sub>a\<^sub>f ;; Q)"
  by (rel_auto)

lemma bool_seqr_laws_ok [usubst]:
    "\<And> P Q \<sigma>. \<sigma>($ok \<mapsto>\<^sub>s true) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>true/$ok\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($ok \<mapsto>\<^sub>s false) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>false/$ok\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($ok\<acute> \<mapsto>\<^sub>s true) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>true/$ok\<acute>\<rbrakk>)"
    "\<And> P Q \<sigma>. \<sigma>($ok\<acute> \<mapsto>\<^sub>s false) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>false/$ok\<acute>\<rbrakk>)"
    by (simp_all add: bool_seqr_laws)

lemma bool_seqr_laws_abrupt [usubst]:
    "\<And> P Q \<sigma>. \<sigma>($abrupt \<mapsto>\<^sub>s true) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>true/$abrupt\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($abrupt \<mapsto>\<^sub>s false) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>false/$abrupt\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($abrupt\<acute> \<mapsto>\<^sub>s true) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>true/$abrupt\<acute>\<rbrakk>)"
    "\<And> P Q \<sigma>. \<sigma>($abrupt\<acute> \<mapsto>\<^sub>s false) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>false/$abrupt\<acute>\<rbrakk>)"
    by (simp_all add: bool_seqr_laws)

lemma cpa_ord [usubst]:
  "$ok \<prec>\<^sub>v $ok\<acute>" "$abrupt \<prec>\<^sub>v $abrupt\<acute>" 
  "$ok \<prec>\<^sub>v $abrupt\<acute>" "$ok \<prec>\<^sub>v $abrupt" "$ok\<acute> \<prec>\<^sub>v $abrupt\<acute>" "$ok\<acute> \<prec>\<^sub>v $abrupt" 
  by (simp_all add: var_name_ord_def)

lemma usubst_C3_abr [usubst]: 
  "\<sigma> \<dagger> C3_abr(P) = (\<sigma> \<dagger> P \<triangleleft> \<sigma> \<dagger> (\<not>$abrupt) \<triangleright> \<sigma> \<dagger> II) "
  unfolding C3_abr_def usubst_condr .. 

lemma usubst_Simpl_abr [usubst]: 
  "\<sigma> \<dagger> Simpl\<^sub>A\<^sub>B\<^sub>R (P) = (\<sigma> \<dagger> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> P) \<triangleleft> \<sigma> \<dagger> (\<not>$abrupt) \<triangleright> \<sigma> \<dagger> II)"
  unfolding C3_abr_def usubst_condr ..

lemma usubst_lift_pre_uexpr_cpa[simp]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< = \<lceil>\<sigma> \<dagger> b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><" 
  by rel_auto

lemma rel_usubst_lift_pre_uexpr_cpa[simp]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< = \<lceil>\<sigma> \<dagger> \<lceil>b\<rceil>\<^sub><\<rceil>\<^sub>A\<^sub>B\<^sub>R" 
  by rel_auto

lemma rel_usubst_lift_post_uexpr_cpa[simp]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>> = \<lceil>\<sigma> \<dagger> \<lceil>b\<rceil>\<^sub>>\<rceil>\<^sub>A\<^sub>B\<^sub>R" 
  by rel_auto

lemma usubst_cond_abr[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> (bif b then P else Q eif) = 
   ((\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> P \<triangleleft> \<lceil>\<sigma> \<dagger> b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<triangleright> \<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> Q)) \<triangleleft> \<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> (\<not> $abrupt) \<triangleright> \<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> II)"
   unfolding C3_abr_def
  by (simp add: usubst unrest)

lemma usubst_cpa_des_cond_abr [usubst]:
  "\<lbrakk>$ok \<sharp> \<sigma>; $ok\<acute> \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> 
    \<sigma> \<dagger> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> bif b then P else Q eif) = 
    (\<sigma> \<dagger> \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile>  ((\<sigma> \<dagger> \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<sigma> \<dagger> P \<triangleleft> \<sigma> \<dagger> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<triangleright> \<sigma> \<dagger> Q)) \<triangleleft> \<sigma> \<dagger> (\<not> $abrupt) \<triangleright> \<sigma> \<dagger> II))"
  by (simp add: usubst)

lemma usubst_rel_des_cond_abr [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> bif b then P else Q eif) = 
   (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile>  ((\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> P \<triangleleft> \<lceil>\<sigma> \<dagger> \<lceil>b\<rceil>\<^sub><\<rceil>\<^sub>A\<^sub>B\<^sub>R \<triangleright> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> Q)) \<triangleleft> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> (\<not> $abrupt) \<triangleright> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> II))"
  by (simp add: usubst unrest)

lemma usubst_des_cond_abr [usubst]:   
  "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> bif b then P else Q eif) = 
   (\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile>  ((\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> P \<triangleleft> \<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<triangleright> \<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> Q)) \<triangleleft> \<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> (\<not> $abrupt) \<triangleright> \<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> II))"
  by (simp add: usubst unrest)

subsection {*Assign abrupt behavior*}

lemma assigns_usubst_cpa [usubst] :
  "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>\<langle>\<rho>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R = \<lceil>\<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R" 
  by rel_auto

lemma assigns_cpa_comp:
   "\<lbrakk>$ok \<sharp> P; $ok\<acute> \<sharp> P; $abrupt \<sharp> P; $abrupt\<acute> \<sharp> P\<rbrakk>\<Longrightarrow> 
   (\<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R ;; P) = (\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> P)"
   apply pred_auto apply transfer 
   apply (metis cp_abr.surjective des_vars.surjective des_vars_ext_def fst_conv in\<alpha>_def lens.select_convs(1) lens.select_convs(2) old.prod.case snd_conv)
   apply transfer
   apply (smt cp_abr.simps(2) cp_abr_ext_def des_vars.select_convs(2) des_vars_ext_def fst_conv in\<alpha>_def lens.select_convs(1) lens.select_convs(2) mem_Collect_eq old.prod.case relcomp.simps snd_conv) 
done
 
lemma assigns_cpa_rel_lift_comp: 
  "(\<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R ;; \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R) = (\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto 

thm assigns_subst

lemma "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> \<langle>\<rho>\<rangle>\<^sub>A\<^sub>B\<^sub>R = \<langle>\<rho> \<circ> \<lfloor>\<sigma>\<rfloor>\<^sub>s\<rangle>\<^sub>A\<^sub>B\<^sub>R" 
  apply transfer apply rel_auto oops
term "\<lceil>\<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R"


lemma assigns_abr_subst [usubst]:
  " \<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> \<langle>\<rho>\<rangle>\<^sub>A\<^sub>B\<^sub>R = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R"
  apply transfer  apply (rel_auto) oops

lemma assigns_abr_comp: "(\<langle>f\<rangle>\<^sub>A\<^sub>B\<^sub>R ;; \<langle>g\<rangle>\<^sub>A\<^sub>B\<^sub>R) = \<langle>g \<circ> f\<rangle>\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto 
thm design_composition

lemma assign_d_left_comp:
assumes
    "$ok\<acute> \<sharp> (P \<turnstile> Q)" "$ok \<sharp> (P \<turnstile> Q)" 
  shows
  "(\<langle>f\<rangle>\<^sub>A\<^sub>B\<^sub>R ;; (P \<turnstile> Q)) = (\<lceil>\<lceil>f\<rceil>\<^sub>s\<rceil>\<^sub>A\<^sub>B \<dagger> P \<turnstile> \<lceil>\<lceil>f\<rceil>\<^sub>s\<rceil>\<^sub>A\<^sub>B \<dagger> Q)"
  apply (simp add: assigns_c_def    C3_abr_def)

lemma assign_d_right_comp:
  "((P \<turnstile>\<^sub>r Q) ;; \<langle>f\<rangle>\<^sub>D) = ((\<not> ((\<not> P) ;; true)) \<turnstile>\<^sub>r (Q ;; \<langle>f\<rangle>\<^sub>a))"
  by (simp add: assigns_d_def rdesign_composition)

lemma assigns_d_comp:
  "(\<langle>f\<rangle>\<^sub>D ;; \<langle>g\<rangle>\<^sub>D) = \<langle>g \<circ> f\<rangle>\<^sub>D"
  by (simp add: assigns_d_def rdesign_composition assigns_comp)

subsection {*Seq behavior*}

lemma lift_des_skip_dr_unit_abr [simp]:
  "(\<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R ;; \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R) = \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  "(\<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R ;; \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R) = \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  by (rel_auto)+


subsection {*Abrupt semantics behavior*}

lemma Simpl_abr_idem[simp]: "Simpl\<^sub>A\<^sub>B\<^sub>R(Simpl\<^sub>A\<^sub>B\<^sub>R(P)) = Simpl\<^sub>A\<^sub>B\<^sub>R(P)"
  by (rel_auto)

lemma Simpl_abr_Idempotent: "Idempotent Simpl\<^sub>A\<^sub>B\<^sub>R"
  by (simp add: Idempotent_def Simpl_abr_idem)

lemma Simpl_abr_mono: "P \<sqsubseteq> Q \<Longrightarrow> Simpl\<^sub>A\<^sub>B\<^sub>R(P) \<sqsubseteq> Simpl\<^sub>A\<^sub>B\<^sub>R(Q)"
  by (rel_auto)

lemma Simpl_abr_Monotonic: "Monotonic Simpl\<^sub>A\<^sub>B\<^sub>R"
  by (simp add: Monotonic_def Simpl_abr_mono)

lemma Simpl_abr_condr: "Simpl\<^sub>A\<^sub>B\<^sub>R(P \<triangleleft> b \<triangleright> Q) = (Simpl\<^sub>A\<^sub>B\<^sub>R(P) \<triangleleft> b \<triangleright> Simpl\<^sub>A\<^sub>B\<^sub>R(Q))"
  by (rel_auto)

lemma Simpl_abr_if_abr: 
  "Simpl\<^sub>A\<^sub>B\<^sub>R(bif b then P else Q eif) = 
   (bif b then Simpl\<^sub>A\<^sub>B\<^sub>R(P) else Simpl\<^sub>A\<^sub>B\<^sub>R(Q) eif)"
  by (rel_auto)

lemma Simpl_abr_skip_abr[simp]: "Simpl\<^sub>A\<^sub>B\<^sub>R(SKIP\<^sub>A\<^sub>B\<^sub>R) = (SKIP\<^sub>A\<^sub>B\<^sub>R)"
  by (rel_auto)
                    
lemma Simpl_abr_throw_abr[simp]: "Simpl\<^sub>A\<^sub>B\<^sub>R(THROW\<^sub>A\<^sub>B\<^sub>R) = (THROW\<^sub>A\<^sub>B\<^sub>R)"
  by (rel_auto)

lemma Simpl_abr_assign_abr[simp]: "Simpl\<^sub>A\<^sub>B\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R) = (\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R)"
  by (rel_auto)

lemma Simpl_abr_form: "
  Simpl\<^sub>A\<^sub>B\<^sub>R(P) = ((\<not> (\<not>$abrupt) \<and> II) \<or> ((\<not>$abrupt) \<and> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (P))))"
  by (rel_auto) 

lemma abrupt_Simpl_abr:
  "(\<not> (\<not>$abrupt ) \<and> Simpl\<^sub>A\<^sub>B\<^sub>R(P)) = 
   (II \<and> \<not> (\<not>$abrupt\<acute>))"
  by (rel_auto)

lemma nabrupt_Simpl_abr:
  "(\<not>$abrupt \<and> \<not>$fault \<and> Simpl\<^sub>A\<^sub>B\<^sub>R(P)) = 
   (\<not>$abrupt \<and>\<not>$fault \<and> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (P)))"
  by (rel_auto)

lemma Simpl_abr_semir_form:
  "(Simpl\<^sub>A\<^sub>B\<^sub>R(P) ;; Simpl\<^sub>A\<^sub>B\<^sub>R(Q)) = Simpl\<^sub>A\<^sub>B\<^sub>R((\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (P)) ;; Simpl\<^sub>A\<^sub>B\<^sub>R(Q))"
  by (rel_simp) blast 

lemma Simpl_abr_semir_closure:
  assumes "P is Simpl\<^sub>A\<^sub>B\<^sub>R" "Q is Simpl\<^sub>A\<^sub>B\<^sub>R"
  shows "(P ;; Q) is Simpl\<^sub>A\<^sub>B\<^sub>R"
  using assms
  by (metis  Healthy_def Simpl_abr_semir_form Simpl_abr_idem)

definition design_abr_sup :: "('\<alpha>,'\<beta>) rel_cpa set \<Rightarrow> ('\<alpha>,'\<beta>) rel_cpa" ("\<Sqinter>\<^sub>A\<^sub>B\<^sub>R_" [900] 900) where
"\<Sqinter>\<^sub>A\<^sub>B\<^sub>R A = (if (A = {}) then \<top>\<^sub>A\<^sub>B\<^sub>R else \<Sqinter> A)"

lemma Simpl_abr_Continuous: "Continuous Simpl\<^sub>A\<^sub>B\<^sub>R"
  unfolding Continuous_def SUP_def apply rel_simp
  unfolding  SUP_def  
  apply transfer apply auto 
done

lemma Simpl_abr_R3_conj: "Simpl\<^sub>A\<^sub>B\<^sub>R(P \<and> Q) = (Simpl\<^sub>A\<^sub>B\<^sub>R(P) \<and> Simpl\<^sub>A\<^sub>B\<^sub>R(Q))"
  by (rel_auto)

lemma Simpl_abr_disj: "Simpl\<^sub>A\<^sub>B\<^sub>R(P \<or> Q) = (Simpl\<^sub>A\<^sub>B\<^sub>R(P) \<or> Simpl\<^sub>A\<^sub>B\<^sub>R(Q))"
  by (rel_auto)

lemma Simpl_abr_USUP:
  assumes "A \<noteq> {}"
  shows "Simpl\<^sub>A\<^sub>B\<^sub>R(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> Simpl\<^sub>A\<^sub>B\<^sub>R(P(i)))"
  using assms by (rel_auto)


lemma design_abr_sup_non_empty [simp]:  
  "A \<noteq> {} \<Longrightarrow> \<Sqinter>\<^sub>A\<^sub>B\<^sub>R A = \<Sqinter> A"
  by (simp add: design_abr_sup_def)

subsection {*Abrupt top behavior*}

theorem design_top_abr_left_zero[simp]: 
  "(\<top>\<^sub>A\<^sub>B\<^sub>R ;; (P \<turnstile> Q)) = \<top>\<^sub>A\<^sub>B\<^sub>R"
  by (rel_auto)

theorem Simpl_abr_top_abr_left_zero[simp]: 
  "(\<top>\<^sub>A\<^sub>B\<^sub>R ;; Simpl\<^sub>A\<^sub>B\<^sub>R (P)) = \<top>\<^sub>A\<^sub>B\<^sub>R"
  by (rel_auto)

lemma design_top_abr:
  "(P \<turnstile> Q) \<sqsubseteq> \<top>\<^sub>A\<^sub>B\<^sub>R"
  by (rel_auto)

lemma Simpl_abr_top_abr:
  "Simpl\<^sub>A\<^sub>B\<^sub>R (P) \<sqsubseteq> \<top>\<^sub>A\<^sub>B\<^sub>R"
  by (rel_auto)

lemma design_abr_sup_empty [simp]: 
  "\<Sqinter>\<^sub>A\<^sub>B\<^sub>R {} = \<top>\<^sub>A\<^sub>B\<^sub>R"
  by (simp add: design_abr_sup_def)

subsection {*Abrupt Bot behavior*}

abbreviation design_inf :: "('\<alpha>, '\<beta>) rel_des set \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" ("\<Squnion>\<^sub>A\<^sub>B\<^sub>R_" [900] 900) where
"\<Squnion>\<^sub>A\<^sub>B\<^sub>R A \<equiv> \<Squnion> A"

lemma design_bottom_abr:
  "\<bottom>\<^sub>A\<^sub>B\<^sub>R \<sqsubseteq> (P \<turnstile> Q)"
  by simp

lemma Simpl_abr_bottom_abr:
  "\<bottom>\<^sub>A\<^sub>B\<^sub>R \<sqsubseteq> Simpl\<^sub>A\<^sub>B\<^sub>R (P)"
  by simp

lemma Simpl_abr_UINF:
  assumes "A \<noteq> {}"
  shows "Simpl\<^sub>A\<^sub>B\<^sub>R(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> Simpl\<^sub>A\<^sub>B\<^sub>R(P(i)))"
  using assms by (rel_auto)

subsection {*Abrupt If behavior*}

lemma if_mono:
  "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (bif b then P\<^sub>1 else Q\<^sub>1 eif) \<sqsubseteq> (bif b then P\<^sub>2 else Q\<^sub>2 eif)"
  by rel_auto

end