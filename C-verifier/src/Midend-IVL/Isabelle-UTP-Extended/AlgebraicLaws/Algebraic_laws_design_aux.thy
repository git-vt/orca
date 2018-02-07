section \<open>Algebraic laws of programming\<close>

text \<open>In this section we introduce the semantic rules related to the different
      statements of IMP. In the literature this also known as the algebraic laws of programming.
      In our framework we will use these rules in order to optimize a given program written in our
      language, and this before any deductive proof verification activity or formal testing.\<close>

theory Algebraic_laws_design_aux
  imports "../theories/Design/utp_designs_more"
begin
  
section \<open>Algebraic laws AUX\<close>
                             
lemma fun_idempotentI:
 "(\<And> x. x \<in> carrier L \<Longrightarrow>  f (f x) .=\<^bsub>L\<^esub> f x) \<Longrightarrow> idempotent L f"
 unfolding idempotent_def
  by simp

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
  
lemma psubst_lift_pre_des[usubst]:
  "\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rceil>\<^sub>s \<dagger> \<lceil>b\<rceil>\<^sub>D\<^sub>< = \<lceil>\<sigma> \<dagger> b\<rceil>\<^sub>D\<^sub><"    
  by rel_simp
    
lemma usubst_des_rel_lift_assign_d[usubst]: 
  "\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rceil>\<^sub>s \<dagger> \<langle>\<rho>\<rangle>\<^sub>D = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>D"
  by rel_simp

lemma seq_psubst_des[usubst]:
  "P is H1 \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>D ;; P = \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rceil>\<^sub>s \<dagger> P"
  by rel_blast

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
subsection "AUX lemmas for UTP order"
    
lemma Mono_utp_orderI:
  fixes f :: "'a hrel \<Rightarrow> 'a hrel" 
  shows "(\<And>x y. x is H \<Longrightarrow> y is H \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> F x \<sqsubseteq> F y) \<Longrightarrow> Mono\<^bsub>utp_order H\<^esub> F"
  unfolding isotone_def using utp_weak_partial_order 
  by simp    

lemma Mono_utp_orderD: (*This should be generated automatically in utp_theory*)
  assumes "Mono\<^bsub>utp_order H\<^esub> F"
    and    "x is H"
    and    "y is H"
    and    "y \<sqsubseteq> x"    
  shows   "(F y) \<sqsubseteq> (F x)"
  using assms utp_weak_partial_order unfolding isotone_def
  by simp
       
subsection "AUX lemmas for healthiness conditions"
  
lemma rdesign_is_healthy_DES[simp]: (*This should be generated automatically in utp_theory*)
  "Pre \<turnstile>\<^sub>r Post is \<H>\<^bsub>DES\<^esub>"
  unfolding des_hcond_def using rdesign_is_H1_H2
  by assumption
    
lemma ndesign_is_healthy_NDES[simp]: (*This should be generated automatically in utp_theory*)
  "Pre \<turnstile>\<^sub>n Post is \<H>\<^bsub>NDES\<^esub>"
   unfolding ndes_hcond_def using ndesign_H1_H3
  by assumption

lemma Hcarrier_hdesigns:(*This should be generated automatically in utp_theory*)
  "\<H>\<^bsub>DES\<^esub> P = \<^bold>H P"
  by (simp add: des_hcond_def)

lemma is_Hcarrier_is_hdesigns:(*This should be generated automatically in utp_theory*)
  "(P is \<H>\<^bsub>DES\<^esub>) = (P is \<^bold>H)" 
  by (simp add: des_hcond_def)
    
lemma Ncarrier_ndesigns:(*This should be generated automatically in utp_theory*)
  "\<H>\<^bsub>NDES\<^esub> P = \<^bold>N P"
  by (simp add: ndes_hcond_def)

lemma is_Ncarrier_is_ndesigns:(*This should be generated automatically in utp_theory*)
  "(P is \<H>\<^bsub>NDES\<^esub>) = (P is \<^bold>N)" 
  by (simp add: ndes_hcond_def)
    
 lemma H1_distrib_left_J:
  "H1 (P ;; J) = (H1 P ;;  J)"
   by rel_auto 
    
lemma seq_is_H1:
  assumes "P is H1"    
  assumes "Q is H1"
  shows "(P;;Q) is H1"
  using assms
  by rel_blast
    
lemma utp_theory_des_top_is_not_ok:
  "\<^bold>\<top>\<^bsub>DES\<^esub>  = \<top>\<^sub>D"
  by (metis (no_types, lifting) H1_below_top H1_idem H2_not_okay Hcarrier_hdesigns Healthy_def des_top_is_H1_H3 design_lat_top design_theory_continuous.meet_top semilattice_sup_class.le_iff_sup)

lemma utp_theory_des_bot_is_true:
  "\<^bold>\<bottom>\<^bsub>DES\<^esub>  = \<bottom>\<^sub>D"
  by (metis H1_monotone H2_true des_bot_H1_H3 design_lat_bottom ndesign_lat_bottom normal_design_theory_continuous.bottom_lower ordering_top.extremum_unique utp_pred_laws.top.ordering_top_axioms utp_pred_laws.top_greatest)

lemma utp_theory_ndes_top_is_not_ok:
  "\<^bold>\<top>\<^bsub>NDES\<^esub>  = \<top>\<^sub>D"
  by (metis H1_H3_commute H3_H2_absorb H3_ndesign des_top_ndes_def design_lat_top ndesign_lat_top utp_theory_des_top_is_not_ok)
 
lemma utp_theory_ndes_bot_is_true:
  "\<^bold>\<bottom>\<^bsub>NDES\<^esub>  = \<bottom>\<^sub>D"
  by (metis des_bot_H1_H3 normal_design_theory_continuous.bottom_lower ordering_top.extremum_unique utp_pred_laws.top.ordering_top_axioms )
    
find_theorems " _ ;; \<bottom>\<^sub>D"

find_theorems " _ ;; \<top>\<^sub>D"

lemma mieracle_situation_left_zero:
  "P is \<^bold>N \<Longrightarrow> Q is \<^bold>N \<Longrightarrow>(\<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<turnstile>\<^sub>n false) ;; Q = (\<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<turnstile>\<^sub>n false)"  
  by rel_blast
    
lemma H1_H2_impl_H1: "P is \<^bold>H \<Longrightarrow> P is H1"  
  by pred_blast


lemma H1_distrib_left_design:
  "H1 (P ;; (Q\<^sub>1 \<turnstile> Q\<^sub>2)) = (H1 P ;; (Q\<^sub>1 \<turnstile> Q\<^sub>2))"
  by rel_auto 
    
lemma J_left_unit_H1_design_intro:
  "$ok\<acute> \<sharp> P \<Longrightarrow> ((P \<turnstile> Q) ;; J) = (P \<turnstile> Q)"
proof (rel_simp, goal_cases)
  case (1 ok\<^sub>v more ok\<^sub>v' morea)
  then show ?case by fastforce
qed  

lemma H1_distrib_left_rdesign:
  "H1 (P ;; (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2)) = (H1 P ;; (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2))"
  by rel_auto 

lemma H1_distrib_left_ndesign:
  "H1 (P ;; (q \<turnstile>\<^sub>n Q)) = (H1 P ;; (q \<turnstile>\<^sub>n Q))"
  by rel_auto    

lemma design_is_healthy_DES_intro:
  "$ok\<acute> \<sharp> P \<Longrightarrow> P \<turnstile> Q is \<H>\<^bsub>DES\<^esub>" 
proof -
  assume 1:"$ok\<acute> \<sharp> P" 
  have H_DES_is_H1_H2: "((P \<turnstile> Q is \<H>\<^bsub>DES\<^esub>) = (P \<turnstile> Q is \<^bold>H))"
    unfolding Healthy_def 
    by (simp add: des_hcond_def)
  then show ?thesis unfolding H2_def Healthy_def
    by (simp add: H1_distrib_left_J H1_design J_left_unit_H1_design_intro[OF 1])
qed   


lemma rdesign_split: 
  "\<not>(P is \<^bold>H) \<or> (pre\<^sub>D P::'a hrel) \<turnstile>\<^sub>r post\<^sub>D P = P"
  by (simp add: H1_H2_eq_rdesign Healthy_def)

lemma ndesign_split: " \<not> (P is \<^bold>N) \<or> \<lfloor>pre\<^sub>D P::'a hrel\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D P = P"
  using ndesign_form by blast 
 
lemma H3_impl_H2:"P is H3 \<Longrightarrow> P is H2"
  by (metis H2_H3_commute H3_H2_absorb Healthy_def' Healthy_if)

lemma rdesign_form: "P is \<^bold>H \<Longrightarrow> (pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P)) = P"
  by (metis H1_H2_eq_rdesign Healthy_if)
 
lemma H1_H2_intro:
  assumes "P is H1" "P is H2"
  shows "P is \<^bold>H"
  using assms
  by rel_simp 
  
lemma design_is_H1:
  "(P \<turnstile> Q) is H1"  
  by pred_auto 

lemma H3_design:
  assumes  "$ok\<acute> \<sharp> Q"
  shows "H3(\<lceil>P\<rceil>\<^sub>< \<turnstile> Q) = \<lceil>P\<rceil>\<^sub>< \<turnstile> Q"
  using assms
  by rel_blast
    
lemma design_is_H1_H3 [closure]:
  "$ok\<acute> \<sharp> Q \<Longrightarrow> (\<lceil>P\<rceil>\<^sub>< \<turnstile> Q) is \<^bold>N"
  by (simp add: H1_design H3_design Healthy_def')
    
subsection {*AUX lemmas for Refinement*}

lemma cond_refine_des: 
  assumes "((b \<and> p) \<turnstile> q) \<sqsubseteq> C\<^sub>1" and "((\<not>b \<and> p) \<turnstile> q)\<sqsubseteq> C\<^sub>2" 
  shows "(p \<turnstile> q) \<sqsubseteq> (C\<^sub>1 \<triangleleft> b \<triangleright> C\<^sub>2)"
  using assms by rel_blast
    
lemma refine_reverse_impl:
  "`Q \<Rightarrow> P` \<Longrightarrow>  P \<sqsubseteq> Q" 
  by rel_auto
    
lemma seq_refine_unrest_des:
  assumes "out\<alpha> \<sharp> p" "in\<alpha> \<sharp> q"
  assumes "(p \<turnstile> \<lceil>s\<rceil>\<^sub>D\<^sub>>) \<sqsubseteq> P" and "(\<lceil>s\<rceil>\<^sub>D\<^sub>< \<turnstile> q) \<sqsubseteq> Q"
  shows "(p \<turnstile> q) \<sqsubseteq> (P ;; Q)"
 using assms    
proof ( pred_simp, goal_cases)
  case (1 ok\<^sub>v more ok\<^sub>v' morea y)
  then show ?case 
    by (rel_simp) 
       (metis (no_types, lifting) "1"(16) "1"(18) "1"(3) des_vars.surjective)  
qed
    
lemma seq_refine_unrest_rdesign:
  assumes "out\<alpha> \<sharp> p" "in\<alpha> \<sharp> q"
  assumes "(p \<turnstile>\<^sub>r \<lceil>s\<rceil>\<^sub>>) \<sqsubseteq> P" "(\<lceil>s\<rceil>\<^sub>< \<turnstile>\<^sub>r q) \<sqsubseteq> Q"
  shows "(p \<turnstile>\<^sub>r q) \<sqsubseteq> (P ;; Q)"
  unfolding ndesign_def rdesign_def
proof (rule seq_refine_unrest_des[of _ _ _ s], goal_cases)
  case 1
  then show ?case using assms(1) by pred_simp
next
  case 2
  then show ?case using assms(2) by pred_simp
next
  case 3
  then show ?case using assms(3) unfolding ndesign_def rdesign_def by assumption
next
  case 4
  then show ?case using assms(4) unfolding ndesign_def rdesign_def by assumption
qed

lemma seq_refine_unrest_ndesign:
  fixes q:: "'a hrel"
  assumes "in\<alpha> \<sharp> q"
  assumes "(p \<turnstile>\<^sub>n \<lceil>s\<rceil>\<^sub>>) \<sqsubseteq> P" and "(s \<turnstile>\<^sub>n q) \<sqsubseteq> Q"
  shows "(p \<turnstile>\<^sub>n q) \<sqsubseteq> (P ;; Q)"
  unfolding ndesign_def 
proof (rule seq_refine_unrest_rdesign[of "\<lceil>p\<rceil>\<^sub><" "q" _ s], goal_cases)
  case 1
  then show ?case by pred_simp
next
  case 2
  then show ?case using assms(1) by assumption 
next
  case 3
  then show ?case using assms(2) unfolding ndesign_def by assumption 
next
  case 4
  then show ?case using assms(3) unfolding ndesign_def by assumption 
qed  

end


