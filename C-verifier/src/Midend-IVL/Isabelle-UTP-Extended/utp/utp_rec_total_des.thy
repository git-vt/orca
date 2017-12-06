theory utp_rec_total_des
  imports "../hoare/AlgebraicLaws/Design/Algebraic_laws_design"
begin
  
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
    
lemma mu_design_is_healthy_des[simp]: (*This should be generated automatically in utp_theory*)
  "\<mu>\<^sub>D B is \<H>\<^bsub>DES\<^esub>"
  by (simp add: is_Hcarrier_is_hdesigns)

lemma mu_normal_design_is_healthy_des[simp]: (*This should be generated automatically in utp_theory*)
  "\<mu>\<^sub>N B is \<H>\<^bsub>NDES\<^esub>"
  by (simp add: is_Ncarrier_is_ndesigns)
    
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

lemma rdesign_is_healthy_DES[simp]: (*This should be generated automatically in utp_theory*)
  "Pre \<turnstile>\<^sub>r Post is \<H>\<^bsub>DES\<^esub>"
  unfolding des_hcond_def using rdesign_is_H1_H2
  by assumption
    
lemma ndesign_is_healthy_NDES[simp]: (*This should be generated automatically in utp_theory*)
  "Pre \<turnstile>\<^sub>n Post is \<H>\<^bsub>NDES\<^esub>"
   unfolding ndes_hcond_def using ndesign_H1_H3
  by assumption
    
lemma Mono_utp_orderD: (*This should be generated automatically in utp_theory*)
  assumes "Mono\<^bsub>utp_order H\<^esub> B"
  and     "x is H"
  and     "y is H"
  and     "y \<sqsubseteq> x"    
  shows   "(B y) \<sqsubseteq> (B x)"
  using assms
  by (auto simp add: isotone_def utp_weak_partial_order)

lemma  design_mu_wf_refine_intro: 
  assumes   WF: "wf R"
    and      M: "Mono\<^bsub>uthy_order DES\<^esub> B"
    and      H: "B \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    and      Okey1:"$ok\<acute> \<sharp> Pre" and Okey2:"$ok\<acute> \<sharp> Post"
    and  induct_step:
    "\<And>st. ((Pre \<and>\<lceil>E\<rceil>\<^sub>D\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> Post) \<sqsubseteq> (B ((Pre \<and> (\<lceil>E\<rceil>\<^sub>D\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile> Post))"
  shows "(Pre \<turnstile> Post) \<sqsubseteq> \<mu>\<^sub>D B"            
proof -   
  {
    fix st
    have "(Pre \<and> \<lceil>E\<rceil>\<^sub>D\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> Post \<sqsubseteq> \<mu>\<^sub>D B" 
      using WF proof (induction rule: wf_induct_rule)
      case (less st)
      hence 0: "(Pre \<and> (\<lceil>E\<rceil>\<^sub>D\<^sub><, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile> Post \<sqsubseteq> \<mu>\<^sub>D B"
        by rel_blast
      from M H design_theory_continuous.LFP_lemma3 mono_Monotone_utp_order
      have 1: "\<mu>\<^sub>D B \<sqsubseteq>  B (\<mu>\<^sub>D B)"
        by blast
      from 0 1 have 2:"(Pre \<and> (\<lceil>E\<rceil>\<^sub>D\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile> Post \<sqsubseteq> B (\<mu>\<^sub>D B)"
        by simp
      have 3: "B ((Pre \<and> (\<lceil>E\<rceil>\<^sub>D\<^sub><, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile> Post) \<sqsubseteq> B (\<mu>\<^sub>D B)"
      proof (rule Mono_utp_orderD[OF M "mu_design_is_healthy_des" "design_is_healthy_DES_intro" 0], goal_cases)
        case 1
        then show ?case by (simp add: Okey1 unrest)
      qed  
      have 4:"(Pre \<and> \<lceil>E\<rceil>\<^sub>D\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> Post \<sqsubseteq> \<dots>" 
        by (rule induct_step)
      show ?case
        using order_trans[OF 3 4] Okey1 H M design_theory_continuous.LFP_lemma2 dual_order.trans mono_Monotone_utp_order 
        by blast
    qed
  }
  thus ?thesis
    by pred_simp
qed    
  
lemma rdesign_mu_wf_refine_intro: 
  assumes   WF: "wf R"
    and      M: "Mono\<^bsub>uthy_order DES\<^esub> B"
    and      H: "B \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    and  induct_step:
    "\<And>st. ((Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r Post) \<sqsubseteq> (B ((Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r Post))"
  shows "(Pre \<turnstile>\<^sub>r Post) \<sqsubseteq> \<mu>\<^sub>D B"            
proof -          
  {
  fix st
  have "(Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r Post \<sqsubseteq> \<mu>\<^sub>D B" 
    using WF proof (induction rule: wf_induct_rule)
    case (less st)
    hence 0: "(Pre \<and> (\<lceil>E\<rceil>\<^sub><, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r Post \<sqsubseteq> \<mu>\<^sub>D B"
      by rel_blast
    from M H design_theory_continuous.LFP_lemma3 mono_Monotone_utp_order
    have 1: "\<mu>\<^sub>D B \<sqsubseteq>  B (\<mu>\<^sub>D B)"
      by blast
    from 0 1 have 2:"(Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r Post \<sqsubseteq> B (\<mu>\<^sub>D B)"
      by simp
    have 3: "B ((Pre \<and> (\<lceil>E\<rceil>\<^sub><, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r Post) \<sqsubseteq> B (\<mu>\<^sub>D B)"
      by (auto intro: Mono_utp_orderD M 0)
    have 4:"(Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r Post \<sqsubseteq> \<dots>" 
      by (rule induct_step)
    show ?case
      using order_trans[OF 3 4] H M design_theory_continuous.LFP_lemma2 dual_order.trans mono_Monotone_utp_order 
      by blast
  qed
  }
  thus ?thesis
    by pred_simp
qed    
  
lemma ndesign_mu_wf_refine_intro: 
  assumes   WF: "wf R"
    and      M: "Mono\<^bsub>uthy_order NDES\<^esub> B"
    and      H: "B \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
    and  induct_step:
    "\<And>e. ((Pre \<and> E =\<^sub>u \<guillemotleft>e\<guillemotright>) \<turnstile>\<^sub>n Post) \<sqsubseteq> (B ((Pre \<and> (E,\<guillemotleft>e\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Post))"
  shows "(Pre \<turnstile>\<^sub>n Post) \<sqsubseteq> \<mu>\<^sub>N B"            
proof -          
  {
  fix e
  have "(Pre \<and> E =\<^sub>u \<guillemotleft>e\<guillemotright>) \<turnstile>\<^sub>n Post \<sqsubseteq> \<mu>\<^sub>N B" 
    using WF proof (induction rule: wf_induct_rule)
    case (less e)
    hence 0: "(Pre \<and> (E, \<guillemotleft>e\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Post \<sqsubseteq> \<mu>\<^sub>N B"
      by rel_blast
    from M H normal_design_theory_continuous.LFP_lemma3 mono_Monotone_utp_order
    have 1: "\<mu>\<^sub>N B \<sqsubseteq>  B (\<mu>\<^sub>N B)"
      by blast
    from 0 1 have 2:"(Pre \<and> (E,\<guillemotleft>e\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Post \<sqsubseteq> B (\<mu>\<^sub>N B)"
      by simp
    have 3: "B ((Pre \<and> (E, \<guillemotleft>e\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Post) \<sqsubseteq> B (\<mu>\<^sub>N B)"
      by (auto intro: Mono_utp_orderD M 0)
    have 4:"(Pre \<and> E =\<^sub>u \<guillemotleft>e\<guillemotright>) \<turnstile>\<^sub>n Post \<sqsubseteq> \<dots>" 
      by (rule induct_step)
    show ?case
      using order_trans[OF 3 4] H M normal_design_theory_continuous.LFP_lemma2 dual_order.trans mono_Monotone_utp_order 
      by blast
  qed
  }
  thus ?thesis
    by pred_simp
qed  
 
lemma ndesign_mu_uwf_refine_intros: 
  assumes   WF: "`\<guillemotleft>wf R\<guillemotright>`"
    and      M: "Mono\<^bsub>uthy_order NDES\<^esub> B"
    and      H: "B \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
    and  induct_step:
    "\<And>e. ((Pre \<and> E =\<^sub>u \<guillemotleft>e\<guillemotright>) \<turnstile>\<^sub>n Post) \<sqsubseteq> (B ((Pre \<and> (E,\<guillemotleft>e\<guillemotright>)\<^sub>u\<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Post))"
  shows "(Pre \<turnstile>\<^sub>n Post) \<sqsubseteq> \<mu>\<^sub>N B" 
proof (induction rule: ndesign_mu_wf_refine_intro[of R _ _ E ])
  case 1
  then show ?case using WF by rel_blast 
next
  case 2
  then show ?case using M by assumption 
next
  case 3
  then show ?case using H by assumption   
next
  case (4 e)
  then show ?case using induct_step by simp  
qed
term "uop measure (\<lambda>_ \<bullet> Rdd)"
lemma ndesign_mu_uwf_refine_introsda: 
  assumes        M: "Mono\<^bsub>uthy_order NDES\<^esub> B"
    and      H: "B \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
    and  induct_step:
    "\<And>e. ((Pre \<and> E =\<^sub>u \<guillemotleft>e\<guillemotright>) \<turnstile>\<^sub>n Post) \<sqsubseteq> (B ((Pre \<and> (E,\<guillemotleft>e\<guillemotright>)\<^sub>u\<in>\<^sub>u (uop measure (\<lambda>_ \<bullet> E))) \<turnstile>\<^sub>n Post))"
  shows "(Pre \<turnstile>\<^sub>n Post) \<sqsubseteq> \<mu>\<^sub>N B" 
   term "(measure o Rep_uexpr) E" 
proof (induction rule: ndesign_mu_wf_refine_intro[of R _ _ E ])
  case 1
  then show ?case using WF by rel_blast 
next
  case 2
  then show ?case using M by assumption 
next
  case 3
  then show ?case using H by assumption   
next
  case (4 e)
  then show ?case using induct_step by simp  
qed   
end