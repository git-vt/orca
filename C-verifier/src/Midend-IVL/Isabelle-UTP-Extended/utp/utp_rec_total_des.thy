theory utp_rec_total_des
  imports "../hoare/AlgebraicLaws/Design/Algebraic_laws_design"
begin

lemma mu_design_is_healthy_des[simp]: (*This should be genrated automatically in utp_theory*)
  "\<mu>\<^sub>D B is \<H>\<^bsub>DES\<^esub>"    
  by (metis (no_types) Healthy_def' des_hcond_def design_theory_continuous.LFP_closed)


lemma mu_normal_design_is_healthy_des[simp]: (*This should be genrated automatically in utp_theory*)
  "\<mu>\<^sub>N B is \<H>\<^bsub>NDES\<^esub>"
  by (metis (no_types) Healthy_def' ndes_hcond_def normal_design_theory_continuous.LFP_closed) 

lemma design_is_healthy_des:"$ok\<acute> \<sharp> Pre \<Longrightarrow> Pre \<turnstile> Post is \<H>\<^bsub>DES\<^esub>" 
  apply rel_simp 
  apply fastforce
done    

lemma rdesign_is_healthy_des[simp]: (*This should be genrated automatically in utp_theory*)
  "Pre \<turnstile>\<^sub>r Post is \<H>\<^bsub>DES\<^esub>"
  by (simp add: rdesign_def design_is_healthy_des unrest)  

lemma ndesign_is_healthy_des[simp]: (*This should be genrated automatically in utp_theory*)
  "Pre \<turnstile>\<^sub>n Post is \<H>\<^bsub>NDES\<^esub>"
  apply rel_simp 
  apply fastforce
done
    
lemma Mono_utp_orderD: (*This should be genrated automatically in utp_theory*)
  assumes M: "Mono\<^bsub>utp_order H\<^esub> B"
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
      apply (rule Mono_utp_orderD [OF M _ _ 0], simp)
      using Okey1
      apply rel_simp
      apply fastforce
    done    
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
    "\<And>st. ((Pre \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n Post) \<sqsubseteq> (B ((Pre \<and> (E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Post))"
  shows "(Pre \<turnstile>\<^sub>n Post) \<sqsubseteq> \<mu>\<^sub>N B"            
proof -          
  {
  fix st
  have "(Pre \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n Post \<sqsubseteq> \<mu>\<^sub>N B" 
    using WF proof (induction rule: wf_induct_rule)
    case (less st)
    hence 0: "(Pre \<and> (E, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Post \<sqsubseteq> \<mu>\<^sub>N B"
      by rel_blast
    from M H normal_design_theory_continuous.LFP_lemma3 mono_Monotone_utp_order
    have 1: "\<mu>\<^sub>N B \<sqsubseteq>  B (\<mu>\<^sub>N B)"
      by blast
    from 0 1 have 2:"(Pre \<and> (E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Post \<sqsubseteq> B (\<mu>\<^sub>N B)"
      by simp
    have 3: "B ((Pre \<and> (E, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Post) \<sqsubseteq> B (\<mu>\<^sub>N B)"
      by (auto intro: Mono_utp_orderD M 0)
    have 4:"(Pre \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n Post \<sqsubseteq> \<dots>" 
      by (rule induct_step)
    show ?case
      using order_trans[OF 3 4] H M normal_design_theory_continuous.LFP_lemma2 dual_order.trans mono_Monotone_utp_order 
      by blast
  qed
  }
  thus ?thesis
    by pred_simp
qed    
  
end