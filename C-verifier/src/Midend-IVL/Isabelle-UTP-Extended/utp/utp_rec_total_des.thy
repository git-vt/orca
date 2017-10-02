theory utp_rec_total_des
  imports "../../Isabelle-UTP/theories/utp_designs"
begin
  
lemma  wf_fixp_induct_pure_des_rule: 
  assumes fixp_unfold: "fp B = B (fp B)"
  and              WF: "wf R"
  and     induct_step:
          "\<And>f st. \<lbrakk>\<And>st'. (st',st) \<in> R  \<Longrightarrow> (((Pre \<and> \<lceil>E\<rceil>\<^sub><  =\<^sub>u\<guillemotleft>st'\<guillemotright>) \<turnstile> Post) \<sqsubseteq> f)\<rbrakk> \<Longrightarrow> 
           fp B = f \<Longrightarrow>((Pre \<and> \<lceil>E\<rceil>\<^sub><  =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> Post) \<sqsubseteq> (B f)"
  shows "((Pre \<turnstile> Post) \<sqsubseteq> fp B)"  
proof -
  { fix st 
    have "(((Pre \<and> \<lceil>E\<rceil>\<^sub><  =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> Post) \<sqsubseteq> (fp B))" 
      using WF
      apply (induction st rule: wf_induct_rule)  
      apply (subst fixp_unfold)  
      apply (rule induct_step)  
      apply blast
      apply simp  
      done  
  }
  thus ?thesis
    by rel_auto
qed  
  
lemma  wf_fixp_induct_pure_desr_rule: 
  assumes fixp_unfold: "fp B = B (fp B)"
  and              WF: "wf R"
  and     induct_step:
          "\<And> f st. \<lbrakk>\<And>st'. ((st',st) \<in> R  \<Longrightarrow> ((Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u\<guillemotleft>st'\<guillemotright>) \<turnstile>\<^sub>r Post) \<sqsubseteq> f)\<rbrakk> \<Longrightarrow> 
           fp B = f \<Longrightarrow>((Pre \<and> \<lceil>E\<rceil>\<^sub><  =\<^sub>u\<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r Post) \<sqsubseteq> (B f)"
        shows "(Pre \<turnstile>\<^sub>r Post) \<sqsubseteq> fp B"  
proof -
  { fix st 
    have "((Pre \<and> \<lceil>E\<rceil>\<^sub><  =\<^sub>u\<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r Post) \<sqsubseteq> (fp B)" 
      using WF
      apply (induction st rule: wf_induct_rule)  
      apply (subst fixp_unfold)  
      apply (rule induct_step)  
      apply blast
      apply simp  
      done  
  }
  thus ?thesis
    by rel_auto
qed


lemma  rec_total_rule_des: 
  assumes WF: "wf R"
  and     M: "Mono\<^bsub>uthy_order DES\<^esub> B "  
  and     H: "B \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
  and     induct_step:
          "\<And> f st. (\<forall>st'. ((st',st) \<in>R  \<longrightarrow> ((Pre \<turnstile> Post)\<lbrakk>\<guillemotleft>st'\<guillemotright>/$\<Sigma>\<rbrakk> \<sqsubseteq> f\<lbrakk>\<guillemotleft>st'\<guillemotright>/$\<Sigma>\<rbrakk>))
               \<Longrightarrow> \<mu>\<^sub>D B = f \<Longrightarrow>(Pre \<turnstile> Post)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk> \<sqsubseteq> (B f)\<lbrakk>\<guillemotleft>st\<guillemotright>/$\<Sigma>\<rbrakk>)"
  shows   "((Pre \<turnstile> Post) \<sqsubseteq> \<mu>\<^sub>D B)"  
  apply (rule wf_fixp_uinduct_des[where fp=\<mu>\<^sub>D and Pre=Pre and B=B])    
  using M H
    apply (rule design_theory_continuous.LFP_unfold)    
   apply (rule WF)  
  apply (rule induct_step)
   apply assumption
    apply assumption
  done  
 
end