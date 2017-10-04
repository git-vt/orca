section \<open>Verification Condition Testing\<close>

theory utp_hoare_rel_total
  imports "../../../../utp/utp_rec_total"
begin
    
definition while_invT :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sub>\<bottom> _ invr _ do _ od" 71) where
"while\<^sub>\<bottom> b invr p do S od = while\<^sub>\<bottom> b do S od"  


lemma uwhile_total_rule:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`"
  assumes induct_step:"\<And> st. (\<lceil>b \<and> I \<and> &\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> (\<lceil>I\<and> (&\<Sigma>,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rceil>\<^sub>> )) \<sqsubseteq> f"  
  assumes PHI:"`\<not> \<lceil>b\<rceil>\<^sub>< \<and> \<lceil>I\<rceil>\<^sub>< \<Rightarrow> \<lceil>Post\<rceil>\<^sub>>`"  
  shows "\<lbrace>Pre\<rbrace>while\<^sub>\<bottom> b invr I do f od\<lbrace>Post\<rbrace>\<^sub>u"
  unfolding  hoare_r_def while_invT_def while_bot_def
   apply (rule pre_weak_rel[of _ "\<lceil>I\<rceil>\<^sub><" ])
  using I0 
   apply pred_simp
    apply (rule rec_total_utp_rule[where Pre="\<lceil>I\<rceil>\<^sub><", OF WF])  
   apply (simp add: cond_mono monoI seqr_mono)
  apply (rule  cond_refine_rel)
     prefer 2
   apply (rule skip_refine_rel)
  using PHI
   apply pred_blast
    subgoal for  st 
      apply (rule_tac seq_refine_unrest[where s= "I \<and> (&\<Sigma>,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>" ])
         apply pred_simp
        apply pred_simp
       apply (rule order_trans[OF induct_step]) 
       apply pred_blast
      apply pred_simp
done        
  done     
 
end