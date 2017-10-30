section \<open>Verification Condition Testing\<close>

theory utp_hoare_rel_total
  imports "../../PartialCorrectness/utp_hoare"
begin
  
definition while_invT :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sub>\<bottom> _ invr _ do _ od" 71) where
"while\<^sub>\<bottom> b invr p do S od = while\<^sub>\<bottom> b do S od"  

lemma while_wf_hoare_r:
  assumes WF: "wf R"
  assumes I0: "`pre \<Rightarrow> I`"
  assumes induct_step:"\<And> st. \<lbrace>b \<and> I \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>Q\<lbrace>I \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  assumes PHI:"`(\<not>b \<and> I) \<Rightarrow> post`"  
  shows "\<lbrace>pre\<rbrace>while\<^sub>\<bottom> b invr I do Q od\<lbrace>post\<rbrace>\<^sub>u"
unfolding hoare_r_def while_invT_def while_bot_def
proof (rule pre_weak_rel[of _ "\<lceil>I\<rceil>\<^sub><" ])
  from I0 show "`\<lceil>pre\<rceil>\<^sub>< \<Rightarrow> \<lceil>I\<rceil>\<^sub><`"
    by rel_auto
  show "(\<lceil>I\<rceil>\<^sub>< \<Rightarrow> \<lceil>post\<rceil>\<^sub>>) \<sqsubseteq> (\<mu> X \<bullet> Q ;; X \<triangleleft> b \<triangleright>\<^sub>r II)"
  proof (rule rec_total_utp_rule[where E=e, OF WF])
    show "mono (\<lambda>X. Q ;; X \<triangleleft> b \<triangleright>\<^sub>r II)"
      by (simp add: cond_mono monoI seqr_mono)
    have induct_step': "\<And> st. (\<lceil>b \<and> I \<and>  e =\<^sub>u \<guillemotleft>st\<guillemotright> \<rceil>\<^sub>< \<Rightarrow> (\<lceil>I \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright> \<rceil>\<^sub>> )) \<sqsubseteq> Q"
      using induct_step by rel_auto  
    with PHI
    show "\<And>st. (\<lceil>I\<rceil>\<^sub>< \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> \<lceil>post\<rceil>\<^sub>>) \<sqsubseteq> Q ;; (\<lceil>I\<rceil>\<^sub>< \<and> (\<lceil>e\<rceil>\<^sub><, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright> \<Rightarrow> \<lceil>post\<rceil>\<^sub>>) \<triangleleft> b \<triangleright>\<^sub>r II" 
      by (rel_auto)
  qed       
qed

 
end