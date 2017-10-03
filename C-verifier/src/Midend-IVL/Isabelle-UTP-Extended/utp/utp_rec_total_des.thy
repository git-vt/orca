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
  

lemma  rec_total_rule_des: 
  assumes WF: "wf R"
  and     M: "Mono\<^bsub>uthy_order DES\<^esub> B "  
  and     H: "B \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
  and     induct_step:
          "\<And> f st. \<lbrakk>\<And>st'. (st',st) \<in> R  \<Longrightarrow> (((Pre \<and> \<lceil>E\<rceil>\<^sub><  =\<^sub>u\<guillemotleft>st'\<guillemotright>) \<turnstile> Post) \<sqsubseteq> f)\<rbrakk>
               \<Longrightarrow> \<mu>\<^sub>D B = f \<Longrightarrow>((Pre \<and> \<lceil>E\<rceil>\<^sub><  =\<^sub>u\<guillemotleft>st\<guillemotright>) \<turnstile> Post) \<sqsubseteq> (B f)"
  shows   "((Pre \<turnstile> Post) \<sqsubseteq> \<mu>\<^sub>D B)"  
  apply (rule wf_fixp_induct_pure_des_rule [where fp=\<mu>\<^sub>D and Pre=Pre and B=B])    
  using M H
    apply (rule design_theory_continuous.LFP_unfold)    
   apply (rule WF)  
  apply (rule induct_step)
   apply assumption
    apply assumption
  done
    
lemma 1:  
   assumes   WF: "wf R"
  assumes "$ok\<acute> \<sharp> Pre" "$ok\<acute> \<sharp> Post"
  assumes "(\<And>st'. (st', st) \<in> R \<Longrightarrow> ((Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st'\<guillemotright> ) \<turnstile> Post) \<sqsubseteq> \<mu>\<^sub>D B)"
  shows "(( Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>  Post) \<sqsubseteq> \<mu>\<^sub>D B"
  using assms
  by (pred_blast)
    
lemma 2:  
   assumes   WF: "wf R"
  assumes "$ok\<acute> \<sharp> Pre" "$ok\<acute> \<sharp> Post"
  shows "\<And>st. (\<And>st'. (st'  , st) \<in> R \<Longrightarrow> ((Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st'\<guillemotright> ) \<turnstile> Post) \<sqsubseteq> \<mu>\<^sub>D B) \<Longrightarrow>
         (( Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>  Post) \<sqsubseteq> \<mu>\<^sub>D B"
  by (pred_blast)
    
find_theorems "LFP" "mono"
lemma  rec_total_utp_des_rule: 
  assumes   WF: "wf R"
    and      M: "Mono\<^bsub>uthy_order DES\<^esub> B"
    and      H: "B \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    and  induct_step:
    "\<And>st. ((Pre \<and>\<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> Post) \<sqsubseteq> (B ((Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile> Post))"
  shows "(Pre \<turnstile> Post) \<sqsubseteq> \<mu>\<^sub>D B"  
proof -          
  { fix st
    have "((Pre \<and>\<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> Post)\<sqsubseteq> (\<mu>\<^sub>D B)" 
      using WF
      apply (induction  rule: wf_induct_rule)  
      apply (subst design_theory_continuous.LFP_unfold [OF M H])
    proof -
      fix st 
      assume *: "\<And>st'. (st'  , st) \<in> R \<Longrightarrow> ((Pre \<and>\<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st'\<guillemotright>) \<turnstile> Post) \<sqsubseteq> \<mu>\<^sub>D B"
      hence "((Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile> Post) \<sqsubseteq> \<mu>\<^sub>D B"  
        by pred_blast
      hence 1: "B ((Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<Rightarrow> Post)) \<sqsubseteq> B (\<mu>\<^sub>D B)"    
        by (rule monoD[OF M])
      have 2: "(Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> \<dots>" 
        by (rule induct_step)  
      show "(Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> B (\<mu> B) "  
        using order_trans[OF 1 2] .
    qed  
  }
  thus ?thesis
    by pred_simp
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

 
 
end