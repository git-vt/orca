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
 thm monoD   
lemma Mono_thy_orderD:
  assumes M: "Mono\<^bsub>uthy_order DES\<^esub> B"
  (*and     H: "B \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H" what is the relation of H with other assumptions*)
  and       "x is \<H>\<^bsub>DES\<^esub>"
   and       "y is \<H>\<^bsub>DES\<^esub>"
  and      "y \<sqsubseteq> x"    
shows   "(B y) \<sqsubseteq> (B x)"
  using assms
  by (auto simp add: isotone_def utp_weak_partial_order)

    
  thm Mono_utp_orderI
      monoI monoD
lemma  rec_total_utp_des_rule: 
  assumes   WF: "wf R"
    and      M: "Mono\<^bsub>uthy_order DES\<^esub> B"
    and      H: "B \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    and      Okey1:"$ok\<acute> \<sharp> Pre" and Okey2:"$ok\<acute> \<sharp> Post"
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
      assume *: "\<And>st'. (st', st) \<in> R \<Longrightarrow> ((Pre \<and>\<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st'\<guillemotright>) \<turnstile> Post) \<sqsubseteq> \<mu>\<^sub>D B"
      from * have 0:"((Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile> Post) \<sqsubseteq> \<mu>\<^sub>D B"  
        by pred_blast
     from M H design_theory_continuous.LFP_lemma3 have 1: "\<mu>\<^sub>D B \<sqsubseteq>  B (\<mu>\<^sub>D B)"
       by auto     
     from 0 1 have 2:"((Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile> Post) \<sqsubseteq> B(\<mu>\<^sub>D B)"
       by simp
     have 3: "B((Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>)  \<turnstile> Post) \<sqsubseteq> B (\<mu>\<^sub>D B)"
       thm Mono_thy_orderD
        apply (rule Mono_thy_orderD[OF M])
         apply (metis (no_types) Healthy_def' des_hcond_def design_theory_continuous.LFP_closed)
         prefer 2
       apply (simp add: "0")
        unfolding prod_hcond_def Healthy_def utp_designs.des_hcond_def H1_def H2_def J_def
          using Okey1 Okey2
          apply rel_simp
          apply fastforce 
         done
        have 4:"((Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> Post) \<sqsubseteq> \<dots>"  by (rule induct_step)
      show "((Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> Post) \<sqsubseteq> B (\<mu>\<^sub>D B) "  
        using order_trans[OF 3 4] .
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