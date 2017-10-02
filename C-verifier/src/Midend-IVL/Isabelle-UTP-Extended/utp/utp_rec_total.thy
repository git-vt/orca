theory utp_rec_total
  imports  "../hoare/HoareLogic/PartialCorrectness/utp_hoare"
begin
text {*The following lemma explains the intuition behind lifting operators from predicates to relations.
       While in relational setting both, input and output state are evaluated. A predicate
       evaluate only on a single state. To unify predicates and relations such a lifting is necessary.
       This gives away to express Hoare logic in relational calculus.*}
  
lemma "\<lbrakk>\<lceil>p\<rceil>\<^sub><\<Rightarrow> \<lceil>q\<rceil>\<^sub>>\<rbrakk>\<^sub>e (s,s') = (\<lbrakk>\<lceil>p\<rceil>\<^sub><\<rbrakk>\<^sub>e(s,UNIV) \<longrightarrow> \<lbrakk>\<lceil>q\<rceil>\<^sub>>\<rbrakk>\<^sub>e (UNIV, s'))"
  by rel_auto
    
section {*Noetherian induction instantiation*}
      
(*The following generalization was used by Tobias Nipkow in .. and Peter Lammich  in Refine_Monadic*)

lemma  wf_fixp_uinduct_pure_ueq_gen:     
  assumes fixp_unfold: "fp B = B (fp B)"
  and              WF: "wf R"
  and     induct_step:
          "\<And>f st. \<lbrakk>\<And>st'. (st',st) \<in>R  \<Longrightarrow> (((Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st'\<guillemotright>) \<Rightarrow> Post) \<sqsubseteq> f)\<rbrakk>
               \<Longrightarrow> fp B = f \<Longrightarrow>((Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<Rightarrow> Post) \<sqsubseteq> (B f)"
        shows "((Pre \<Rightarrow> Post) \<sqsubseteq> fp B)"  
 proof -  
   { fix st
    have "((Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<Rightarrow> Post) \<sqsubseteq> (fp B)" 
      using WF
      apply (induction rule: wf_induct_rule)  
      apply (subst fixp_unfold)  
      apply (rule induct_step)  
      apply pred_blast
      apply simp  
      done  
     }
    thus ?thesis 
    by pred_simp  
qed
  
text {*The next lemma shows that using substitution also work. However it is not that generic
       nor practical for proof automation ...*}

lemma refine_usubst_to_ueq:
  "vwb_lens E \<Longrightarrow>(Pre \<Rightarrow> Post)\<lbrakk>\<guillemotleft>st'\<guillemotright>/$E\<rbrakk> \<sqsubseteq> f\<lbrakk>\<guillemotleft>st'\<guillemotright>/$E\<rbrakk> = (((Pre \<and> $E =\<^sub>u \<guillemotleft>st'\<guillemotright>) \<Rightarrow> Post) \<sqsubseteq> f)"
  apply rel_auto
  apply (metis vwb_lens_wb wb_lens.get_put)
done  

text {*By instantiation of @{thm wf_fixp_uinduct_pure_ueq_gen} with @{term \<mu>}and lifting of the 
       well-founded relation we have ...*}
  
lemma  rec_total_pure_rule: 
  assumes WF: "wf R"
  and     M: "mono B"  
  and     induct_step:
          "\<And> f st.  \<lbrakk>(Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> f\<rbrakk>
               \<Longrightarrow> \<mu> B = f \<Longrightarrow>(Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> (B f)"
        shows "(Pre \<Rightarrow> Post) \<sqsubseteq> \<mu> B"  
  apply (rule  wf_fixp_uinduct_pure_ueq_gen[where fp=\<mu> and Pre=Pre and B=B])    
  using M apply (rule gfp_unfold)    
   apply (rule WF)  
  apply (rule induct_step)
    apply pred_simp
   apply assumption
  done     

(*TODO @Yakoub: the proof of rec_total_utp_rule is totally independent from
  wf_fixp_uinduct_pure_ueq. Make it dependent to keep the logic reasoning straight*)
text {*Since @{term "B ((Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<Rightarrow> Post)) \<sqsubseteq> B (\<mu> B)"} and 
      @{term "mono B"}, thus,  @{thm rec_total_pure_rule} can be expressed as follows*}
  
lemma  rec_total_utp_rule: 
  assumes WF: "wf R"
    and     M: "mono B"  
    and     induct_step:
    "\<And>st. (Pre \<and>\<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> (B ((Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<Rightarrow> Post)))"
  shows "(Pre \<Rightarrow> Post) \<sqsubseteq> \<mu> B"  
proof -          
  { fix st
    have "(Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post)\<sqsubseteq> (\<mu> B)" 
      using WF
      apply (induction rule: wf_induct_rule)  
      apply (subst gfp_unfold[OF M])
    proof -
      fix st
      assume "(\<And>st'. (st', st) \<in> R \<Longrightarrow> (Pre \<and> \<lceil>E\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st'\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> \<mu> B)"
      hence "(Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> \<mu> B"  
        by (pred_simp)
      hence 1: "B ((Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<Rightarrow> Post)) \<sqsubseteq> B (\<mu> B)"    
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

section {*Examples*}

(*The lemma total_rec_utp_test shows how rec_total_utp_rule improves automation wrt
  rec_total_pure_rule which was used for the same example in  total_rec_test*)  
lemma total_rec_utp_test:
  "vwb_lens x \<Longrightarrow> 
   (\<lceil>true\<rceil>\<^sub><\<Rightarrow> \<lceil>&x \<le>\<^sub>u \<guillemotleft>0::int\<guillemotright>\<rceil>\<^sub>>) \<sqsubseteq> (\<mu> R \<bullet> ((x :== (&x - \<guillemotleft>1\<guillemotright>)) ;; R) \<triangleleft> &x >\<^sub>u \<guillemotleft>0::int\<guillemotright> \<triangleright>\<^sub>r II)"    
  apply (rule  rec_total_utp_rule[where R="measure (nat o \<lbrakk>&x\<rbrakk>\<^sub>e)" and E = "&\<Sigma>"])  
    apply simp
     apply (simp add: cond_mono monoI seqr_mono)
  apply (rule  cond_refine_rel)
     prefer 2
     apply pred_simp+      
  done
    
lemma total_rec_test:
  "vwb_lens x \<Longrightarrow> 
   (\<lceil>true\<rceil>\<^sub><\<Rightarrow> \<lceil>&x \<le>\<^sub>u \<guillemotleft>0::int\<guillemotright>\<rceil>\<^sub>>) \<sqsubseteq> (\<mu> R \<bullet> ((x :== (&x - \<guillemotleft>1\<guillemotright>)) ;; R) \<triangleleft> &x >\<^sub>u \<guillemotleft>0::int\<guillemotright> \<triangleright>\<^sub>r II)"    
  apply (rule   rec_total_pure_rule[where R="measure (nat o \<lbrakk>&x\<rbrakk>\<^sub>e)" and E = "&\<Sigma>"])  
    apply simp
     apply (simp add: cond_mono monoI seqr_mono)   
  apply (rule  cond_refine_rel)
     prefer 2
     apply pred_simp      
    subgoal premises prems for f st   
    apply (rule seq_refine_unrest[where s="0 \<le>\<^sub>u &x \<and> &\<Sigma> =\<^sub>u \<guillemotleft>([x\<mapsto>\<^sub>s &x-1] st)\<guillemotright>"]) 
     apply pred_simp 
      apply pred_simp 
      using prems(1) apply pred_simp 
      apply (rule pre_weak_rel[rotated]) 
      apply (rule prems(2))  
      using prems(1) apply pred_simp 
      done
    done
      
definition while_invT :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sub>\<bottom> _ invr _ do _ od" 71) where
"while\<^sub>\<bottom> b invr p do S od = while\<^sub>\<bottom> b do S od"  


lemma uwhile_total_rule:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`"
  assumes induct_step:"\<And> st. (\<lceil>b \<and> I \<and>  E =\<^sub>u \<guillemotleft>st\<guillemotright> \<rceil>\<^sub>< \<Rightarrow> (\<lceil>I \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rceil>\<^sub>> )) \<sqsubseteq> f"  
  assumes PHI:"`\<not> \<lceil>b\<rceil>\<^sub>< \<and> \<lceil>I\<rceil>\<^sub>< \<Rightarrow> \<lceil>Post\<rceil>\<^sub>>`"  
  shows "\<lbrace>Pre\<rbrace>while\<^sub>\<bottom> b invr I do f od\<lbrace> Post\<rbrace>\<^sub>u"
  unfolding  hoare_r_def while_invT_def while_bot_def
   apply (rule pre_weak_rel[of _ "\<lceil>I\<rceil>\<^sub><" ])
  using I0 
   apply pred_simp
    apply (rule rec_total_utp_rule[where Pre="\<lceil>I\<rceil>\<^sub><" and E = E, OF WF])  
   apply (simp add: cond_mono monoI seqr_mono)
  apply (rule  cond_refine_rel)
     prefer 2
   apply (rule skip_refine_rel)
  using PHI
   apply pred_blast
    subgoal for  st 
      apply (rule_tac seq_refine_unrest[where s= "I \<and> (E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>" ])
         apply pred_simp
        apply pred_simp
       apply (rule order_trans[OF induct_step, where st1 = st]) 
       apply pred_simp 
      apply pred_simp
done        
  done 

end