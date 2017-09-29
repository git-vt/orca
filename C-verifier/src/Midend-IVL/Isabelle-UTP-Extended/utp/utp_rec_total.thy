theory utp_rec_total
  imports  "../hoare/HoareLogic/PartialCorrectness/utp_hoare"
begin
  
lemma "\<lbrakk>\<lceil>p\<rceil>\<^sub><\<Rightarrow> \<lceil>q\<rceil>\<^sub>>\<rbrakk>\<^sub>e (s,s') = (\<lbrakk>\<lceil>p\<rceil>\<^sub><\<rbrakk>\<^sub>e(s,UNIV) \<longrightarrow> \<lbrakk>\<lceil>q\<rceil>\<^sub>>\<rbrakk>\<^sub>e (UNIV, s'))"
  by rel_auto
    
section {*Noetherian induction instantiation*}
      
(*This  generalization was used by Tobias Nipkow in .. and Peter Lammich  in Refine_Monadic*)

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
  
text {*The next lemma shows that using substitution also work but is is not that generic..*}

lemma refine_usubst_to_ueq:
  "vwb_lens E \<Longrightarrow>(Pre \<Rightarrow> Post)\<lbrakk>\<guillemotleft>st'\<guillemotright>/$E\<rbrakk> \<sqsubseteq> f\<lbrakk>\<guillemotleft>st'\<guillemotright>/$E\<rbrakk> = (((Pre \<and> $E =\<^sub>u \<guillemotleft>st'\<guillemotright>) \<Rightarrow> Post) \<sqsubseteq> f)"
  apply rel_auto
  apply (metis vwb_lens_wb wb_lens.get_put)
done  

lemma wf_fixp_uinduct_pure_usubst: (*TODO @Yakoub: Maybe wf_fixp_uinduct_pure_usubst is redundant and itshould be just a lemmas*)            
  assumes fixp_unfold: "fp B = B (fp B)"
  and              WF: "wf R"
  and     induct_step:
          "\<And>f st. \<lbrakk>\<And>st'. (st',st) \<in>R  \<Longrightarrow> ((Pre \<Rightarrow> Post)\<lbrakk>\<guillemotleft>st'\<guillemotright>/ $\<Sigma>\<rbrakk> \<sqsubseteq> f\<lbrakk>\<guillemotleft>st'\<guillemotright>/ $\<Sigma>\<rbrakk>)\<rbrakk>\<Longrightarrow> 
                    fp B = f \<Longrightarrow>(Pre \<Rightarrow> Post)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk> \<sqsubseteq> (B f)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk>"
  shows "(Pre \<Rightarrow> Post) \<sqsubseteq> fp B"  
  using wf_fixp_uinduct_pure_usubst_gen[of fp B R "\<Sigma>" Pre Post ] assms
  by simp
 
     

    
lemma foo:
assumes 
        "fp B = B (fp B)"
    and "wf R"
    and "vwb_lens E"
    and
    "\<And>f st.
        (\<And>st'.
            (st', st) \<in> R \<Longrightarrow>
            (Pre \<and> $E =\<^sub>u \<guillemotleft>st'\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> f) \<Longrightarrow>
        fp B = f \<Longrightarrow> (Pre \<and> $E =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> B f"
  shows "(Pre \<Rightarrow> Post) \<sqsubseteq> fp B"  
  using assms wf_fixp_uinduct_pure_usubst_gen[of fp B,OF assms(1,2,3)] refine_usubst_to_ueq_gen
  by metis  
  

thm wf_fixp_uinduct_pure_usubst[simplified refine_usubst_to_ueq]  
text{*Following usubst_to_ueq we can have...*}

         
    
  thm wf_inv_image  
    
  thm wf_fixp_uinduct_pure_ueq_gen[where E="&E"]  
    
  using foo[of E fp]
        assms
  by auto
    
lemma  wf_fixp_uinduct_pure_ueq: (*TODO @Yakoub: Maybe wf_fixp_uinduct_pure_ueq is redundant and it should be just a lemmas*)                 
  assumes fixp_unfold: "fp B = B (fp B)"
  and              WF: "wf R"
  and     induct_step:
          "\<And>f st. \<lbrakk>\<And>st'. (st',st) \<in>R  \<Longrightarrow> (((Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st'\<guillemotright>) \<Rightarrow> Post) \<sqsubseteq> f)\<rbrakk>
               \<Longrightarrow> fp B = f \<Longrightarrow>((Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright>) \<Rightarrow> Post) \<sqsubseteq> (B f)"
        shows "((Pre \<Rightarrow> Post) \<sqsubseteq> fp B)"  
  using wf_fixp_uinduct_pure_usubst[simplified refine_usubst_to_ueq,of fp B R Pre Post] assms
  by simp
      
lemma  rec_total_rule_pure: 
  assumes WF: "wf R"
  and     M: "mono B"  
  and     induct_step:
          "\<And> f st.  \<lbrakk>(Pre \<and> ($\<Sigma>,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> f\<rbrakk>
               \<Longrightarrow> \<mu> B = f \<Longrightarrow>(Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> (B f)"
        shows "(Pre \<Rightarrow> Post) \<sqsubseteq> \<mu> B"  
  apply (rule  wf_fixp_uinduct_pure_usubst[simplified refine_usubst_to_ueq, where fp=\<mu> and Pre=Pre and B=B])    
  using M apply (rule gfp_unfold)    
   apply (rule WF)  
  apply (rule induct_step)
    apply pred_simp
   apply assumption
  done     

(*TODO @Yakoub: the proof of rec_total_rule_utp is totally independent from
  wf_fixp_uinduct_pure_ueq. Make it dependent to keep the logic reasoning straight*)
lemma  rec_total_utp_rule: 
  assumes WF: "wf R"
    and     M: "mono B"  
    and     induct_step:
    "\<And>st. (Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> (B ((Pre \<and> ($\<Sigma>,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<Rightarrow> Post)))"
  shows "(Pre \<Rightarrow> Post) \<sqsubseteq> \<mu> B"  
proof -          
  { fix st
    have "(Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post)\<sqsubseteq> (\<mu> B)" 
      using WF
      apply (induction rule: wf_induct_rule)  
      apply (subst gfp_unfold[OF M])
    proof -
      fix st
      assume "(\<And>st'. (st', st) \<in> R \<Longrightarrow> (Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st'\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> \<mu> B)"
      hence "(Pre \<and> ($\<Sigma>,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> \<mu> B"  
        by (pred_simp)
      hence 1: "B ((Pre \<and> ($\<Sigma>,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<Rightarrow> Post)) \<sqsubseteq> B (\<mu> B)"    
        by (rule monoD[OF M])
      have 2: "(Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> \<dots>" by (rule induct_step)
          
      show "(Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> B (\<mu> B) "  
        using order_trans[OF 1 2] .
    qed  
  }
  thus ?thesis
    by pred_simp
qed            

section {*Examples*}

(*The lemma total_rec_utp_test shows how rec_total_utp_rule improves automation wrt
  rec_total_rule_pure which was used for the same example in  total_rec_test*)  
lemma total_rec_utp_test:
  "vwb_lens x \<Longrightarrow> 
   (\<lceil>true\<rceil>\<^sub><\<Rightarrow> \<lceil>&x \<le>\<^sub>u \<guillemotleft>0::int\<guillemotright>\<rceil>\<^sub>>) \<sqsubseteq> (\<mu> R \<bullet> ((x :== (&x - \<guillemotleft>1\<guillemotright>)) ;; R) \<triangleleft> &x >\<^sub>u \<guillemotleft>0::int\<guillemotright> \<triangleright>\<^sub>r II)"    
  apply (rule  rec_total_utp_rule[where R="measure (nat o \<lbrakk>&x\<rbrakk>\<^sub>e)"])  
    apply simp
     apply (simp add: cond_mono monoI seqr_mono)
  apply (rule  cond_refine_rel)
     prefer 2
     apply pred_simp+      
  done
    
lemma total_rec_test:
  "vwb_lens x \<Longrightarrow> 
   (\<lceil>true\<rceil>\<^sub><\<Rightarrow> \<lceil>&x \<le>\<^sub>u \<guillemotleft>0::int\<guillemotright>\<rceil>\<^sub>>) \<sqsubseteq> (\<mu> R \<bullet> ((x :== (&x - \<guillemotleft>1\<guillemotright>)) ;; R) \<triangleleft> &x >\<^sub>u \<guillemotleft>0::int\<guillemotright> \<triangleright>\<^sub>r II)"    
  apply (rule   rec_total_rule_pure[where R="measure (nat o \<lbrakk>&x\<rbrakk>\<^sub>e)"])  
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
 

end