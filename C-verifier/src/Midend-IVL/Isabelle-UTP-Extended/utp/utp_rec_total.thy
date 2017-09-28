theory utp_rec_total
  imports  "../hoare/HoareLogic/PartialCorrectness/utp_hoare"
begin
        
lift_definition uwfP::"('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>  ('a, 'a) rel" is
"\<lambda> P r.  (r \<in> {(x, y). wfP P \<and> P x y})" .  
update_uexpr_rep_eq_thms -- {* Reread @{text rep_eq} theorems. *}     

term "\<forall> x \<in> X. ((\<forall>y \<in> X. (R x y \<longrightarrow> P y)) \<longrightarrow> P x)\<longrightarrow> (\<forall>x \<in> X. P x)"
  
term "\<^bold>\<forall>st \<bullet> \<^bold>\<forall>f \<bullet> ((\<^bold>\<forall> st'\<bullet> \<guillemotleft>(st',st) \<in>R\<guillemotright> \<Rightarrow> \<guillemotleft>(Pre \<Rightarrow> Post) \<sqsubseteq> (B f)\<guillemotright>) \<Rightarrow> \<guillemotleft>(Pre \<Rightarrow> Post) \<sqsubseteq> (B f)\<guillemotright>) "

lemma "`\<^bold>\<forall> x \<bullet> ((\<^bold>\<forall> y \<bullet> (\<lceil>\<guillemotleft>(y,x) \<in>R\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> P\<lbrakk>\<guillemotleft>y\<guillemotright>/ &\<Sigma>\<rbrakk>)) \<Rightarrow> P\<lbrakk>\<guillemotleft>x\<guillemotright>/ &\<Sigma>\<rbrakk> )` = 
        (\<forall>x. (\<forall>y. (y, x) \<in> R \<longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>e y)\<longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>e x)"
  by pred_auto 

term "\<forall> x \<in> X. ((\<forall>y \<in> X. (R x y \<longrightarrow> P y)) \<longrightarrow> P x)\<longrightarrow> (\<forall>x \<in> X. P x)" 
term " (subst_upd id \<Sigma>) \<dagger> P" 
term"(subst_upd id \<Sigma> \<guillemotleft>s\<guillemotright>)"
term "[$\<Sigma> \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>] :: ('a \<times> 'b )\<Rightarrow>('a \<times> 'b )"  
  
 term "([$\<Sigma> \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>] :: ('a \<times> 'b )\<Rightarrow>('a \<times> 'b ) )\<dagger> (P:: ('a, 'b) rel)" 
term "((Pre\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk>) \<Rightarrow> Post)"  
  
lemma "Rep_uexpr (P\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk>) (s,s') \<longleftrightarrow> Rep_uexpr P (st,s')"  
  by rel_auto
  
  
lemma "([$\<Sigma> \<mapsto>\<^sub>s \<guillemotleft>sx\<guillemotright>] :: ('a \<times> 'b )\<Rightarrow>('a \<times> 'b )) = 
  (\<lambda>(s,s'). (sx,s'))"  
  by rel_auto  
  
lemma "(subst_upd id \<Sigma> \<guillemotleft>s\<guillemotright>) = (\<lambda>_. s)"
  by rel_auto  
  
  
  
lemma foo: "(\<forall>st .(Pre \<Rightarrow> Post)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk> \<sqsubseteq> (B f)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk>) = 
         ((Pre \<Rightarrow> Post) \<sqsubseteq> (B f))"
  by pred_simp
   
lemma pre_str:
  assumes "`Pre \<Rightarrow> I`"
  and     "(I \<Rightarrow> Post) \<sqsubseteq> P"
  shows "(Pre \<Rightarrow> Post) \<sqsubseteq> P"
 using assms
  by(rel_auto)

lemma cond_refine_split': 
  assumes "(b \<and> p \<Rightarrow> q) \<sqsubseteq> C\<^sub>1" and "(\<not>b \<and> p \<Rightarrow> q)\<sqsubseteq> C\<^sub>2" 
  shows "(p \<Rightarrow> q) \<sqsubseteq> (C\<^sub>1 \<triangleleft> b \<triangleright> C\<^sub>2)"
  by (insert assms) rel_auto
    
    
lemma cond_refine_split: 
  assumes "(\<lceil>b \<and> p\<rceil>\<^sub><\<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> C\<^sub>1" and "(\<lceil>\<not>b \<and> p\<rceil>\<^sub><\<Rightarrow> \<lceil>q\<rceil>\<^sub>>)\<sqsubseteq> C\<^sub>2" 
  shows "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> (C\<^sub>1 \<triangleleft> \<lceil>b\<rceil>\<^sub>< \<triangleright> C\<^sub>2)"
  by (insert assms) rel_auto
    
lemma seq_refine_split:
  assumes "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>s\<rceil>\<^sub>>)\<sqsubseteq> f" and"(\<lceil>s\<rceil>\<^sub>< \<Rightarrow>  \<lceil>q\<rceil>\<^sub>>)\<sqsubseteq> fa"
  shows "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk> \<sqsubseteq> (f ;; fa)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk>"
  by (insert assms) rel_auto     

    
lemma seq_refine_split':
  assumes "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>s\<rceil>\<^sub>>) \<sqsubseteq> f" and "(\<lceil>s\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> fa"
  (*and "in\<alpha> \<sharp> p"  *)
  shows "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> (f ;; fa)"
  apply (insert assms)
  apply rel_simp
  done  
    
lemma seq_refine_split'':
  assumes "out\<alpha> \<sharp> p" "in\<alpha> \<sharp> q"
  assumes "(p \<Rightarrow> \<lceil>s\<rceil>\<^sub>>) \<sqsubseteq> f" and "(\<lceil>s\<rceil>\<^sub>< \<Rightarrow> q) \<sqsubseteq> fa"
  shows "(p \<Rightarrow> q) \<sqsubseteq> (f ;; fa)"
  apply (insert assms)
  apply rel_blast
  done  
    
   
    
    
lemma skip_refine_orig:
  "(p \<Rightarrow> p) \<sqsubseteq> II"
  by pred_blast

lemma [simp]: "\<lbrakk>II\<rbrakk>\<^sub>e (a, b) \<longleftrightarrow> a=b"
  apply rel_simp
  by auto  
    
lemma skip_refine_XX:
  "(p \<Rightarrow> q) \<sqsubseteq> II \<longleftrightarrow> `((p \<squnion> II) \<Rightarrow> q)`"
  apply pred_auto
  done  

lemma skip_refine_XXX:
  "`(II \<Rightarrow> (p \<Rightarrow> q))` \<Longrightarrow> (p \<Rightarrow> q) \<sqsubseteq> II"
  apply pred_auto
  done  
    
    
lemma str_post: "(p\<Rightarrow>q) \<sqsubseteq> P \<Longrightarrow> `q\<Rightarrow>r` \<Longrightarrow> (p\<Rightarrow>r) \<sqsubseteq> P"
  by pred_blast
    
lemmas skip_refine' = str_post[OF skip_refine_orig]

  
lemma skip_refine:
  "`(p \<Rightarrow> q)` \<Longrightarrow> (\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> II"
  by rel_auto
  
    
lemma skip_refine:
  "`(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk>` \<Longrightarrow> (\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk> \<sqsubseteq> II\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk>"
  by pred_blast
    
lemma 11:"(\<lceil>b\<rceil>\<^sub>< \<and> \<lceil>I\<rceil>\<^sub><)  = \<lceil>b \<and> I\<rceil>\<^sub><"
  by ( simp add: utp_alphabet.alpha)

lemma 12: "\<not>\<lceil>b\<rceil>\<^sub>< = \<lceil>\<not>b\<rceil>\<^sub><"    
  by pred_auto

      
(*This is a generalization done by Peter Lammich  in Refine_Monadic*)

lemma  wf_fixp_uinduc_HOL: 
  assumes fixp_unfold: "fp B = B (fp B)"
  and              WF: "wf R"
  and     induct_step:
          "\<And>f st. (\<forall>st'. ((st',st) \<in>R  \<longrightarrow> ((Pre \<Rightarrow> Post)\<lbrakk>\<guillemotleft>st'\<guillemotright>/ $\<Sigma>\<rbrakk> \<sqsubseteq> f\<lbrakk>\<guillemotleft>st'\<guillemotright>/ $\<Sigma>\<rbrakk>))
               \<Longrightarrow> fp B = f \<Longrightarrow>(Pre \<Rightarrow> Post)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk> \<sqsubseteq> (B f)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk>)"
  shows "((Pre \<Rightarrow> Post) \<sqsubseteq> fp B)"  
proof -  
   { fix st
    have "((Pre \<Rightarrow> Post)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk> \<sqsubseteq> (fp B)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk>)" 
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

term "(P \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright>) \<Rightarrow> Q"

term "(\<lceil>P  \<and> &\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright>\<rceil>\<^sub><) \<Rightarrow> Q"
  
lemma "Rep_uexpr ((P \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright>) \<Rightarrow> Q) (s,s') = 
        (s=st \<and> Rep_uexpr P (st, s') \<longrightarrow> Rep_uexpr Q (st, s'))"  
  by (rel_auto)
    
lemma  wf_fixp_uinduct_Pure': 
  assumes fixp_unfold: "fp B = B (fp B)"
  and              WF: "wf R"
  and     induct_step:
          "\<And>f st. \<lbrakk>\<And>st'. (st',st) \<in>R  \<Longrightarrow> (((Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st'\<guillemotright>) \<Rightarrow> Post) \<sqsubseteq> f)\<rbrakk>
               \<Longrightarrow> fp B = f \<Longrightarrow>((Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright>) \<Rightarrow> Post) \<sqsubseteq> (B f)"
  shows "((Pre \<Rightarrow> Post) \<sqsubseteq> fp B)"  
proof -  
   { fix st
    have "((Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post)\<sqsubseteq> (fp B))" 
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

lemma  rec_total_rule_Pure'': 
  assumes WF: "wf R"
  and     M: "mono B"  
  and     induct_step:
          "\<And> f st.  \<lbrakk>(Pre \<and> ($\<Sigma>,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> f\<rbrakk>
               \<Longrightarrow> \<mu> B = f \<Longrightarrow>(Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> (B f)"
        shows "(Pre \<Rightarrow> Post) \<sqsubseteq> \<mu> B"  
  apply (rule wf_fixp_uinduct_Pure'[where fp=\<mu> and Pre=Pre and B=B])    
  using M apply (rule gfp_unfold)    
   apply (rule WF)  
  apply (rule induct_step)
    apply pred_simp
   apply assumption
  done     
  
lemma  rec_total_rule_Pure''': 
  assumes WF: "wf R"
    and     M: "mono B"  
    and     induct_step:
    "\<And>st. (Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> (B ((Pre \<and> ($\<Sigma>,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<Rightarrow> Post)))"
  shows "(Pre \<Rightarrow> Post) \<sqsubseteq> \<mu> B"  
proof -          
  { fix st
    have "((Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post)\<sqsubseteq> (\<mu> B))" 
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
  
  
lemma  rec_total_rule_Pure': 
  assumes WF: "wf R"
  and     M: "mono B"  
  and     induct_step:
          "\<And> f st.  \<lbrakk>\<And>st'. (st',st) \<in>R  \<Longrightarrow> (Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st'\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> f\<rbrakk>
               \<Longrightarrow> \<mu> B = f \<Longrightarrow>(Pre \<and> $\<Sigma> =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> (B f)"
        shows "(Pre \<Rightarrow> Post) \<sqsubseteq> \<mu> B"  
  apply (rule wf_fixp_uinduct_Pure'[where fp=\<mu> and Pre=Pre and B=B])    
  using M apply (rule gfp_unfold)    
   apply (rule WF)  
  apply (rule induct_step)
   apply assumption
    apply assumption
  done     

lemma job_done_going_home_now:
  "vwb_lens x \<Longrightarrow> (\<lceil>true\<rceil>\<^sub><\<Rightarrow> \<lceil>&x \<le>\<^sub>u \<guillemotleft>0::int\<guillemotright>\<rceil>\<^sub>>) \<sqsubseteq> (\<mu> R \<bullet> ((x :== (&x - \<guillemotleft>1\<guillemotright>)) ;; R) \<triangleleft> &x >\<^sub>u \<guillemotleft>0::int\<guillemotright> \<triangleright>\<^sub>r II)"    
  term "\<lbrakk>&x\<rbrakk>\<^sub>e"
  term "measure (nat o \<lbrakk>&x\<rbrakk>\<^sub>e)"
    thm rec_total_rule_Pure
  apply (rule rec_total_rule_Pure''[where R="measure (nat o \<lbrakk>&x\<rbrakk>\<^sub>e)"])  
    apply simp
     apply (simp add: cond_mono monoI seqr_mono)
    
  apply (rule  cond_refine_split')
     prefer 2
     apply (rule skip_refine_XXX)
     apply pred_simp 
     
    subgoal premises prems for f st   
      term "([x\<mapsto>\<^sub>s &x-1] st)"
    (*apply (rule seq_refine_split''[where s="0 \<le>\<^sub>u &x \<and>  subst_upd id\<dagger>(&x =\<^sub>u (&x-1))\<guillemotleft>([x\<mapsto>\<^sub>s &x-1] st)\<guillemotright>"]) *)
    apply (rule seq_refine_split''[where s="0 \<le>\<^sub>u &x \<and> &\<Sigma> =\<^sub>u \<guillemotleft>([x\<mapsto>\<^sub>s &x-1] st)\<guillemotright>"]) 
     apply pred_simp 
      apply pred_simp 
      using prems(1) apply pred_simp 
      apply (rule pre_str[rotated]) 
      apply (rule prems(2))  
      using prems(1) apply pred_simp 
      done
    done
      

lemma job_done_going_home_now_definitely:
  "vwb_lens x \<Longrightarrow> (\<lceil>true\<rceil>\<^sub><\<Rightarrow> \<lceil>&x \<le>\<^sub>u \<guillemotleft>0::int\<guillemotright>\<rceil>\<^sub>>) \<sqsubseteq> (\<mu> R \<bullet> ((x :== (&x - \<guillemotleft>1\<guillemotright>)) ;; R) \<triangleleft> &x >\<^sub>u \<guillemotleft>0::int\<guillemotright> \<triangleright>\<^sub>r II)"    
  term "\<lbrakk>&x\<rbrakk>\<^sub>e"
  term "measure (nat o \<lbrakk>&x\<rbrakk>\<^sub>e)"
  apply (rule rec_total_rule_Pure'''[where R="measure (nat o \<lbrakk>&x\<rbrakk>\<^sub>e)"])  
    apply simp
     apply (simp add: cond_mono monoI seqr_mono)
    
  apply (rule  cond_refine_split')
     prefer 2
     apply (rule skip_refine_XXX)
     apply pred_simp 
    
    subgoal for st   
      term "([x\<mapsto>\<^sub>s &x-1] st)"
    (*apply (rule seq_refine_split''[where s="0 \<le>\<^sub>u &x \<and>  subst_upd id\<dagger>(&x =\<^sub>u (&x-1))\<guillemotleft>([x\<mapsto>\<^sub>s &x-1] st)\<guillemotright>"]) *)
    apply (rule seq_refine_split''[where s="0 \<le>\<^sub>u &x \<and> &\<Sigma> =\<^sub>u \<guillemotleft>([x\<mapsto>\<^sub>s &x-1] st)\<guillemotright>"]) 
     apply pred_simp 
      apply pred_simp 
      apply pred_simp 
      apply pred_simp 
      done
    done


      
      
      
      using 12[of "[]\<^sub>u <\<^sub>u &x"]
      apply (subst 12[of "[]\<^sub>u <\<^sub>u &x"])
      apply (simp only:inf_top_right inf_top_left 11 12)
 
     
    apply (simp)
      
    using seq_refine_split
   apply (rule seq_refine_split)
    
    
  apply (fold foo) 
  apply (rule allI)  
  oops   
  
  
lemma  wf_fixp_uinduct_Pure: 
  assumes fixp_unfold: "fp B = B (fp B)"
  and              WF: "wf R"
  and     induct_step:
          "\<And>f st. \<lbrakk>\<And>st'. (st',st) \<in>R  \<Longrightarrow> ((Pre \<Rightarrow> Post)\<lbrakk>\<guillemotleft>st'\<guillemotright>/ $\<Sigma>\<rbrakk> \<sqsubseteq> f\<lbrakk>\<guillemotleft>st'\<guillemotright>/ $\<Sigma>\<rbrakk>)\<rbrakk>
               \<Longrightarrow> fp B = f \<Longrightarrow>(Pre \<Rightarrow> Post)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk> \<sqsubseteq> (B f)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk>"
  shows "((Pre \<Rightarrow> Post) \<sqsubseteq> fp B)"  
proof -  
   { fix st
    have "((Pre \<Rightarrow> Post)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk> \<sqsubseteq> (fp B)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk>)" 
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
   
lemma  rec_total_rule_Pure: 
  assumes WF: "wf R"
  and     M: "mono B"  
  and     induct_step:
          "\<And> f st.  \<lbrakk>\<And>st'. (st',st) \<in>R  \<Longrightarrow> (Pre \<Rightarrow> Post)\<lbrakk>\<guillemotleft>st'\<guillemotright>/ $\<Sigma>\<rbrakk> \<sqsubseteq> f\<lbrakk>\<guillemotleft>st'\<guillemotright>/ $\<Sigma>\<rbrakk>\<rbrakk>
               \<Longrightarrow> \<mu> B = f \<Longrightarrow>(Pre \<Rightarrow> Post)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk> \<sqsubseteq> (B f)\<lbrakk>\<guillemotleft>st\<guillemotright>/ $\<Sigma>\<rbrakk>"
        shows "(Pre \<Rightarrow> Post) \<sqsubseteq> \<mu> B"  
  apply (rule wf_fixp_uinduct_Pure[where fp=\<mu> and Pre=Pre and B=B])    
  using M apply (rule gfp_unfold)    
   apply (rule WF)  
  apply (rule induct_step)
   apply assumption
    apply assumption
  done  


    
definition while_invT :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sub>\<bottom> _ invr _ do _ od" 71) where
"while\<^sub>\<bottom> b invr p do S od = while\<^sub>\<bottom> b do S od"  


lemma uwhile_total_rule:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`"
  assumes induct_step:"\<And> st. (\<lceil>b \<and> I\<rceil>\<^sub>< \<Rightarrow> \<lceil>I \<and> \<guillemotleft>(st', st) \<in> R\<guillemotright>\<rceil>\<^sub>>) \<sqsubseteq> f"  
  assumes PHI:"`\<not> \<lceil>b\<rceil>\<^sub>< \<and> \<lceil>I\<rceil>\<^sub>< \<Rightarrow> \<lceil>Post\<rceil>\<^sub>>`"  
  shows "\<lbrace>Pre\<rbrace>while\<^sub>\<bottom> b invr I do f od\<lbrace> Post\<rbrace>\<^sub>u"
  unfolding  hoare_r_def while_invT_def while_bot_def
   apply (rule pre_str[of _ "\<lceil>I\<rceil>\<^sub><" ])
  using I0 
   apply pred_simp
    apply (rule rec_total_rule[where Pre="\<lceil>I\<rceil>\<^sub><", OF WF])  
   apply (simp add: cond_mono monoI seqr_mono)
  apply (rule  cond_refine_split)
     prefer 2
   apply (rule skip_refine)
  using PHI
   apply simp
  apply (subst 11)
    subgoal  order_trans for fa st 
  apply (rule_tac seq_refine_split[where s= "I \<and> \<guillemotleft>(st', st) \<in> R\<guillemotright>" ])
   apply (rule order_trans[OF induct_step])
   apply pred_blast
  apply (subst (asm) 11)
    apply blast
done


lemma uwhile_total_rule_Pure:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`"
  assumes induct_step:"\<And> st st'. (\<lceil>b \<and> I\<rceil>\<^sub>< \<Rightarrow> \<lceil>I\<lbrakk>\<guillemotleft>st'\<guillemotright>/&\<Sigma>\<rbrakk> \<and> \<guillemotleft>(st', st) \<in> R\<guillemotright>\<rceil>\<^sub>>) \<sqsubseteq> f\<lbrakk>\<guillemotleft>st'\<guillemotright>/$\<Sigma>\<rbrakk>"  
  assumes PHI:"`\<not> \<lceil>b\<rceil>\<^sub>< \<and> \<lceil>I\<rceil>\<^sub>< \<Rightarrow> \<lceil>Post\<rceil>\<^sub>>`"  
  shows "\<lbrace>Pre\<rbrace>while\<^sub>\<bottom> b invr I do f od\<lbrace> Post\<rbrace>\<^sub>u"
  unfolding  hoare_r_def while_invT_def while_bot_def
  apply (rule 1[of _ "\<lceil>I\<rceil>\<^sub><" ])
  using I0 
   apply pred_simp
        
    apply (rule rec_total_rule_Pure[where Pre="\<lceil>I\<rceil>\<^sub><", OF WF])  
   apply (simp add: cond_mono monoI seqr_mono)
  apply (rule 2)
  prefer 2
   apply (rule 7)
  using PHI
   apply pred_blast 
    apply (subst 11)
  apply (rule_tac s = "I" in 3)
   apply (rule order_trans[OF induct_step])
   prefer 2
    apply (rule order_trans[OF induct_step])
    
  oops
   

end