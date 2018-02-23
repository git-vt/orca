(******************************************************************************
 * Orca: A Functional Correctness Verifier for Imperative Programs
 *       Based on Isabelle/UTP
 *
 * Copyright (c) 2016-2018 Virginia Tech, USA
 *               2016-2018 Technische Universität München, Germany
 *               2016-2018 University of York, UK
 *               2016-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * This software may be distributed and modified according to the terms of
 * the GNU Lesser General Public License version 3.0 or any later version.
 * Note that NO WARRANTY is provided.
 *
 * See CONTRIBUTORS, LICENSE and CITATION files for details.
 ******************************************************************************)

theory utp_rec_total
  imports  "../AlgebraicLaws/Algebraic_Laws"
begin
text {*The following lemma explains the intuition behind lifting operators from predicates to relations.
       While in relational setting both, input and output state are evaluated. A predicate
       evaluate only on a single state. To unify predicates and relations such a lifting is necessary.
       This gives a way to express Hoare logic in relational calculus.*}
  
lemma "\<lbrakk>\<lceil>p\<rceil>\<^sub><\<Rightarrow> \<lceil>q\<rceil>\<^sub>>\<rbrakk>\<^sub>e (s,s') = (\<lbrakk>\<lceil>p\<rceil>\<^sub><\<rbrakk>\<^sub>e(s,UNIV) \<longrightarrow> \<lbrakk>\<lceil>q\<rceil>\<^sub>>\<rbrakk>\<^sub>e (UNIV, s'))"
  by rel_auto
    
section {*Noetherian induction instantiation*}
      
(*The following generalization was used by Tobias Nipkow in .. and Peter Lammich  in Refine_Monadic*)

lemma  wf_fixp_uinduct_pure_ueq_gen:     
  assumes fixp_unfold: "fp F = F (fp F)"
  and              WF: "wf R"
  and     induct_step:
          "\<And>f st. \<lbrakk>\<And>st'. (st',st) \<in>R  \<Longrightarrow> (\<lceil>p \<and> e =\<^sub>u \<guillemotleft>st'\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> f\<rbrakk>
               \<Longrightarrow> fp F = f \<Longrightarrow>(\<lceil>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> (F f)"
        shows "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> fp F"  
 proof -  
   { fix st
    have "(\<lceil>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> (fp F)" 
      using WF
      apply (induction rule: wf_induct_rule)  
      apply (subst fixp_unfold)  
      apply (rule induct_step)  
      apply blast
      apply simp  
      done  
     }
    thus ?thesis 
    by pred_simp  
qed
  
text {*The next lemma shows that using substitution also work. However it is not that generic
       nor practical for proof automation ...*}

lemma refine_usubst_to_ueq:
  "vwb_lens e \<Longrightarrow>(p \<Rightarrow> q)\<lbrakk>\<guillemotleft>st'\<guillemotright>/$e\<rbrakk> \<sqsubseteq> f\<lbrakk>\<guillemotleft>st'\<guillemotright>/$e\<rbrakk> = (((p \<and> $e =\<^sub>u \<guillemotleft>st'\<guillemotright>) \<Rightarrow> q) \<sqsubseteq> f)"
  apply rel_auto
  apply (metis vwb_lens_wb wb_lens.get_put)
done  

text {*By instantiation of @{thm wf_fixp_uinduct_pure_ueq_gen} with @{term \<mu>}and lifting of the 
       well-founded relation we have ...*}
  
lemma  mu_rec_total_pure_rule: 
  assumes WF: "wf R"
    and     M: "mono F"  
    and     induct_step:
    "\<And> f st. \<lbrakk>(\<lceil>p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> f\<rbrakk> \<Longrightarrow> \<mu> F = f \<Longrightarrow>(\<lceil>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> (F f)"
  shows "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> \<mu> F"          
proof (induction rule:  wf_fixp_uinduct_pure_ueq_gen[where fp=\<mu> and p=p and F=F and e = e and R = R])
  case 1
  then show ?case using M by (rule gfp_unfold)    
next
  case 2
  then show ?case using WF .
next
  case (3 f st) 
  then show ?case 
    apply hypsubst  
    apply (rule induct_step) 
     apply pred_simp+  
    done
qed


text {*Since @{term "F (p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<Rightarrow> q) \<sqsubseteq> F (\<mu> F)"} and 
      @{term "mono F"}, thus,  @{thm mu_rec_total_pure_rule} can be expressed as follows*}
  
lemma mu_rec_total_utp_rule: 
  assumes           WF: "wf R"
  assumes            M: "mono F"  
  assumes  induct_step:
    "\<And>st. (\<lceil>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> F (\<lceil>p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>)"
  shows "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> \<mu> F"  
proof -          
  { fix st
    have "(\<lceil>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>)\<sqsubseteq> (\<mu> F)" 
      using WF
    proof (induction rule: wf_induct_rule)
      case (less x)
      hence 0:"(\<lceil>p \<and> (e,\<guillemotleft>x\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rceil>\<^sub>< \<Rightarrow>\<lceil>q\<rceil>\<^sub>>)\<sqsubseteq> (\<mu> F)" 
        by rel_blast
      hence 1: "F (\<lceil>p \<and> (e,\<guillemotleft>x\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>)\<sqsubseteq> F(\<mu> F)" 
        by (rule monoD[OF M])
      have 2: "(\<lceil>p \<and> e =\<^sub>u \<guillemotleft>x\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> ..."
        by (simp add: induct_step)
      then show ?case
        using order_trans [OF 1 2]
      proof (subst gfp_unfold[OF M], goal_cases)
        case 1
        assume 01:"(\<lceil>p \<and> e =\<^sub>u \<guillemotleft>x\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> F (\<lceil>p \<and> (e,\<guillemotleft>x\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>)"
        assume 02:"(\<lceil>p \<and> e =\<^sub>u \<guillemotleft>x\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> F (\<mu> F)"  
        show ?case using 01 02 
          by simp    
      qed 
        
    qed   
  }
  thus ?thesis
    by pred_simp
qed            

lemma nu_rec_total_utp_rule: 
  assumes           WF: "wf R"
  assumes            M: "mono F"  
  assumes  induct_step:
    "\<And>st. (\<lceil>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> F (\<lceil>p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>)"
  shows "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> \<nu> F"  
proof -          
  { fix st
    have "(\<lceil>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>)\<sqsubseteq> (\<nu> F)" 
      using WF
    proof (induction rule: wf_induct_rule)
      case (less x)
      hence 0:"(\<lceil>p \<and> (e,\<guillemotleft>x\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rceil>\<^sub>< \<Rightarrow>\<lceil>q\<rceil>\<^sub>>)\<sqsubseteq> (\<nu> F)" 
        by rel_blast
      hence 1: "F (\<lceil>p \<and> (e,\<guillemotleft>x\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>)\<sqsubseteq> F(\<nu> F)" 
        by (rule monoD[OF M])
      have 2: "(\<lceil>p \<and> e =\<^sub>u \<guillemotleft>x\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> ..."
        by (simp add: induct_step)
      then show ?case
        using order_trans [OF 1 2]
      proof (subst lfp_unfold[OF M], goal_cases)
        case 1
        assume 01:"(\<lceil>p \<and> e =\<^sub>u \<guillemotleft>x\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> F (\<lceil>p \<and> (e,\<guillemotleft>x\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>)"
        assume 02:"(\<lceil>p \<and> e =\<^sub>u \<guillemotleft>x\<guillemotright>\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> F (\<nu> F)"  
        show ?case using 01 02 
          by simp    
      qed 
        
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
  apply (rule mu_rec_total_utp_rule[where R="measure (nat o \<lbrakk>&x\<rbrakk>\<^sub>e)"and e = "&\<Sigma>"]) 
    apply simp
     apply (simp add: cond_mono monoI seqr_mono)
  apply (rule  cond_refine_rel)
     prefer 2
     apply pred_simp+      
  done
 
lemma total_rec_test:
  "vwb_lens x \<Longrightarrow> 
   (\<lceil>true\<rceil>\<^sub><\<Rightarrow> \<lceil>&x \<le>\<^sub>u \<guillemotleft>0::int\<guillemotright>\<rceil>\<^sub>>) \<sqsubseteq> (\<mu> R \<bullet> ((x :== (&x - \<guillemotleft>1\<guillemotright>)) ;; R) \<triangleleft> &x >\<^sub>u \<guillemotleft>0::int\<guillemotright> \<triangleright>\<^sub>r II)"    
  apply (rule mu_rec_total_pure_rule[where R="measure (nat o \<lbrakk>&x\<rbrakk>\<^sub>e)" and e = "&\<Sigma>"])  
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

