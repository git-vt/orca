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
  
section {*Examples*}

(*The lemma total_rec_utp_test shows how rec_total_utp_rule improves automation wrt
  rec_total_pure_rule which was used for the same example in  total_rec_test*)  
lemma total_rec_utp_test:
  "vwb_lens x \<Longrightarrow> 
   (\<lceil>true\<rceil>\<^sub><\<Rightarrow> \<lceil>&x \<le>\<^sub>u \<guillemotleft>0::int\<guillemotright>\<rceil>\<^sub>>) \<sqsubseteq> (\<mu> R \<bullet> ((x :== (&x - \<guillemotleft>1\<guillemotright>)) ;; R) \<triangleleft> &x >\<^sub>u \<guillemotleft>0::int\<guillemotright> \<triangleright>\<^sub>r II)"
  apply (rule mu_rec_total_utp_rule[where R="measure (nat o \<lbrakk>&x\<rbrakk>\<^sub>e)"and e = "&\<^bold>v"]) 
    apply simp
   apply (simp add: cond_mono monoI seqr_mono)
  apply (rule  cond_refine_rel)
   prefer 2
   apply pred_simp+      
  done
    
lemma total_rec_test:
  assumes "vwb_lens x"
  shows "(\<lceil>true\<rceil>\<^sub><\<Rightarrow> \<lceil>&x \<le>\<^sub>u \<guillemotleft>0::int\<guillemotright>\<rceil>\<^sub>>) \<sqsubseteq> (\<mu> R \<bullet> ((x :== (&x - \<guillemotleft>1\<guillemotright>)) ;; R) \<triangleleft> &x >\<^sub>u \<guillemotleft>0::int\<guillemotright> \<triangleright>\<^sub>r II)"    
  apply (rule mu_rec_total_pure_rule[where R="measure (nat o \<lbrakk>&x\<rbrakk>\<^sub>e)" and e = "&\<^bold>v"])  
    apply simp
   apply (simp add: cond_mono monoI seqr_mono)   
  apply (rule  cond_refine_rel)
   prefer 2
   apply pred_simp      
  subgoal premises prems for f st   
    using assms apply (rel_simp)
    oops (* Couldn't managed to fix this example yet *)
(*
    apply (rule seq_refine_unrest)
    apply (rule seq_refine_unrest[where s="0 \<le>\<^sub>u &x \<and> &\<^bold>v =\<^sub>u \<guillemotleft>([x\<mapsto>\<^sub>s &x-1] st)\<guillemotright>"]) 
       apply pred_simp 
      apply pred_simp 
    using prems(1) apply pred_simp 
    apply (rule pre_weak_rel[rotated]) 
     apply (rule prems(2))  
    using prems(1) apply pred_simp 
    done
  done
*)  

end

