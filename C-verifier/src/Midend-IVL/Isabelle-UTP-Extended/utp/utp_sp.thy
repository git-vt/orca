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

theory utp_sp
imports "../../Isabelle-UTP/utp/utp_wp"
    
begin

named_theorems slp

method slp_tac = (simp add: slp)

consts
  usp :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infix "slp" 60)

text \<open>Since the definition of strongest post condition  below do not require termination. We name
      it strongest liberal post-condition. Thus we follow Dijkstra terminology.\<close>
  
definition slp_upred :: "'\<alpha> cond \<Rightarrow> ('\<alpha>, '\<beta>) rel \<Rightarrow> '\<beta> cond" where
"slp_upred p Q = \<lfloor>(\<lceil>p\<rceil>\<^sub>> ;; Q) :: ('\<alpha>, '\<beta>) rel\<rfloor>\<^sub>>"

adhoc_overloading
  usp slp_upred

declare slp_upred_def [upred_defs]

lemma slp_false [slp]: "p slp false = false"
  by (rel_simp) 

lemma slp_true [slp]: "q \<noteq> false \<Longrightarrow> q slp true = true"
  by (rel_auto) 
    
lemma slp_is_post_condition:
  "\<lbrace>p\<rbrace>C\<lbrace>p slp C\<rbrace>\<^sub>u"
  by rel_blast
    
lemma slp_is_the_strongest_post:
  "`p slp C \<Rightarrow> Q`\<Longrightarrow>\<lbrace>p\<rbrace>C\<lbrace>Q\<rbrace>\<^sub>u"
  by rel_blast
    
lemma slp_is_the_strongest_post':
  "(Q \<sqsubseteq> p slp C) \<Longrightarrow>\<lbrace>p\<rbrace>C\<lbrace>Q\<rbrace>\<^sub>u"
  by rel_auto
    
lemma hoare_r_slp_eq:
  " \<lbrace>p\<rbrace>C\<lbrace>Q\<rbrace>\<^sub>u = `p slp C \<Rightarrow> Q` "
  by rel_blast
    
theorem hoare_r_slp_eq':
  "\<lbrace>p\<rbrace>Q\<lbrace>q\<rbrace>\<^sub>u \<longleftrightarrow> (q \<sqsubseteq> p slp Q)"
  by rel_auto                               
     
theorem slp_eq_intro: 
  "\<lbrakk>\<And>r. r slp P = r slp Q\<rbrakk> \<Longrightarrow> P = Q"
  by (rel_auto robust, fastforce+)  
    
lemma wlp_slp_sym:
  "`prog wp (true slp prog)`"
  by rel_auto
     
lemma slp_is_pre_condition:
  "\<lbrace>C wp Q\<rbrace>C\<lbrace>Q\<rbrace>\<^sub>u"
  by rel_blast    

lemma wlp_is_the_weakest_pre:
  "`P \<Rightarrow> C wp Q` \<Longrightarrow> \<lbrace>P\<rbrace>C\<lbrace>Q\<rbrace>\<^sub>u"
  by rel_blast  
    
lemma wlp_is_the_weakest_pre':
  "(C wp Q) \<sqsubseteq> P \<Longrightarrow> \<lbrace>P\<rbrace>C\<lbrace>Q\<rbrace>\<^sub>u"
  by rel_blast 
    
lemma hoare_r_wlp_eq:
  "\<lbrace>P\<rbrace>C\<lbrace>Q\<rbrace>\<^sub>u = `P \<Rightarrow> C wp Q`"
  by rel_blast
 
lemma skip_r_slp:
  "P slp SKIP\<^sub>r = P"
  by rel_simp

lemma skip_r_wlp:
  "SKIP\<^sub>r wp Q = Q"
  by rel_simp
    
lemma assigns_r_slp[slp]: 
  "vwb_lens x \<Longrightarrow> (p slp x :== e ) = (\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>)"
  apply (rel_simp) 
    apply transfer
  apply auto
   apply (rule_tac x = \<open>get\<^bsub>x\<^esub> y\<close> in exI)
    apply simp
  apply (metis vwb_lens.put_eq)
  done  
 
lemma assigns_r_wlp[wp]:
  "(\<langle>\<sigma>\<rangle>\<^sub>a wp Q) = (\<sigma> \<dagger> Q)"
  by rel_simp
 
lemma seq_r_slp[slp]:
  " P slp (S\<^sub>1 ;; S\<^sub>2) = (P slp S\<^sub>1) slp S\<^sub>2"
  by rel_auto

lemma seq_r_wlp[wp]:
  "(S\<^sub>1 ;; S\<^sub>2) wp Q = S\<^sub>1 wp (S\<^sub>2 wp Q)"
  by rel_auto 
    
lemma If_r_slp[slp]:
  "P slp (bif b then S\<^sub>1 else S\<^sub>2 eif) = (((P \<and> b) slp S\<^sub>1) \<or> ((P \<and> \<not>b) slp S\<^sub>2))"
  by rel_auto

lemma If_r_wlp[wp]:
  "(bif b then S\<^sub>1 else S\<^sub>2 eif) wp Q = ((S\<^sub>1 wp Q \<and> b)\<or> (S\<^sub>2 wp Q \<and> \<not>b))"
  by rel_auto
    
lemma while_gfp_rel_slp [slp]:
  "P slp (while\<^sup>\<top> b do body od) = ((((P \<and> b) slp body) slp (while\<^sup>\<top> b do body od)) \<or> (P \<and> \<not>b))"
  apply (subst while_gfp_rel_unfold)
  apply rel_auto
  done

lemma while_gfp_rel_wlp[wp]:
  "(while\<^sup>\<top> b do body od) wp Q = ((body wp ((while\<^sup>\<top> b do body od)  wp Q) \<and> b) \<or> (Q \<and> \<not>b))"
  apply (subst while_gfp_rel_unfold)
  apply rel_auto
  done
    
lemma gfp_rel_slp [slp]:
  "mono F \<Longrightarrow> P slp \<nu> F =  P slp F(\<nu> F)"
  apply (subst lfp_unfold)
   apply simp_all
  done
    
lemma gfp_rel_wlp [wp]:
  "mono F \<Longrightarrow> P slp \<nu> F =  P slp F(\<nu> F)"
  apply (subst lfp_unfold)
   apply simp_all
  done
end  
  

