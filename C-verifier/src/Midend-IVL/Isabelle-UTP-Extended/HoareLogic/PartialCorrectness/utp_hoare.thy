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

subsection {* Relational Hoare calculus *}

theory utp_hoare
imports "../../utp/utp_rec_total"
begin

named_theorems hoare_sp_rules and hoare_wp_rules and hoare_wp_proof_annotation_rules

subsection {*Hoare triple definition*}


definition hoare_r :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>u") where
"\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u = ((\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>r\<rceil>\<^sub>>) \<sqsubseteq> Q)"

declare hoare_r_def[upred_defs]
lemma hoare_true_assisgns_prog_t: 
  "\<lbrace>p\<rbrace> \<langle>\<sigma>\<rangle>\<^sub>a \<lbrace>true\<rbrace>\<^sub>u"
  by rel_simp

lemma skip_true_hoare_rel: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>r\<lbrace>true\<rbrace>\<^sub>u"
   by rel_simp

lemma pre_false_hoare_rel: 
  "\<lbrace>false\<rbrace>C\<lbrace>q\<rbrace>\<^sub>u"
  by rel_simp

subsection {*Precondition weakening*}

lemma pre_str_hoare_rel:
  assumes "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" and "\<lbrace>p\<^sub>2\<rbrace>C\<lbrace>q\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<^sub>1\<rbrace>C\<lbrace>q\<rbrace>\<^sub>u" 
  using assms  
  by rel_simp
    
subsection {*Post-condition strengthening*}
  
lemma post_weak_hoare_rel:
  assumes "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>2\<rbrace>\<^sub>u" and "`q\<^sub>2 \<Rightarrow> q\<^sub>1`"
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>1\<rbrace>\<^sub>u" 
  using assms  
  by rel_simp
    
subsection {*Consequence rule*}  
  
lemma consequence_hoare_rel:
  assumes I0': "`p \<Rightarrow> p'`" 
  assumes induct_step:"\<lbrace>p'\<rbrace> C \<lbrace>q'\<rbrace>\<^sub>u" 
  assumes I0 :"`q'\<Rightarrow> q`"  
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<rbrace>\<^sub>u"
proof(rule post_weak_hoare_rel[OF _ I0], goal_cases)
  case 1
  then show ?case by (rule pre_str_hoare_rel[OF I0' induct_step]) 
qed   
  
subsection {*Hoare and assertion logic*}

lemma conj_hoare_rel: 
  assumes"\<lbrace>p\<rbrace>C\<lbrace>r\<rbrace>\<^sub>u" and "\<lbrace>p\<rbrace>C\<lbrace>s\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>C\<lbrace>r \<and> s\<rbrace>\<^sub>u"
  using assms  
  by rel_simp
    
subsection {*Hoare SKIP*}

lemma skip_rel_hoare_rel[hoare_sp_rules, hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>r\<lbrace>p\<rbrace>\<^sub>u"
  by rel_simp
    
lemma skip_rel_hoare_rel_intro: 
  "`p \<Rightarrow> q`\<Longrightarrow>\<lbrace>p\<rbrace>SKIP\<^sub>r\<lbrace>q\<rbrace>\<^sub>u"
  by rel_simp
  
subsection {*Hoare for assignment*}

lemma assigns_rel_hoare_rel_intro: 
  assumes"`p \<Rightarrow> \<sigma> \<dagger> q`" 
  shows  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>a\<lbrace>q\<rbrace>\<^sub>u"
  using assms  
  by rel_simp
    
lemma assigns_rel_backward_hoare_rel[hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  "\<lbrace>\<sigma> \<dagger> p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>a\<lbrace>p\<rbrace>\<^sub>u"
  by rel_simp
    
lemma assigns_rel_floyd_hoare_rel[hoare_sp_rules]:
  assumes "vwb_lens x"
  shows \<open>\<lbrace>p\<rbrace>x :== e\<lbrace>\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrace>\<^sub>u\<close>
  using assms
  apply rel_simp   
  subgoal for a    
    apply (rule exI[where x = "lens_get x a"])
    apply simp
    done
  done    

subsection {*Hoare for Sequential Composition*}

lemma seq_invariant_hoare_rel: 
 "\<lbrakk>\<lbrace>p\<rbrace>Q\<^sub>1\<lbrace>p\<rbrace>\<^sub>u ; \<lbrace>p\<rbrace>Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>u\<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>u"
  by rel_simp 
    
lemma seq_stronger_pre_1_hoare_rel: 
  "\<lbrakk> \<lbrace>p \<and> q\<rbrace>Q\<^sub>1\<lbrace>p \<and> q\<rbrace>\<^sub>u ; \<lbrace>p \<and> q\<rbrace>Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrace>p \<and> q\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>u"
  by rel_simp

lemma seq_stronger_pre_2_hoare_rel: 
  "\<lbrakk> \<lbrace>p \<and> q\<rbrace>Q\<^sub>1\<lbrace>p \<and> q\<rbrace>\<^sub>u ; \<lbrace>p \<and> q\<rbrace>Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>u\<rbrakk> \<Longrightarrow> \<lbrace>p \<and> q\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>u"
  by rel_simp
    
lemma seq_hoare_rel[hoare_wp_rules, hoare_sp_rules]: 
  assumes"\<lbrace>p\<rbrace>C\<^sub>1\<lbrace>s\<rbrace>\<^sub>u" and "\<lbrace>s\<rbrace>C\<^sub>2\<lbrace>r\<rbrace>\<^sub>u" 
  shows"\<lbrace>p\<rbrace>C\<^sub>1 ;; C\<^sub>2\<lbrace>r\<rbrace>\<^sub>u"
  using assms
  by rel_simp
    
subsection {*Hoare for Conditional*}

lemma cond_rel_hoare_rel: 
  assumes "\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>u" and "\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace> bif b then C\<^sub>1 else C\<^sub>2 eif\<lbrace>q\<rbrace>\<^sub>u"
  using assms
  by pred_simp
    
lemma cond_rel_hoare_rel_wp[hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  assumes "\<lbrace>p'\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>u" and "\<lbrace>p''\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>u"
  shows "\<lbrace>(b \<and> p')\<or> (\<not>b \<and> p'')\<rbrace>bif b then C\<^sub>1 else C\<^sub>2 eif\<lbrace>q\<rbrace>\<^sub>u"
  using assms
  by pred_simp
    
lemma cond_rel_hoare_rel_sp[hoare_sp_rules]:
  assumes \<open>\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>u\<close> and \<open>\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>s\<rbrace>\<^sub>u\<close>
  shows \<open>\<lbrace>p\<rbrace>bif b then C\<^sub>1 else C\<^sub>2 eif\<lbrace>q \<or> s\<rbrace>\<^sub>u\<close>
  using assms
  by pred_simp
    
subsection {*Hoare for recursion*}
  
lemma nu_rel_hoare_rel_partial: 
  assumes induct_step:
    "\<And> st P. \<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>p\<rbrace>F P\<lbrace>q\<rbrace>\<^sub>u"   
  shows "\<lbrace>p\<rbrace>\<nu> F \<lbrace>q\<rbrace>\<^sub>u"  
  unfolding hoare_r_def
  apply (rule lfp_lowerbound)
    apply (rule induct_step[unfolded hoare_r_def])
    apply simp
  done    
  
lemma mu_rel_hoare_rel:
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<And> st P. \<lbrace>p \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>P\<lbrace>q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>F P\<lbrace>q\<rbrace>\<^sub>u"   
  shows "\<lbrace>p\<rbrace>\<mu> F \<lbrace>q\<rbrace>\<^sub>u"  
  unfolding hoare_r_def
proof (rule mu_rec_total_utp_rule[OF WF M , of _ e ], goal_cases)
  case (1 st)
  then show ?case 
  by (rule induct_step[unfolded hoare_r_def], simp)    
qed
    
lemma mu_rel_hoare_rel':
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<And> st P. \<lbrace>p \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace> P \<lbrace>q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> F P \<lbrace>q\<rbrace>\<^sub>u" 
  assumes I0: "`p' \<Rightarrow> p`"  
  shows "\<lbrace>p'\<rbrace>\<mu> F \<lbrace>q\<rbrace>\<^sub>u"
  by (simp add: pre_str_hoare_rel[OF I0 mu_rel_hoare_rel[OF WF M induct_step]])

subsection {*Hoare for frames*}
  
lemma antiframe_hoare_rel:
  assumes "vwb_lens a"
  assumes "a \<sharp> r" 
  assumes "a \<natural> q"    
  assumes "\<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>u"  
  shows "\<lbrace>p \<and> r\<rbrace>a:[P]\<lbrace>q \<and> r\<rbrace>\<^sub>u"
  using assms
  by rel_simp  
  
lemma antiframe_hoar_rel_stronger:
  assumes "vwb_lens a"
  assumes "a \<sharp> r" 
  assumes "a \<natural> q"    
  assumes "\<lbrace>p \<and> r\<rbrace>P\<lbrace>q\<rbrace>\<^sub>u"  
  shows "\<lbrace>p \<and> r\<rbrace>a:[P]\<lbrace>q \<and> r\<rbrace>\<^sub>u"
  using assms
  by rel_simp
    
lemma frame_hoare_rel:
  assumes "vwb_lens a"
  assumes "a \<natural> r" 
  assumes "a \<sharp> q"    
  assumes "\<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>u"  
  shows "\<lbrace>p \<and> r\<rbrace> a:\<lbrakk>P\<rbrakk> \<lbrace>q \<and> r\<rbrace>\<^sub>u"
  using assms
  by rel_simp
    
lemma frame_hoare_rel_stronger:
  assumes "vwb_lens a"
  assumes "a \<natural> r" 
  assumes "a \<sharp> q"    
  assumes "\<lbrace>p \<and> r\<rbrace>P\<lbrace>q\<rbrace>\<^sub>u"  
  shows "\<lbrace>p \<and> r\<rbrace> a:\<lbrakk>P\<rbrakk> \<lbrace>q \<and> r\<rbrace>\<^sub>u"
  using assms 
  by rel_simp
    
lemma blah1: 
  assumes "vwb_lens g'" "vwb_lens l"
  assumes  "l \<bowtie> g'" 
  shows "vwb_lens  (g' +\<^sub>L l)" 
  using assms 
  by (simp add: lens_indep_sym plus_vwb_lens) 
   
lemma
  assumes 1:"vwb_lens g" 
  assumes 2:"vwb_lens g'" 
  assumes 3:"vwb_lens l"
  assumes 4:"l \<bowtie> g" 
  assumes 8:"g' \<subseteq>\<^sub>L g"
  assumes 5:"{&g', &l}:[C] = C" 
  assumes 6:"\<lbrace>p\<rbrace>C\<lbrace>q\<rbrace>\<^sub>u"
  assumes 7:"`r \<Rightarrow> p`"     
  shows "\<lbrace>r\<rbrace> l:\<lbrakk>C\<rbrakk> \<lbrace>(\<exists> l \<bullet> q) \<and> (\<exists>g' \<bullet> r)\<rbrace>\<^sub>u"
  using 1 2 3 4 5 6 7 unfolding lens_indep_def
  apply rel_auto 
   apply (metis (no_types, lifting) vwb_lens_wb wb_lens.get_put)
  apply (rule_tac x="get\<^bsub> g'\<^esub> a" in exI) using 8 4
proof -
  fix a :: 'b and x :: 'b
  assume a1: "\<lbrakk>r\<rbrakk>\<^sub>e a"
  assume a2: "\<forall>\<sigma> v u. put\<^bsub>l\<^esub> (put\<^bsub>g\<^esub> \<sigma> v) u = put\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> \<sigma> u) v"
  assume a3: "vwb_lens g"
  assume a4: "\<lbrakk>C\<rbrakk>\<^sub>e (a, x)"
  assume a5: "\<forall>a b. (\<exists>x. \<lbrakk>C\<rbrakk>\<^sub>e (a, x) \<and> b = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> x)) (get\<^bsub>g'\<^esub> x)) = \<lbrakk>C\<rbrakk>\<^sub>e (a, b)"
  assume a6: "vwb_lens l"
  assume a7: "\<forall>\<sigma> u. get\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> \<sigma> u) = get\<^bsub>g\<^esub> \<sigma>"
  assume a8: "vwb_lens g'"
  have f9: "\<forall>l la b c a. \<not> mwb_lens l \<or> \<not> la \<subseteq>\<^sub>L l \<or> put\<^bsub>l\<^esub> (put\<^bsub>la\<^esub> (b::'b) (c::'c)) (a::'a) = put\<^bsub>l\<^esub> b a"
    by (meson sublens_put_put)
  have "mwb_lens g"
    using a3 vwb_lens_mwb by blast
  then have f10: "put\<^bsub>g\<^esub> (put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> (v2_0 x a))) (get\<^bsub>g'\<^esub> (v2_0 x a))) (get\<^bsub>g\<^esub> x) = put\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> (v2_0 x a))) (get\<^bsub>g\<^esub> x)"
    using f9 by (metis "8") (* > 1.0 s, timed out *)
  obtain bb :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" where
    "\<forall>x0 x1. (\<exists>v2. \<lbrakk>C\<rbrakk>\<^sub>e (x1, v2) \<and> x0 = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x1 (get\<^bsub>l\<^esub> v2)) (get\<^bsub>g'\<^esub> v2)) = (\<lbrakk>C\<rbrakk>\<^sub>e (x1, bb x0 x1) \<and> x0 = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x1 (get\<^bsub>l\<^esub> (bb x0 x1))) (get\<^bsub>g'\<^esub> (bb x0 x1)))"
    by moura
  then have f11: "\<lbrakk>C\<rbrakk>\<^sub>e (a, bb x a) \<and> x = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> (bb x a))) (get\<^bsub>g'\<^esub> (bb x a))"
    using a5 a4 by presburger
  have "mwb_lens g"
    using a3 vwb_lens_mwb by blast
  then have f12: "put\<^bsub>g\<^esub> (put\<^bsub>g'\<^esub> a (get\<^bsub>g'\<^esub> (bb x a))) (get\<^bsub>g\<^esub> x) = put\<^bsub>g\<^esub> a (get\<^bsub>g\<^esub> x)"
    using f9 by (metis "8")
  have f13: "\<forall>l la b c. \<not> vwb_lens l \<or> \<not> la \<subseteq>\<^sub>L l \<or> get\<^bsub>l\<^esub> (put\<^bsub>la\<^esub> (b::'b) (c::'c)) = put\<^bsub>la /\<^sub>L l\<^esub> (get\<^bsub>l\<^esub> b::'a) c"
    by (simp add: lens_get_put_quasi_commute)
  then have f14: "get\<^bsub>g\<^esub> (put\<^bsub>g'\<^esub> a (get\<^bsub>g'\<^esub> (bb x a))) = put\<^bsub>g' /\<^sub>L g\<^esub> (get\<^bsub>g\<^esub> a) (get\<^bsub>g'\<^esub> (bb x a))"
    using a3 "8" by fastforce 
  have "get\<^bsub>g\<^esub> (put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> (bb x a))) (get\<^bsub>g'\<^esub> (bb x a))) = put\<^bsub>g' /\<^sub>L g\<^esub> (get\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> (bb x a)))) (get\<^bsub>g'\<^esub> (bb x a))"
    using a3 f13 "8" by fastforce 
  then show "\<lbrakk>r\<rbrakk>\<^sub>e (put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x (get\<^bsub>l\<^esub> a)) (get\<^bsub>g'\<^esub> a))"
    using f14 f12 f11 f10 a8 a7 a6 a3 a2 a1
  proof -
    have "\<forall>l la b c a. \<not> mwb_lens l \<or> \<not> la \<subseteq>\<^sub>L l \<or> put\<^bsub>l\<^esub> (put\<^bsub>la\<^esub> (b::'b) (c::'c)) (a::'a) = put\<^bsub>l\<^esub> b a"
      by (meson sublens_put_put)
    then have "put\<^bsub>g\<^esub> (put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> (bb x a))) (get\<^bsub>g'\<^esub> (bb x a))) (put\<^bsub>g' /\<^sub>L g\<^esub> (get\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> (bb x a)))) (get\<^bsub>g'\<^esub> (bb x a))) = put\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> (bb x a))) (put\<^bsub>g' /\<^sub>L g\<^esub> (get\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> (bb x a)))) (get\<^bsub>g'\<^esub> (bb x a)))"
      by (metis "8" \<open>mwb_lens g\<close>) 
    then show ?thesis
      by (metis (no_types) \<open>get\<^bsub>g\<^esub> (put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> (bb x a))) (get\<^bsub>g'\<^esub> (bb x a))) = put\<^bsub>g' /\<^sub>L g\<^esub> (get\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> (bb x a)))) (get\<^bsub>g'\<^esub> (bb x a))\<close> a1 a2 a3 a6 a7 a8 f11 f12 f14 vwb_lens.put_eq vwb_lens_wb wb_lens.get_put)
  qed
qed

subsection {*Hoare for while loop*} 
  
lemma if_rel_mono:
  "mono (\<lambda>X. bif b then P ;; X else Q eif)"
  by (auto intro: monoI seqr_mono cond_mono) 


lemma while_gfp_hoare_rel_minimal_partial:
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<lbrace>invar\<and> b\<rbrace> C \<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top> b do C od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding while_gfp_rel_def_alt
  apply (rule pre_str_hoare_rel[OF seq_step])   
  apply (rule nu_rel_hoare_rel_partial)
  apply (rule cond_rel_hoare_rel)  
   apply (rule seq_hoare_rel[where s="invar"])
  subgoal for st P
    using pre_str_hoare_rel induct_step seq_step
    unfolding hoare_r_def
    apply pred_simp
    done
  subgoal for st P
    apply assumption
    done
  subgoal for st P
    apply pred_simp
    done
  done          

lemma while_gfp_invr_hoare_rel_minimal_partial:
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<lbrace>invar\<and> b\<rbrace> C \<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>p\<rbrace>invr invar while\<^sup>\<top> b do C od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding while_gfp_invr_rel_def 
  by (auto intro!: assms while_gfp_hoare_rel_minimal_partial)
    
lemma while_gfp_rel_consequence_partial:
  assumes seq_step: "`p\<Rightarrow>invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "` invar \<and> b  \<Rightarrow> p'`"
  assumes induct_step: "\<lbrace>p'\<rbrace>C \<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top> b do C od\<lbrace>q\<rbrace>\<^sub>u"
  by (rule consequence_hoare_rel[OF seq_step _ PHI, 
                                 OF while_gfp_hoare_rel_minimal_partial[OF uimp_refl],
                                 OF consequence_hoare_rel[OF I0' induct_step I0]])

lemma while_gfp_invr_rel_consequence_partial:
  assumes seq_step: "`p\<Rightarrow>invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "` invar \<and> b  \<Rightarrow> p'`"
  assumes induct_step: "\<lbrace>p'\<rbrace>C \<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>invr invar while\<^sup>\<top> b do C od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding while_gfp_invr_rel_def 
  by (auto intro!: assms while_gfp_rel_consequence_partial)  

lemma while_gfp_rel_wp_partial:
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "`invar \<and> b \<Rightarrow> p'`"
  assumes induct_step: "\<lbrace>p'\<rbrace>C \<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>invar\<rbrace>while\<^sup>\<top> b do C od\<lbrace>q\<rbrace>\<^sub>u"
  by (rule consequence_hoare_rel[OF uimp_refl _ PHI, 
                                 OF while_gfp_hoare_rel_minimal_partial[OF uimp_refl],
                                 OF consequence_hoare_rel[OF I0' induct_step uimp_refl]])    

lemma while_gfp_invr_rel_wp_partial:
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "`invar \<and> b \<Rightarrow> p'`"
  assumes induct_step: "\<lbrace>p'\<rbrace>C \<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>invar\<rbrace>invr invar while\<^sup>\<top> b do C od\<lbrace>q\<rbrace>\<^sub>u"                             
  unfolding while_gfp_invr_rel_def 
  by (auto intro!: assms while_gfp_rel_consequence_partial)  
                           
lemma while_gfp_rel_sp_partial:
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<lbrace>invar \<and> b\<rbrace>C \<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top> b do C od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  by (rule consequence_hoare_rel[OF seq_step _ uimp_refl, 
                                 OF while_gfp_hoare_rel_minimal_partial[OF uimp_refl],
                                 OF consequence_hoare_rel[OF uimp_refl induct_step I0]])

lemma while_gfp_invr_rel_sp_partial:
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<lbrace>invar \<and> b\<rbrace>C \<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>invr invar while\<^sup>\<top> b do C od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding while_gfp_invr_rel_def 
  by (rule consequence_hoare_rel[OF seq_step _ uimp_refl, 
                                 OF while_gfp_hoare_rel_minimal_partial[OF uimp_refl],
                                 OF consequence_hoare_rel[OF uimp_refl induct_step I0]])
                             
(*TODO:Partial correctness rules for the other rules*)
                             
lemma while_lfp_hoare_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`" 
  assumes induct_step:"\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"    
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom> b do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding while_lfp_rel_def_alt
proof (rule pre_str_hoare_rel[OF seq_step mu_rel_hoare_rel[OF WF if_rel_mono cond_rel_hoare_rel, of _ e]], goal_cases)
  case (1 st X)
  assume *: "\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>X\<lbrace>\<not> b \<and> invar\<rbrace>\<^sub>u"  
  show ?case 
  proof (rule seq_hoare_rel [of _ _ "invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>"], goal_cases)
    case 1
    then show ?case by (rule induct_step)
  next
    case 2
    then show ?case by (rule *) 
  qed 
next
  case (2 st X)
  then show ?case by rel_simp 
qed
    
lemma while_lfp_invr_hoare_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`" 
  assumes induct_step:"\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"    
  shows "\<lbrace>p\<rbrace>invr invar while\<^sub>\<bottom> b do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding while_lfp_invr_rel_def
  using assms while_lfp_hoare_rel_minimal
  by blast  

lemma while_lfp_invr_vrt_hoare_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`" 
  assumes induct_step:"\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"    
  shows "\<lbrace>p\<rbrace>invr invar vrt \<guillemotleft>R\<guillemotright> while\<^sub>\<bottom> b do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding while_lfp_invr_vrt_rel_def
  using assms while_lfp_hoare_rel_minimal
  by blast  
    
lemma while_lfp_hoare_rel_consequence:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom> b do body od\<lbrace>q\<rbrace>\<^sub>u" 
  by (rule consequence_hoare_rel[OF seq_step _ PHI, 
                                  OF while_lfp_hoare_rel_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_rel[OF I0' induct_step I0]])

lemma while_lfp_invr_hoare_rel_consequence:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>invr invar while\<^sub>\<bottom> b do body od\<lbrace>q\<rbrace>\<^sub>u" 
  unfolding while_lfp_invr_rel_def
  by (rule consequence_hoare_rel[OF seq_step _ PHI, 
                                  OF while_lfp_hoare_rel_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_rel[OF I0' induct_step I0]])

lemma while_lfp_invr_vrt_hoare_rel_consequence:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>invr invar vrt \<guillemotleft>R\<guillemotright> while\<^sub>\<bottom> b do body od\<lbrace>q\<rbrace>\<^sub>u" 
  unfolding while_lfp_invr_vrt_rel_def  
  by (rule consequence_hoare_rel[OF seq_step _ PHI, 
                                 OF while_lfp_hoare_rel_minimal[OF WF uimp_refl, of _ _ e],
                                 OF consequence_hoare_rel[OF I0' induct_step I0]])
                              
lemma while_lfp_hoare_rel_wp:
  assumes WF: "wf R"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>u"
  shows "\<lbrace>invar\<rbrace>while\<^sub>\<bottom> b do body od\<lbrace>q\<rbrace>\<^sub>u" 
  by (rule consequence_hoare_rel[OF uimp_refl _ PHI,
                                 OF while_lfp_hoare_rel_minimal[OF WF uimp_refl, of _ _ e],
                                 OF consequence_hoare_rel[OF I0' induct_step uimp_refl]])

lemma while_lfp_invr_hoare_rel_wp:
  assumes WF: "wf R"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>u"
  shows "\<lbrace>invar\<rbrace>invr invar while\<^sub>\<bottom> b do body od\<lbrace>q\<rbrace>\<^sub>u"                              
  unfolding while_lfp_invr_rel_def
  by (rule consequence_hoare_rel[OF uimp_refl _ PHI,
                                 OF while_lfp_hoare_rel_minimal[OF WF uimp_refl, of _ _ e],
                                 OF consequence_hoare_rel[OF I0' induct_step uimp_refl]])

lemma while_lfp_invr_vrt_hoare_rel_wp:
  assumes WF: "wf R"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>u"
  shows "\<lbrace>invar\<rbrace>invr invar vrt \<guillemotleft>R\<guillemotright> while\<^sub>\<bottom> b do body od\<lbrace>q\<rbrace>\<^sub>u"                              
  unfolding while_lfp_invr_vrt_rel_def
  by (rule consequence_hoare_rel[OF uimp_refl _ PHI,
                                 OF while_lfp_hoare_rel_minimal[OF WF uimp_refl, of _ _ e],
                                 OF consequence_hoare_rel[OF I0' induct_step uimp_refl]])
                                
lemma while_lfp_hoare_rel_sp:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom> b do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u" 
  by (rule consequence_hoare_rel [OF seq_step _ uimp_refl, 
                                  OF while_lfp_hoare_rel_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_rel[OF uimp_refl induct_step I0]])                              
                              
lemma while_lfp_invr_hoare_rel_sp:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>invr invar while\<^sub>\<bottom> b do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u" 
  unfolding while_lfp_invr_rel_def  
  by (rule consequence_hoare_rel[OF seq_step _ uimp_refl, 
                                 OF while_lfp_hoare_rel_minimal[OF WF uimp_refl, of _ _ e],
                                 OF consequence_hoare_rel[OF uimp_refl induct_step I0]])

lemma while_lfp_invr_vrt_hoare_rel_sp:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>invr invar vrt \<guillemotleft>R\<guillemotright> while\<^sub>\<bottom> b do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u" 
  unfolding while_lfp_invr_vrt_rel_def  
  by (rule consequence_hoare_rel[OF seq_step _ uimp_refl, 
                                  OF while_lfp_hoare_rel_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_rel[OF uimp_refl induct_step I0]])
  
subsection {*Hoare for from_until_loop*}     

lemma from_until_lfp_hoare_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom> init until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>u"
  unfolding from_until_lfp_rel_alt_def while_lfp_rel_def_alt
  by (rule seq_hoare_rel[OF seq_step, 
                          OF mu_rel_hoare_rel[OF WF if_rel_mono cond_rel_hoare_rel, of _ e],
                          OF seq_hoare_rel[OF induct_step], OF _ skip_rel_hoare_rel_intro],                             
      rel_auto+)

lemma from_until_lfp_invr_hoare_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom> init invr invar until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>u"
  unfolding from_until_lfp_invr_rel_def 
  using     from_until_lfp_hoare_rel_minimal [OF WF seq_step induct_step] .
    
lemma from_until_lfp_invr_vrt_hoare_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom> init invr invar vrt \<guillemotleft>R\<guillemotright> until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>u"
  unfolding from_until_lfp_invr_vrt_rel_def 
  using     from_until_lfp_hoare_rel_minimal [OF WF seq_step induct_step] .

lemma from_until_lfp_hoare_rel_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom> init until exit do body od\<lbrace>q\<rbrace>\<^sub>u" 
  unfolding from_until_lfp_rel_alt_def
  by (simp add: PHI seq_hoare_rel[OF seq_step] 
                while_lfp_hoare_rel_consequence[OF WF uimp_refl _ I0' induct_step I0])

lemma from_until_lfp_invr_hoare_rel_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom> init invr invar until exit do body od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding from_until_lfp_invr_rel_def 
  using     from_until_lfp_hoare_rel_consequence [OF WF seq_step PHI I0' induct_step I0].
    
lemma from_until_lfp_invr_vrt_hoare_rel_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom> init invr invar vrt \<guillemotleft>R\<guillemotright> until exit do body od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding from_until_lfp_invr_vrt_rel_def
  using     from_until_lfp_hoare_rel_consequence [OF WF seq_step PHI I0' induct_step I0].
 
lemma from_until_lfp_hoare_rel_wp:
  assumes WF: "wf R" 
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom> init until exit do body od\<lbrace>q\<rbrace>\<^sub>u" 
  unfolding from_until_lfp_rel_alt_def
  by (simp add: PHI seq_hoare_rel[OF seq_step]
                while_lfp_hoare_rel_consequence[OF WF uimp_refl _ I0' induct_step uimp_refl])

lemma from_until_lfp_invr_hoare_rel_wp:
  assumes WF: "wf R" 
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom> init invr invar until exit do body od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding from_until_lfp_invr_rel_def
  using from_until_lfp_hoare_rel_wp [OF WF seq_step PHI I0' induct_step] .
    
lemma from_until_lfp_invr_vrt_hoare_rel_wp:
  assumes WF: "wf R"   
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom> init invr invar vrt \<guillemotleft>R\<guillemotright> until exit do body od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding from_until_lfp_invr_vrt_rel_def
  using from_until_lfp_hoare_rel_wp[OF WF seq_step PHI I0' induct_step] .
    
lemma from_until_lfp_hoare_rel_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>u"
  assumes I0': "`q'' \<Rightarrow> invar`"    
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom> init until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>u" 
  unfolding from_until_lfp_rel_alt_def
  by (simp add: uimp_refl seq_hoare_rel[OF seq_step] pre_str_hoare_rel[OF I0']
                while_lfp_hoare_rel_consequence[OF WF uimp_refl _ uimp_refl induct_step I0])

lemma from_until_lfp_invr_hoare_rel_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>u"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom> init invr invar until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>u" 
  unfolding from_until_lfp_invr_rel_def
  using from_until_lfp_hoare_rel_sp[OF WF seq_step I0' induct_step I0] .  

lemma from_until_lfp_invr_vrt_hoare_rel_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>u"
   assumes I0': "`q'' \<Rightarrow> invar`"    
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom> init invr invar vrt \<guillemotleft>R\<guillemotright> until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>u" 
  unfolding from_until_lfp_invr_vrt_rel_def
  using from_until_lfp_hoare_rel_sp[OF WF seq_step I0' induct_step I0] .

subsection {*Hoare for do_while_loop*}     

lemma do_while_lfp_hoare_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and>  e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  shows" \<lbrace>p\<rbrace>do body while\<^sub>\<bottom> b od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"  
  unfolding do_while_lfp_rel_alt_def
  by (rule seq_hoare_rel[OF seq_step while_lfp_hoare_rel_minimal[OF WF uimp_refl induct_step]])  

lemma do_while_lfp_invr_hoare_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and>  e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  shows" \<lbrace>p\<rbrace>do body while\<^sub>\<bottom> b invr invar od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"  
  unfolding do_while_lfp_invr_rel_def
  by (auto intro!: induct_step from_until_lfp_hoare_rel_minimal[OF WF seq_step ])
 
lemma do_while_lfp_invr_vrt_hoare_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and>  e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  shows" \<lbrace>p\<rbrace>do body while\<^sub>\<bottom> b invr invar vrt \<guillemotleft>R\<guillemotright> od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"  
  unfolding do_while_lfp_invr_vrt_rel_def
  by (auto intro!: induct_step from_until_lfp_hoare_rel_minimal[OF WF seq_step ])
    
lemma do_while_lfp_hoare_rel_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom> b od\<lbrace>q\<rbrace>\<^sub>u" 
  unfolding do_while_lfp_rel_alt_def
  by (rule seq_hoare_rel[OF seq_step 
                            while_lfp_hoare_rel_consequence[OF WF uimp_refl PHI I0' induct_step I0]])
    
lemma do_while_lfp_invr_hoare_rel_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom> b invr invar  od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding do_while_lfp_invr_rel_def
  by (auto intro!: assms from_until_lfp_hoare_rel_consequence[OF WF seq_step])

lemma do_while_lfp_invr_vrt_hoare_rel_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom> b invr invar vrt \<guillemotleft>R\<guillemotright> od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding do_while_lfp_invr_vrt_rel_def
  by (auto intro!: assms from_until_lfp_hoare_rel_consequence[OF WF seq_step])
    
lemma do_while_lfp_hoare_rel_wp:
  assumes WF: "wf R" 
  assumes seq_step: "\<lbrace>invar\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  shows "\<lbrace>invar\<rbrace>do body while\<^sub>\<bottom> b od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding do_while_lfp_rel_alt_def
  by (simp add: uimp_refl seq_hoare_rel[OF seq_step] 
                while_lfp_hoare_rel_wp[OF WF PHI I0' induct_step])

lemma do_while_lfp_invr_hoare_rel_wp:
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>invar\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI : "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  shows "\<lbrace>invar\<rbrace>do body while\<^sub>\<bottom> b invr invar od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding do_while_lfp_invr_rel_def do_while_lfp_rel_alt_def  
  by (auto intro!: assms from_until_lfp_hoare_rel_wp)

lemma do_while_lfp_invr_vrt_hoare_rel_wp:
  assumes WF: "wf R"    
  assumes seq_step: "\<lbrace>invar\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI : "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  shows "\<lbrace>invar\<rbrace>do body while\<^sub>\<bottom> b invr invar vrt \<guillemotleft>R\<guillemotright> od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding do_while_lfp_invr_vrt_rel_def do_while_lfp_invr_rel_def do_while_lfp_rel_alt_def
  by (auto intro!: assms from_until_lfp_hoare_rel_wp)

lemma do_while_lfp_hoare_rel_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>q''\<rbrace>\<^sub>u"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom> b od\<lbrace>\<not>b  \<and> invar\<rbrace>\<^sub>u"
  unfolding  do_while_lfp_rel_alt_def
  by (simp add: uimp_refl seq_hoare_rel[OF seq_step] pre_str_hoare_rel[OF I0']
                while_lfp_hoare_rel_sp[OF WF uimp_refl induct_step I0])
                 
lemma do_while_lfp_invr_hoare_rel_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>q''\<rbrace>\<^sub>u"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>do body  while\<^sub>\<bottom> b invr invar od \<lbrace>\<not>b  \<and> invar\<rbrace>\<^sub>u"
  unfolding do_while_lfp_invr_vrt_rel_def do_while_lfp_invr_rel_def do_while_lfp_rel_alt_def
  by (auto intro!: assms from_until_lfp_hoare_rel_sp)
                 
lemma do_while_lfp_invr_vrt_hoare_rel_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>q''\<rbrace>\<^sub>u"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom> b invr invar vrt \<guillemotleft>R\<guillemotright> od\<lbrace>\<not>b  \<and> invar\<rbrace>\<^sub>u"
  unfolding do_while_lfp_invr_vrt_rel_def do_while_lfp_rel_alt_def
  by (auto intro!: assms from_until_lfp_hoare_rel_sp)
           
subsection {*Hoare for for_loop*}     
    
lemma for_hoare_lfp_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body ;; incr\<lbrace>invar \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>for\<^sub>\<bottom> (init, b, incr) do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding for_lfp_rel_def
  by (auto intro!: assms from_until_lfp_hoare_rel_minimal)

lemma for_lfp_invr_hoare_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body ;; incr\<lbrace>invar \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>for\<^sub>\<bottom> (init, b, incr) invr invar do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding for_lfp_invr_rel_def for_lfp_rel_def
  by (simp add: from_until_lfp_hoare_rel_minimal [OF WF seq_step, of _ e] induct_step)  

lemma for_lfp_invr_vrt_hoare_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body ;; incr\<lbrace>invar \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>for\<^sub>\<bottom> (init, b, incr) invr invar vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding for_lfp_invr_vrt_rel_def for_lfp_rel_def
  by (simp add: from_until_lfp_hoare_rel_minimal [OF WF seq_step, of _ e] induct_step)      

lemma for_lfp_hoare_rel_consequence:
  assumes WF: "wf R"
  assumes seq_step:  "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;;incr\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"
  shows "\<lbrace>p\<rbrace>for\<^sub>\<bottom> (init, b, incr) do body od\<lbrace>q\<rbrace>\<^sub>u"  
  unfolding for_lfp_rel_def
  by(simp add: from_until_lfp_hoare_rel_consequence [OF WF seq_step PHI _ induct_step I0] I0')

lemma for_lfp_invr_hoare_rel_consequence:
  assumes WF: "wf R"
  assumes seq_step:  "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;;incr\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"
  shows "\<lbrace>p\<rbrace>for\<^sub>\<bottom> (init, b, incr) invr invar do body od\<lbrace>q\<rbrace>\<^sub>u"  
  unfolding for_lfp_rel_def for_lfp_invr_rel_def
  by(simp add: from_until_lfp_hoare_rel_consequence [OF WF seq_step PHI _ induct_step I0] I0')

lemma for_lfp_invr_vrt_hoare_rel_consequence:
  assumes WF: "wf R"
  assumes seq_step:  "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;;incr\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"
  shows "\<lbrace>p\<rbrace>for\<^sub>\<bottom> (init, b, incr) invr invar vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>q\<rbrace>\<^sub>u"  
  unfolding for_lfp_rel_def for_lfp_invr_vrt_rel_def
  by(simp add: from_until_lfp_hoare_rel_consequence [OF WF seq_step PHI _ induct_step I0] I0')
    
lemma for_lfp_hoare_rel_wp:
  assumes WF : "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e=\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;;incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>for\<^sub>\<bottom> (init,b,incr) do body od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding for_lfp_rel_alt_def
  by (simp add: uimp_refl seq_hoare_rel[OF seq_step] 
                while_lfp_hoare_rel_wp[OF WF PHI I0' induct_step])

lemma for_lfp_invr_hoare_rel_wp:
  assumes WF : "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e=\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;;incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>for\<^sub>\<bottom> (init,b,incr) invr invar do body od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding for_lfp_invr_rel_def for_lfp_rel_alt_def from_until_lfp_rel_alt_def
  by (simp add: seq_hoare_rel[OF seq_step] 
                while_lfp_hoare_rel_wp[OF WF PHI I0' induct_step])

lemma for_lfp_invr_vrt_hoare_rel_wp:
  assumes WF : "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e=\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;;incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>for\<^sub>\<bottom> (init,b,incr) invr invar vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding for_lfp_invr_vrt_rel_def for_lfp_rel_alt_def from_until_lfp_rel_alt_def
  by (simp add: uimp_refl seq_hoare_rel[OF seq_step] 
                while_lfp_hoare_rel_wp[OF WF  PHI I0' induct_step])

lemma for_lfp_hoare_rel_sp:
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>u"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;;incr\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>for\<^sub>\<bottom> (init,b,incr) do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding for_lfp_rel_alt_def  
  by (simp add: seq_hoare_rel[OF seq_step] pre_str_hoare_rel[OF I0']
                while_lfp_hoare_rel_sp[OF WF uimp_refl induct_step I0])
 
lemma for_lfp_invr_hoare_rel_sp:
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>u"
  assumes I0':  "`q'' \<Rightarrow> invar`"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;;incr\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>for\<^sub>\<bottom> (init,b,incr) invr invar do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding for_lfp_invr_rel_def for_lfp_rel_alt_def from_until_lfp_rel_alt_def
  by (simp add: seq_hoare_rel[OF seq_step] pre_str_hoare_rel[OF I0']
                while_lfp_hoare_rel_sp[OF WF uimp_refl induct_step I0])
         
lemma for_lfp_invr_vrt_hoare_rel_sp:
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>u"
  assumes I0':"`q''\<Rightarrow> invar`" 
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;;incr\<lbrace>q' st\<rbrace>\<^sub>u"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>for\<^sub>\<bottom> (init,b,incr) invr invar vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding for_lfp_invr_vrt_rel_def for_lfp_rel_alt_def  from_until_lfp_rel_alt_def
  by (simp add: seq_hoare_rel[OF seq_step] pre_str_hoare_rel[OF I0']
                while_lfp_hoare_rel_sp[OF WF uimp_refl induct_step I0])
      
lemmas loop_invr_vrt_hoare_rel_sp_instantiated [hoare_sp_rules] = 
       while_lfp_invr_vrt_hoare_rel_sp [where e = "&\<Sigma>"]
       for_lfp_invr_vrt_hoare_rel_sp [where e = "&\<Sigma>"]
       do_while_lfp_invr_vrt_hoare_rel_sp [where e = "&\<Sigma>"]
       from_until_lfp_invr_vrt_hoare_rel_sp[where e = "&\<Sigma>"]

lemmas loop_invr_vrt_hoare_rel_wp_instantiated [hoare_wp_rules] = 
       while_lfp_invr_vrt_hoare_rel_wp [where e = "&\<Sigma>"]
       for_lfp_invr_vrt_hoare_rel_wp [where e = "&\<Sigma>"]
       do_while_lfp_invr_vrt_hoare_rel_wp [where e = "&\<Sigma>"]
       from_until_lfp_invr_vrt_hoare_rel_wp[where e = "&\<Sigma>"]

end

