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

theory utp_hoare_extra
  imports UTP.utp_hoare
    "../../AlgebraicLaws/Algebraic_Laws"
begin

named_theorems hoare_sp_rules and hoare_wp_rules and hoare_wp_proof_annotation_rules

subsection {*Hoare triple definition*}

lemma assisgns_true_hoare_rel:
  "\<lbrace>p\<rbrace> P \<lbrace>true\<rbrace>\<^sub>u"
  by rel_simp

lemma skip_true_hoare_rel: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>r\<lbrace>true\<rbrace>\<^sub>u"
   by rel_simp

lemma pre_false_hoare_rel: 
  "\<lbrace>false\<rbrace>C\<lbrace>q\<rbrace>\<^sub>u"
  by rel_simp
  
    
subsection {*Hoare SKIP*}

declare skip_hoare_r[hoare_sp_rules, hoare_wp_rules, hoare_wp_proof_annotation_rules]
  
subsection {*Hoare for assignment*}
    
declare assign_floyd_hoare_r[hoare_sp_rules]

subsection {*Hoare for Sequential Composition*}

declare seq_hoare_r[hoare_wp_rules, hoare_sp_rules]
    
subsection {*Hoare for Conditional*}
    
declare cond_hoare_r_wp[hoare_wp_rules, hoare_wp_proof_annotation_rules]
declare cond_hoare_r_sp [hoare_sp_rules]

subsection {*Hoare for frames*}
      
lemma anti_frame_intro:
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
  apply (rule nu_hoare_rel_partial)
  apply (rule cond_hoare_rel)  
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
    
lemma while_gfp_hoare_rel_consequence_partial:
  assumes seq_step: "`p\<Rightarrow>invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "` invar \<and> b  \<Rightarrow> p'`"
  assumes induct_step: "\<lbrace>p'\<rbrace>C \<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top> b do C od\<lbrace>q\<rbrace>\<^sub>u"
  by (rule consequence_hoare_rel[OF seq_step _ PHI, 
                                 OF while_gfp_hoare_rel_minimal_partial[OF uimp_refl],
                                 OF consequence_hoare_rel[OF I0' induct_step I0]])

lemma while_gfp_invr_hoare_rel_consequence_partial:
  assumes seq_step: "`p\<Rightarrow>invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "` invar \<and> b  \<Rightarrow> p'`"
  assumes induct_step: "\<lbrace>p'\<rbrace>C \<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>invr invar while\<^sup>\<top> b do C od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding while_gfp_invr_rel_def 
  by (auto intro!: assms while_gfp_hoare_rel_consequence_partial)  

lemma while_gfp_hoare_rel_wp_partial:
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "`invar \<and> b \<Rightarrow> p'`"
  assumes induct_step: "\<lbrace>p'\<rbrace>C \<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>invar\<rbrace>while\<^sup>\<top> b do C od\<lbrace>q\<rbrace>\<^sub>u"
  by (rule consequence_hoare_rel[OF uimp_refl _ PHI, 
                                 OF while_gfp_hoare_rel_minimal_partial[OF uimp_refl],
                                 OF consequence_hoare_rel[OF I0' induct_step uimp_refl]])    

lemma while_gfp_invr_hoare_rel_wp_partial:
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "`invar \<and> b \<Rightarrow> p'`"
  assumes induct_step: "\<lbrace>p'\<rbrace>C \<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>invar\<rbrace>invr invar while\<^sup>\<top> b do C od\<lbrace>q\<rbrace>\<^sub>u"                             
  unfolding while_gfp_invr_rel_def 
  by (auto intro!: assms while_gfp_hoare_rel_consequence_partial)  
                           
lemma while_gfp_hoare_rel_sp_partial:
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<lbrace>invar \<and> b\<rbrace>C \<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top> b do C od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  by (rule consequence_hoare_rel[OF seq_step _ uimp_refl, 
                                 OF while_gfp_hoare_rel_minimal_partial[OF uimp_refl],
                                 OF consequence_hoare_rel[OF uimp_refl induct_step I0]])

lemma while_gfp_invr_hoare_rel_sp_partial:
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<lbrace>invar \<and> b\<rbrace>C \<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>invr invar while\<^sup>\<top> b do C od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding while_gfp_invr_rel_def 
  by (rule consequence_hoare_rel[OF seq_step _ uimp_refl, 
                                 OF while_gfp_hoare_rel_minimal_partial[OF uimp_refl],
                                 OF consequence_hoare_rel[OF uimp_refl induct_step I0]])
                                                          
lemma while_lfp_hoare_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`" 
  assumes induct_step:"\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"    
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom> b do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding while_lfp_rel_def_alt
proof (rule pre_str_hoare_rel[OF seq_step mu_hoare_rel[OF WF if_rel_mono cond_hoare_rel, of _ e]], goal_cases)
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
  
lemma from_until_lfp_hoare_rel_minimal_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes induct_step: "\<lbrace>\<not> exit \<and> invar\<rbrace> body\<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top> init until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>u"
  unfolding from_until_gfp_rel_alt_def
  proof -
    have induct_step': "\<lbrace>invar \<and> \<not> exit\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
      by (metis assms(2) utp_pred_laws.inf.commute)
    have "`\<not> \<not> exit \<and> invar \<Rightarrow> invar \<and> exit`"
      by (simp add: utp_pred_laws.inf.commute)
    then have "\<lbrace>invar\<rbrace>while\<^sup>\<top> \<not> exit do body od\<lbrace>invar \<and> exit\<rbrace>\<^sub>u"
      using induct_step' by (metis (no_types) p_imp_p taut_true while_gfp_hoare_rel_wp_partial)
    then show "\<lbrace>p\<rbrace>init ;; while\<^sup>\<top> \<not> exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>u"
      by (metis (no_types) seq_hoare_rel seq_step utp_pred_laws.inf.commute)
  qed

lemma from_until_lfp_invr_hoare_rel_minimal_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes induct_step: "\<lbrace>\<not> exit \<and> invar\<rbrace> body\<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top> init invr invar until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>u"
  unfolding from_until_gfp_invr_rel_def
  by (auto intro!: assms from_until_lfp_hoare_rel_minimal_partial)  

lemma from_until_gfp_hoare_rel_consequence_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q `"
  assumes I0': "`invar \<and> \<not> exit \<Rightarrow> p'`"  
  assumes induct_step: "\<lbrace>p'\<rbrace> body\<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top> init until exit do body od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding from_until_gfp_rel_alt_def
  proof -
    have PHI': "`\<not> \<not> exit \<and> invar \<Rightarrow> q`"
      by (metis PHI utp_pred_laws.double_compl)
    have "`invar \<Rightarrow> invar`"
      by (metis uimp_refl)
    then have "\<lbrace>invar\<rbrace>while\<^sup>\<top> \<not> exit do body od\<lbrace>q\<rbrace>\<^sub>u"
      using PHI' I0 I0' induct_step while_gfp_hoare_rel_consequence_partial by blast
    then show "\<lbrace>p\<rbrace>init ;; while\<^sup>\<top> \<not> exit do body od\<lbrace>q\<rbrace>\<^sub>u"
      using seq_hoare_rel seq_step by blast
  qed

lemma from_until_gfp_invr_hoare_rel_consequence_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q `"
  assumes I0': "`invar \<and> \<not> exit \<Rightarrow> p'`"  
  assumes induct_step: "\<lbrace>p'\<rbrace> body\<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top> init invr invar until exit do body od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding from_until_gfp_invr_rel_def
  by (auto intro!: assms from_until_gfp_hoare_rel_consequence_partial)  

lemma from_until_gfp_hoare_rel_wp_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`" 
  assumes I0': "`invar \<and> \<not> exit \<Rightarrow> p'`"  
  assumes induct_step:"\<lbrace>p'\<rbrace> body\<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top> init until exit do body od\<lbrace>q\<rbrace>\<^sub>u"  
  unfolding from_until_gfp_rel_alt_def
proof -
  have "\<lbrace>invar\<rbrace>while\<^sup>\<top> \<not> exit do body od\<lbrace>q\<rbrace>\<^sub>u"
    by (metis (no_types) I0' PHI induct_step utp_pred_laws.double_compl while_gfp_hoare_rel_wp_partial)
  then show "\<lbrace>p\<rbrace>init ;; while\<^sup>\<top> \<not> exit do body od\<lbrace>q\<rbrace>\<^sub>u"
    using seq_hoare_rel seq_step by blast
qed 

lemma from_until_gfp_invr_hoare_rel_wp_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`" 
  assumes I0': "`invar \<and> \<not> exit \<Rightarrow> p'`"  
  assumes induct_step:"\<lbrace>p'\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top> init invr invar until exit do body od\<lbrace>q\<rbrace>\<^sub>u"  
  unfolding from_until_gfp_invr_rel_def
  by (auto intro!: assms from_until_gfp_hoare_rel_wp_partial)  

lemma from_until_gfp_hoare_rel_sp_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"
  assumes induct_step: "\<lbrace>invar \<and> \<not> exit\<rbrace> body\<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top> init until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>u"
  unfolding from_until_gfp_rel_alt_def
proof -
  have "\<lbrace>invar\<rbrace>while\<^sup>\<top> \<not> exit do body od\<lbrace>\<not> \<not> exit \<and> invar\<rbrace>\<^sub>u"
    by (metis I0 induct_step uimp_refl while_gfp_hoare_rel_sp_partial)
  then have "\<lbrace>invar\<rbrace>while\<^sup>\<top> \<not> exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>u"
    by (metis double_negation)
  then show "\<lbrace>p\<rbrace>init ;; while\<^sup>\<top> \<not> exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>u"
    by (metis seq_hoare_rel seq_step)
qed

lemma from_until_gfp_invr_hoare_rel_sp_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"
  assumes induct_step: "\<lbrace>invar \<and> \<not> exit\<rbrace> body\<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top> init invr invar until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>u"
  unfolding  from_until_gfp_invr_rel_def
  by (auto intro!: assms from_until_gfp_hoare_rel_sp_partial)
    
lemma from_until_lfp_hoare_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom> init until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>u"
  unfolding from_until_lfp_rel_alt_def while_lfp_rel_def_alt
  by (rule seq_hoare_rel[OF seq_step, 
                         OF mu_hoare_rel[OF WF if_rel_mono cond_hoare_rel, of _ e],
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

lemma do_while_gfp_hoare_rel_minimal_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"  
  assumes induct_step: "\<lbrace>b \<and> invar\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>p\<rbrace>do body while\<^sup>\<top> b od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding do_while_gfp_rel_alt_def
  proof -
    have "\<lbrace>invar\<rbrace>while\<^sup>\<top> b do body od\<lbrace>invar \<and> \<not> b\<rbrace>\<^sub>u"
      by (metis (no_types) assms(2) conj_comm p_imp_p taut_true while_gfp_hoare_rel_wp_partial)
    then show "\<lbrace>p\<rbrace>body ;; while\<^sup>\<top> b do body od\<lbrace>\<not> b \<and> invar\<rbrace>\<^sub>u"
      by (metis (no_types) conj_comm seq_hoare_rel seq_step)
  qed    

lemma do_while_gfp_invr_hoare_rel_minimal_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"  
  assumes induct_step: "\<lbrace>b \<and> invar\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>p\<rbrace>do body while\<^sup>\<top> b invr invar od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding do_while_gfp_invr_rel_def
  by (simp add: from_until_lfp_hoare_rel_minimal_partial induct_step seq_step)

lemma do_while_gfp_hoare_rel_consequence_partial:
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "`b \<and> invar \<Rightarrow> p'`"
  assumes induct_step: "\<lbrace>p'\<rbrace>body\<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>do body while\<^sup>\<top> b od\<lbrace>q\<rbrace>\<^sub>u"
proof -
  have "`invar \<and> \<not> \<not> b \<Rightarrow> p'`"
    by (simp add: I0' utp_pred_laws.inf_commute)
  then have "\<lbrace>p\<rbrace>from\<^sup>\<top> body until \<not> b do body od\<lbrace>q\<rbrace>\<^sub>u"
    using I0 PHI from_until_gfp_hoare_rel_consequence_partial induct_step seq_step by blast
  then show ?thesis
    by (metis do_while_gfp_rel_def)
qed  
 
lemma do_while_gfp_invr_hoare_rel_consequence_partial:
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "`b \<and> invar \<Rightarrow> p'`"
  assumes induct_step: "\<lbrace>p'\<rbrace>body\<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>do body while\<^sup>\<top> b invr invar od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding do_while_gfp_invr_rel_def
  proof -
    have "`invar \<and> \<not> \<not> b \<Rightarrow> p'`"
      by (simp add: I0' utp_pred_laws.inf_commute)
    then show "\<lbrace>p\<rbrace>from\<^sup>\<top> body until \<not> b do body od\<lbrace>q\<rbrace>\<^sub>u"
      using I0 PHI from_until_gfp_hoare_rel_consequence_partial induct_step seq_step by blast
  qed

lemma do_while_gfp_hoare_rel_wp_partial:
  assumes seq_step: "\<lbrace>invar\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes induct_step: "\<lbrace>b \<and> invar\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
  shows "\<lbrace>invar\<rbrace>do body while\<^sup>\<top> b od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding do_while_gfp_rel_alt_def
  using PHI reverse_impl_refine seq_hoare_rel seq_step utp_pred_laws.inf.cobounded2 
        while_gfp_hoare_rel_wp_partial 
  by fastforce

lemma do_while_gfp_invr_hoare_rel_wp_partial:
  assumes seq_step: "\<lbrace>invar\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes induct_step: "\<lbrace>b \<and> invar\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
  shows "\<lbrace>invar\<rbrace>do body while\<^sup>\<top> b invr invar od\<lbrace>q\<rbrace>\<^sub>u"
  unfolding do_while_gfp_invr_rel_def
  using PHI from_until_gfp_hoare_rel_wp_partial reverse_impl_refine seq_step utp_pred_laws.inf_le1 
  by blast
      
lemma do_while_gfp_hoare_rel_sp_partial:
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
  assumes induct_step: "\<lbrace>b \<and> invar\<rbrace>body\<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>do body while\<^sup>\<top> b od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding do_while_gfp_rel_alt_def
  proof -
    have "\<lbrace>invar \<and> b\<rbrace>body\<lbrace>q'\<rbrace>\<^sub>u"
      by (metis conj_comm induct_step)
    then show "\<lbrace>p\<rbrace>body ;; while\<^sup>\<top> b do body od\<lbrace>\<not> b \<and> invar\<rbrace>\<^sub>u"
      by (meson I0 seq_hoare_rel seq_step uimp_refl while_gfp_hoare_rel_sp_partial)
  qed
      
lemma do_while_gfp_invr_hoare_rel_sp_partial:
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"
  assumes induct_step: "\<lbrace>b \<and> invar\<rbrace>body\<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q' \<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>do body while\<^sup>\<top> b invr invar od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding do_while_gfp_rel_alt_def
  using I0 do_while_gfp_invr_hoare_rel_minimal_partial induct_step post_weak_hoare_rel seq_step 
  by blast
    
lemma do_while_lfp_hoare_rel_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>u"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and>  e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom> b od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"  
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

lemma for_hoare_gfp_rel_minimal_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes induct_step: "\<lbrace>b \<and> invar\<rbrace>body;;incr\<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>p\<rbrace>for\<^sup>\<top> (init, b, incr) do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  unfolding for_gfp_rel_alt_def
proof -
  have "\<lbrace>invar\<rbrace>while\<^sup>\<top> b do body ;; incr od\<lbrace>invar \<and> \<not> b\<rbrace>\<^sub>u"
    by (metis (no_types) assms(2) p_imp_p taut_true utp_pred_laws.inf_commute while_gfp_hoare_rel_wp_partial)
  then show "\<lbrace>p\<rbrace>init ;; while\<^sup>\<top> b do body ;; incr od\<lbrace>\<not> b \<and> invar\<rbrace>\<^sub>u"
    by (metis (no_types) seq_hoare_rel seq_step utp_pred_laws.inf_commute)
qed
  
lemma for_gfp_invr_hoare_rel_minimal_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes induct_step: "\<lbrace>b \<and> invar\<rbrace>body;;incr\<lbrace>invar\<rbrace>\<^sub>u"  
  shows "\<lbrace>p\<rbrace>for\<^sup>\<top> (init, b, incr) invr invar do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  by (simp add: for_gfp_invr_rel_def from_until_lfp_hoare_rel_minimal_partial induct_step seq_step) 
         
lemma for_gfp_hoare_rel_consequence_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "`b \<and> invar \<Rightarrow> p'`"  
  assumes induct_step: "\<lbrace>p'\<rbrace>body;;incr\<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q'\<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>for\<^sup>\<top> (init, b, incr) do body od\<lbrace>q\<rbrace>\<^sub>u"
proof -
  have "`invar \<and> \<not> \<not> b \<Rightarrow> p'`"
    by (metis I0' conj_comm double_negation)
  then have "\<lbrace>p\<rbrace>from\<^sup>\<top> init until \<not> b do body ;; incr od\<lbrace>q\<rbrace>\<^sub>u"
    by (meson I0 PHI from_until_gfp_hoare_rel_consequence_partial induct_step seq_step)
  then show ?thesis
    by (metis for_gfp_rel_def)
qed    

lemma for_gfp_invr_hoare_rel_consequence_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "`b \<and> invar \<Rightarrow> p'`"  
  assumes induct_step: "\<lbrace>p'\<rbrace>body;;incr\<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q'\<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>for\<^sup>\<top> (init, b, incr) invr invar  do body od\<lbrace>q\<rbrace>\<^sub>u"
  using I0 I0' PHI consequence_hoare_rel for_gfp_invr_hoare_rel_minimal_partial induct_step 
        post_weak_hoare_rel seq_step 
  by blast   
  
lemma for_gfp_hoare_rel_wp_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "`b \<and> invar \<Rightarrow> p'`"  
  assumes induct_step: "\<lbrace>p'\<rbrace>body;;incr\<lbrace>invar\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>for\<^sup>\<top> (init, b, incr) do body od\<lbrace>q\<rbrace>\<^sub>u"
  using I0' PHI for_gfp_hoare_rel_consequence_partial induct_step seq_step uimp_refl 
  by blast
    
lemma for_gfp_invr_hoare_rel_wp_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "`b \<and> invar \<Rightarrow> p'`"  
  assumes induct_step: "\<lbrace>p'\<rbrace>body;;incr\<lbrace>invar\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>for\<^sup>\<top> (init, b, incr) invr invar do body od\<lbrace>q\<rbrace>\<^sub>u"
  using I0' PHI for_gfp_invr_hoare_rel_consequence_partial induct_step seq_step uimp_refl 
  by blast
    
lemma for_gfp_hoare_rel_sp_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u" 
  assumes induct_step: "\<lbrace>b \<and> invar\<rbrace>body;;incr\<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q'\<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>for\<^sup>\<top> (init, b, incr) do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  using I0 for_hoare_gfp_rel_minimal_partial induct_step post_weak_hoare_rel seq_step 
  by blast    
    
lemma for_gfp_invr_hoare_rel_sp_partial:
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>u" 
  assumes induct_step: "\<lbrace>b \<and> invar\<rbrace>body;;incr\<lbrace>q'\<rbrace>\<^sub>u"
  assumes I0: "`q'\<Rightarrow> invar`"  
  shows "\<lbrace>p\<rbrace>for\<^sup>\<top> (init, b, incr) invr invar do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>u"
  using I0 for_gfp_invr_hoare_rel_minimal_partial induct_step post_weak_hoare_rel seq_step 
  by blast 
    
lemma for_lfp_hoare_rel_minimal:
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

