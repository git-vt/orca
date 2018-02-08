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

theory utp_hoare_des

imports "../../utp/utp_rec_total_des"

begin
section {*Hoare logic for designs*}  
named_theorems hoare_des
subsection {*AUX lemmas*} 
  
lemma uimp_refl:"`p \<Rightarrow> p`"
  by pred_simp  
    
subsection {*Hoare triple definition*}

definition hoare_d :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>D") where
[upred_defs]:"\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>D = ((p \<turnstile>\<^sub>n \<lceil>r\<rceil>\<^sub>>) \<sqsubseteq> Q)"

lemma assisgns_d_true_hoare_ndes[hoare_des]: 
  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>D\<lbrace>true\<rbrace>\<^sub>D"
  by rel_auto

lemma skip_d_true_hoare_ndes[hoare_des]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>D\<lbrace>true\<rbrace>\<^sub>D"
  by rel_auto

lemma false_hoare_ndes[hoare_des]: 
  "\<lbrace>false\<rbrace>C\<lbrace>q\<rbrace>\<^sub>D"
  by rel_auto

subsection {*Precondition strengthening*}

lemma pre_str_hoare_ndes[hoare_des]:
  assumes "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" and "\<lbrace>p\<^sub>2\<rbrace>C\<lbrace>q\<rbrace>\<^sub>D"
  shows "\<lbrace>p\<^sub>1\<rbrace>C\<lbrace>q\<rbrace>\<^sub>D" 
  by (insert assms) rel_auto

subsection {*Post-condition weakening*}

lemma post_weak_hoare_ndes[hoare_des]:
  assumes "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>2\<rbrace>\<^sub>D" and "`q\<^sub>2 \<Rightarrow> q\<^sub>1`"
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>1\<rbrace>\<^sub>D" 
 by (insert assms) rel_auto

subsection {*Consequence rule*}
  
lemma consequence_hoare_ndes[hoare_des]:
  assumes I0': "`p \<Rightarrow> p'`" 
  assumes induct_step:"\<lbrace>p'\<rbrace> C \<lbrace>q'\<rbrace>\<^sub>D" 
  assumes I0 :"`q' \<Rightarrow> q`"  
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<rbrace>\<^sub>D"
proof(rule post_weak_hoare_ndes[OF _ I0], goal_cases)
  case 1
  then show ?case by (rule pre_str_hoare_ndes[OF I0' induct_step ]) 
qed   
    
subsection {*Hoare and assertion logic*}

lemma conj_hoare_ndes[hoare_des]: 
  assumes"\<lbrace>p\<rbrace>C\<lbrace>r\<rbrace>\<^sub>D" and "\<lbrace>p\<rbrace>C\<lbrace>s\<rbrace>\<^sub>D"
  shows "\<lbrace>p\<rbrace>C\<lbrace>r \<and> s\<rbrace>\<^sub>D"
  by (insert assms) rel_auto

subsection {*Hoare SKIP*}

lemma skip_d_hoare_ndes[hoare_des]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>D\<lbrace>p\<rbrace>\<^sub>D"
  by rel_auto
    
lemma skip_d_hoare_ndes_intro[hoare_des]: 
  "`p \<Rightarrow> q`\<Longrightarrow>\<lbrace>p\<rbrace>SKIP\<^sub>D\<lbrace>q\<rbrace>\<^sub>D"
  by rel_auto
    
subsection {*Hoare for assignment*}

lemma assigns_d_hoare_ndes [hoare_des]: 
  assumes"`p \<Rightarrow> \<sigma> \<dagger> q`" 
  shows  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>D\<lbrace>q\<rbrace>\<^sub>D"
  by (insert assms) rel_auto

lemma assigns_d_hoare_ndes'[hoare_des]: 
  "\<lbrace>\<sigma> \<dagger> p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>D\<lbrace>p\<rbrace>\<^sub>D"
  by rel_auto

lemma assigns_d_floyd_ndes[hoare_des]:
  assumes "vwb_lens x"
  shows \<open>\<lbrace>p\<rbrace>x :=\<^sub>D e\<lbrace>\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrace>\<^sub>D\<close>
    using assms
  apply rel_simp
  apply transfer
  apply (rule_tac x = \<open>get\<^bsub>x\<^esub> more\<close> in exI)
  apply auto
  done

subsection {*Hoare for Sequential Composition*}

lemma seq_hoare_ndes[hoare_des]: 
  assumes"\<lbrace>p\<rbrace>C\<^sub>1\<lbrace>s\<rbrace>\<^sub>D" and "\<lbrace>s\<rbrace>C\<^sub>2\<lbrace>r\<rbrace>\<^sub>D" 
  shows"\<lbrace>p\<rbrace>C\<^sub>1 ;; C\<^sub>2\<lbrace>r\<rbrace>\<^sub>D"
  by (insert assms, rel_auto) metis+ 

subsection {*Hoare for Conditional*}

lemma cond_d_hoare_ndes[hoare_des]: 
  assumes "\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>D" and "\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>D" 
  shows "\<lbrace>p\<rbrace>C\<^sub>1 \<triangleleft> \<lceil>b\<rceil>\<^sub>D\<^sub>< \<triangleright> C\<^sub>2\<lbrace>q\<rbrace>\<^sub>D"
  by (insert assms, rel_auto) metis+ 

lemma if_d_hoare_ndes[hoare_des]: 
  assumes "\<lbrace>p\<rbrace>\<lceil>b\<rceil>\<^sub>D\<^sub>< \<and> C\<^sub>1\<lbrace>q\<rbrace>\<^sub>D" and "\<lbrace>p\<rbrace>\<lceil>\<not>b\<rceil>\<^sub>D\<^sub>< \<and> C\<^sub>2\<lbrace>q\<rbrace>\<^sub>D" 
  shows "\<lbrace>p\<rbrace>bif\<^sub>D b then C\<^sub>1 else C\<^sub>2 eif \<lbrace>q\<rbrace>\<^sub>D"
  by (insert assms, rel_auto) 
    
lemma if_d_hoare_ndes'[hoare_des]:
  assumes \<open>\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>D\<close> and \<open>\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>s\<rbrace>\<^sub>D\<close>
  shows \<open>\<lbrace>p\<rbrace>bif\<^sub>D b then C\<^sub>1 else C\<^sub>2 eif\<lbrace>q \<or> s\<rbrace>\<^sub>D\<close>
  by (insert assms, rel_auto) metis+
    
subsection {*Hoare for recursion*}
  
lemma nu_des_hoare_ndes_partial[hoare_des]:
  assumes induct_step:
  "\<And> P. P is \<^bold>H \<Longrightarrow> \<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>D \<Longrightarrow> \<lbrace>p\<rbrace>F P\<lbrace>q\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>\<nu>\<^sub>D F\<lbrace>q\<rbrace>\<^sub>D" 
proof -
  have is_ndesign: "\<lceil>p\<rceil>\<^sub>< \<turnstile>\<^sub>r \<lceil>q\<rceil>\<^sub>> is \<^bold>H"
    using rdesign_is_H1_H2[of "\<lceil>p\<rceil>\<^sub><" "\<lceil>q\<rceil>\<^sub>>"]
    by simp 
  also have fp_refine_spec:"\<lceil>p\<rceil>\<^sub>< \<turnstile>\<^sub>r \<lceil>q\<rceil>\<^sub>> \<sqsubseteq> F (\<lceil>p\<rceil>\<^sub>< \<turnstile>\<^sub>r \<lceil>q\<rceil>\<^sub>>)"
    by (rule induct_step[unfolded hoare_d_def ndesign_def, OF is_ndesign, simplified])
  ultimately show ?thesis 
    unfolding hoare_d_def ndesign_def
    by (rule design_theory_continuous.GFP_upperbound)
qed  
   
lemma nu_ndes_hoare_ndes_partial[hoare_des]:
  assumes induct_step:
  "\<And> P. P is \<^bold>N \<Longrightarrow> \<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>D \<Longrightarrow> \<lbrace>p\<rbrace>F P\<lbrace>q\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>\<nu>\<^sub>N F\<lbrace>q\<rbrace>\<^sub>D" 
proof -
  have is_ndesign: "p \<turnstile>\<^sub>n \<lceil>q\<rceil>\<^sub>> is \<^bold>N"
    using ndesign_H1_H3[of p "\<lceil>q\<rceil>\<^sub>>"]
    by simp 
  also have fp_refine_spec:"p \<turnstile>\<^sub>n \<lceil>q\<rceil>\<^sub>> \<sqsubseteq> F (p \<turnstile>\<^sub>n \<lceil>q\<rceil>\<^sub>>)"
    by (rule induct_step[unfolded hoare_d_def, OF is_ndesign, simplified]) 
  ultimately show ?thesis 
    unfolding hoare_d_def
    by (rule normal_design_theory_continuous.GFP_upperbound)
qed
  
lemma nu_ndes_hoare_ndes[hoare_des]:
  assumes  H: "F \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  assumes WF: "wf R"
  assumes  M: "Mono\<^bsub>uthy_order NDES\<^esub> F"  
  assumes induct_step:
    "\<And>st P. P is \<^bold>N \<Longrightarrow> \<lbrace>p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>P\<lbrace>q\<rbrace>\<^sub>D \<Longrightarrow> \<lbrace>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>F P\<lbrace>q\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>\<nu>\<^sub>N F\<lbrace>q\<rbrace>\<^sub>D" 
proof -
  { fix st 
    have "(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n \<lceil>q\<rceil>\<^sub>> \<sqsubseteq> F ((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n \<lceil>q\<rceil>\<^sub>>)"
      by (rule induct_step[unfolded hoare_d_def, 
                           OF ndesign_H1_H3[of "(p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>)" "\<lceil>q\<rceil>\<^sub>>"] order_refl]) 
  }
  then show ?thesis  
    unfolding hoare_d_def 
    by (rule ndesign_nu_wf_refine_intro[OF WF M H, of _ e])
qed  
  
lemma mu_ndes_hoare_ndes[hoare_des]:
  assumes  H: "F \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  assumes WF: "wf R"
  assumes  M: "Mono\<^bsub>uthy_order NDES\<^esub> F"  
  assumes induct_step:
    "\<And>st P. P is \<^bold>N \<Longrightarrow> \<lbrace>(p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>)\<rbrace>P\<lbrace>q\<rbrace>\<^sub>D \<Longrightarrow> \<lbrace>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>F P\<lbrace>q\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>\<mu>\<^sub>N F\<lbrace>q\<rbrace>\<^sub>D" 
proof -
  { fix st
    have "(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n \<lceil>q\<rceil>\<^sub>> \<sqsubseteq> F ((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n \<lceil>q\<rceil>\<^sub>>)"
      by (rule induct_step[unfolded hoare_d_def, 
                           OF ndesign_H1_H3[of "(p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>)" "\<lceil>q\<rceil>\<^sub>>"] order_refl]) 
  }
  then show ?thesis  
    unfolding hoare_d_def 
    by (rule ndesign_mu_wf_refine_intro[OF WF M H, of _ e])
qed

  
subsection {*Hoare for frames*}

lemma antiframe_hoare_ndes[hoare_des]:
  assumes "vwb_lens a"
  assumes "a \<sharp> r" 
  assumes "a \<natural> q"    
  assumes "\<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>D"  
  shows "\<lbrace>p \<and> r\<rbrace>antiframe\<^sub>D a P\<lbrace>q \<and> r\<rbrace>\<^sub>D"
  using assms by (rel_simp)

lemma antiframe_hoare_ndes_stronger[hoare_des]:
  assumes "vwb_lens a"
  assumes "a \<sharp> r" 
  assumes "a \<natural> q"    
  assumes "\<lbrace>p \<and> r\<rbrace>P\<lbrace>q\<rbrace>\<^sub>D"  
  shows "\<lbrace>p \<and> r\<rbrace>antiframe\<^sub>D a P\<lbrace>q \<and> r\<rbrace>\<^sub>D"
  using assms by (rel_simp)
        
lemma frame_hoare_ndes[hoare_des]:
  assumes "vwb_lens a"
  assumes "a \<natural> r" 
  assumes "a \<sharp> q"    
  assumes "\<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>D"  
  shows "\<lbrace>p \<and> r\<rbrace>frame\<^sub>D a P\<lbrace>q \<and> r\<rbrace>\<^sub>D"
  using assms by (rel_simp)  

lemma frame_hoare_ndes_stronger[hoare_des]:
  assumes "vwb_lens a"
  assumes "a \<natural> r" 
  assumes "a \<sharp> q"    
  assumes "\<lbrace>p \<and> r\<rbrace>P\<lbrace>q\<rbrace>\<^sub>D"  
  shows "\<lbrace>p \<and> r\<rbrace>frame\<^sub>D a P\<lbrace>q \<and> r\<rbrace>\<^sub>D"
  using assms by (rel_simp) 

subsection {*Hoare for from_until-loop*} 
(*Besides assumptions related to the healthiness conditions,
  The order of the assumption forms the control flow of the iteration*)
lemma from_until_gfp_hoare_ndes_minimal[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step:"\<And> st. \<lbrace>\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top>\<^sup>N init until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>D"
  unfolding  from_until_gfp_invr_ndes_def from_until_gfp_ndes_def  
proof (rule seq_hoare_ndes [OF seq_step], goal_cases)
  case 1
  then show ?case
  proof (rule nu_ndes_hoare_ndes [OF _ WF, where e = "e" and p= "invar"], goal_cases)
    case 1
    then show ?case by (rule stronger_if_d_seq_r_H1_H3_closed[OF BH skip_d_is_H1_H3]) 
  next
    case 2
    then show ?case by (rule mono_Monotone_utp_order [OF if_d_mono])
  next
    case (3 st P)
    assume P_is_N: "P is \<^bold>N " 
    assume P_is_wf:"\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>P\<lbrace>exit \<and> invar\<rbrace>\<^sub>D"  
    show ?case
    proof (rule cond_d_hoare_ndes, goal_cases)
      case 1
      then show ?case
      proof (rule seq_hoare_ndes[of _ _ "invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>"], goal_cases)
        case 1
        then show ?case using induct_step[of st] by assumption
      next
        case 2
        then show ?case using P_is_wf by assumption 
      qed
    next
      case 2
      then show ?case 
      proof (rule pre_str_hoare_ndes[of _ "exit \<and> invar"], goal_cases)
        case 1
        then show ?case by pred_simp 
      next
        case 2
        then show ?case by (rule skip_d_hoare_ndes) 
      qed
    qed
  qed
qed

lemma from_until_gfp_invr_hoare_ndes_minimal[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step:"\<And> st. \<lbrace>\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top>\<^sup>N init invr invar until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>D"
  unfolding from_until_gfp_invr_ndes_def  
  using from_until_gfp_hoare_ndes_minimal assms
  by blast
    
lemma from_until_gfp_invr_vrt_hoare_ndes_minimal[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step:"\<And> st. \<lbrace>\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top>\<^sup>N init invr invar vrt \<guillemotleft>R\<guillemotright>until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>D"
  unfolding from_until_gfp_invr_vrt_ndes_def  
  using from_until_gfp_hoare_ndes_minimal assms
  by blast

lemma from_until_lfp_hoare_ndes_minimal[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step:"\<And> st. \<lbrace>\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom>\<^sub>N init until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>D"
  unfolding  from_until_lfp_invr_ndes_def from_until_lfp_ndes_def  
proof (rule seq_hoare_ndes, rule seq_step, goal_cases)
  case 1
  then show ?case
  proof (rule mu_ndes_hoare_ndes[OF _ WF, where e = "e" and p= "invar"], goal_cases)
    case 1
    then show ?case by (rule stronger_if_d_seq_r_H1_H3_closed[OF BH skip_d_is_H1_H3]) 
  next
    case 2
    then show ?case by (rule mono_Monotone_utp_order [OF if_d_mono]) 
  next
    case (3 st P)
    assume P_is_N: "P is \<^bold>N " 
    assume P_is_wf:"\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>P\<lbrace>exit \<and> invar\<rbrace>\<^sub>D"  
    show ?case
    proof (rule cond_d_hoare_ndes, goal_cases)
      case 1
      then show ?case
      proof (rule seq_hoare_ndes[of _ _ "invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>"], goal_cases)
        case 1
        then show ?case using induct_step[of st]  using pre_str_hoare_ndes by blast
      next
        case 2
        then show ?case using P_is_wf by assumption 
      qed
    next
      case 2
      then show ?case 
      proof (rule pre_str_hoare_ndes[of _ "exit \<and> invar"], goal_cases)
        case 1
        then show ?case by pred_simp 
      next
        case 2
        then show ?case by (rule skip_d_hoare_ndes) 
      qed
    qed
  qed
qed
  
lemma from_until_lfp_invr_hoare_ndes_minimal[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step:"\<And> st. \<lbrace>\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom>\<^sub>N init invr invar until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>D"
  unfolding from_until_lfp_invr_ndes_def  
  using from_until_lfp_hoare_ndes_minimal assms
  by blast

lemma from_until_lfp_invr_vrt_hoare_ndes_minimal[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step:"\<And> st. \<lbrace>\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom>\<^sub>N init invr invar vrt \<guillemotleft>R\<guillemotright> until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>D"
  unfolding from_until_lfp_invr_vrt_ndes_def  
  using from_until_lfp_hoare_ndes_minimal assms
  by blast
    
lemma from_until_gfp_hoare_ndes_consequence[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace>init \<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI:"`(exit \<and> invar) \<Rightarrow> q`"  
  assumes I0': "\<And> st. `\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"         
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top>\<^sup>N init until exit do body od\<lbrace>q\<rbrace>\<^sub>D"
  by (blast intro: consequence_hoare_ndes [of p,OF uimp_refl _ PHI]
                   from_until_gfp_hoare_ndes_minimal[OF BH WF seq_step]
                   consequence_hoare_ndes[OF I0' induct_step I0 ])
                 
lemma from_until_lfp_hoare_ndes_consequence[hoare_des]:  
  assumes BH :"body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace> init \<lbrace>invar\<rbrace>\<^sub>D"
  assumes PHI:"`(exit \<and> invar) \<Rightarrow> q`"    
  assumes I0': "\<And> st. `\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D" 
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"   
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom>\<^sub>N init until exit do body od\<lbrace>q\<rbrace>\<^sub>D"  
  by (blast intro: consequence_hoare_ndes [of p,OF uimp_refl _ PHI ]
                   from_until_lfp_hoare_ndes_minimal[OF BH WF seq_step ]
                   consequence_hoare_ndes[OF I0' induct_step I0 ])  

lemma from_until_gfp_hoare_ndes_sp[hoare_des]:  
  assumes BH :"body is H1" 
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace> init \<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step:"\<And> st. \<lbrace>\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top>\<^sup>N init until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>D"
  by (rule from_until_gfp_hoare_ndes_consequence [OF BH WF seq_step uimp_refl  uimp_refl induct_step I0])  
                                  
lemma from_until_lfp_hoare_ndes_sp[hoare_des]:  
  assumes BH :"body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace> init \<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step:"\<And> st. \<lbrace>\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom>\<^sub>N init until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>D"
  by (rule from_until_lfp_hoare_ndes_consequence[OF BH WF seq_step uimp_refl uimp_refl induct_step I0 ])  

lemma from_until_gfp_invr_hoare_ndes_sp[hoare_des]:  
  assumes BH :"body is H1" 
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace> init \<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step:"\<And> st. \<lbrace>\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top>\<^sup>N init invr invar until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>D"
  unfolding from_until_gfp_invr_ndes_def 
  using from_until_gfp_hoare_ndes_sp[OF BH WF seq_step induct_step I0] .
    
lemma from_until_lfp_invr_hoare_ndes_sp[hoare_des]:  
  assumes BH :"body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace> init \<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step:"\<And> st. \<lbrace>\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom>\<^sub>N init invr invar until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>D"
  unfolding from_until_lfp_invr_ndes_def 
  using from_until_lfp_hoare_ndes_sp[OF BH WF seq_step induct_step I0] .

lemma from_until_gfp_invr_vrt_hoare_ndes_sp[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace> init \<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step:"\<And> st. \<lbrace>\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top>\<^sup>N init invr invar vrt \<guillemotleft>R\<guillemotright> until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>D"
  unfolding from_until_gfp_invr_vrt_ndes_def 
  using from_until_gfp_hoare_ndes_sp[OF BH WF seq_step induct_step I0] .
    
lemma from_until_lfp_invr_vrt_hoare_ndes_sp[hoare_des]:  
  assumes BH :"body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace> init \<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step:"\<And> st. \<lbrace>\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom>\<^sub>N init invr invar vrt \<guillemotleft>R\<guillemotright> until exit do body od\<lbrace>exit \<and> invar\<rbrace>\<^sub>D"
  unfolding from_until_lfp_invr_vrt_ndes_def 
  using from_until_lfp_hoare_ndes_sp[OF BH WF seq_step induct_step I0] .

lemma from_until_gfp_hoare_ndes_wp[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace> init \<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI:"`(exit \<and> invar) \<Rightarrow> q`"    
  assumes I0': "\<And> st. `\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"   
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top>\<^sup>N init until exit do body od\<lbrace>q\<rbrace>\<^sub>D"
  by (rule from_until_gfp_hoare_ndes_consequence[OF BH WF seq_step PHI I0' induct_step uimp_refl])  
    
lemma from_until_lfp_hoare_ndes_wp[hoare_des]:  
  assumes BH :"body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace> init \<lbrace>invar\<rbrace>\<^sub>D"     
  assumes PHI:"`(exit \<and> invar) \<Rightarrow> q`"      
  assumes I0': "\<And> st. `\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>invar \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom>\<^sub>N init until exit do body od\<lbrace>q\<rbrace>\<^sub>D"
  by (rule from_until_lfp_hoare_ndes_consequence[OF BH WF seq_step PHI I0' induct_step uimp_refl]) 

lemma from_until_gfp_invr_hoare_ndes_wp[hoare_des]:  
  assumes BH :"body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace> init \<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI:"`(exit \<and> invar) \<Rightarrow> q`"
  assumes I0': "\<And> st. `\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"   
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"      
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top>\<^sup>N init invr invar until exit do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding from_until_gfp_invr_ndes_def     
  using from_until_gfp_hoare_ndes_wp[OF BH WF seq_step PHI I0' induct_step] .
    
lemma from_until_lfp_invr_hoare_ndes_wp[hoare_des]:  
  assumes BH: "body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace> init \<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI:"`(exit \<and> invar) \<Rightarrow> q`"    
  assumes I0': "\<And> st. `\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"    
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom>\<^sub>N init invr invar until exit do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding from_until_lfp_invr_ndes_def 
  using from_until_lfp_hoare_ndes_wp[OF BH WF seq_step PHI I0' induct_step] . 

lemma from_until_gfp_invr_vrt_hoare_ndes_wp[hoare_des]:  
  assumes BH :"body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace> init \<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI:"`(exit \<and> invar) \<Rightarrow> q`"  
  assumes I0': "\<And> st. `\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"    
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"    
  shows "\<lbrace>p\<rbrace>from\<^sup>\<top>\<^sup>N init invr invar vrt \<guillemotleft>R\<guillemotright>until exit do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding from_until_gfp_invr_vrt_ndes_def 
  using from_until_gfp_hoare_ndes_wp[OF BH WF seq_step  PHI I0' induct_step ] . 
     
lemma from_until_lfp_invr_vrt_hoare_ndes_wp[hoare_des]:  
  assumes BH :"body is H1"
  assumes WF: "wf R"  
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI:"`(exit \<and> invar) \<Rightarrow> q`"    
  assumes I0': "\<And> st. `\<not>exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>from\<^sub>\<bottom>\<^sub>N init invr invar vrt \<guillemotleft>R\<guillemotright>until exit do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding from_until_lfp_invr_vrt_ndes_def 
  using from_until_lfp_hoare_ndes_wp[OF BH WF seq_step PHI I0' induct_step] . 
    
subsection {*Laws for while-loop*}  
  
lemma while_gfp_hoare_ndes_minimal[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes I0: "`p\<Rightarrow> invar`"
  assumes induct_step:"\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"    
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top>\<^sup>N b do body od\<lbrace>\<not> b \<and> invar\<rbrace>\<^sub>D"
  unfolding while_gfp_ndes_def
  by (simp add: from_until_gfp_hoare_ndes_minimal[OF BH WF, where e=e]
                skip_d_hoare_ndes_intro[OF I0] induct_step)  

lemma while_gfp_invr_hoare_ndes_minimal [hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes I0: "`p\<Rightarrow> invar`"
  assumes induct_step:"\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"    
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top>\<^sup>N b invr invar do body od\<lbrace>\<not> b \<and> invar\<rbrace>\<^sub>D"
  unfolding while_gfp_invr_ndes_def  
  using while_gfp_hoare_ndes_minimal assms
  by blast

lemma while_gfp_invr_vrt_hoare_ndes_minimal [hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes I0: "`p\<Rightarrow> invar`"
  assumes induct_step:"\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"    
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top>\<^sup>N b invr invar vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>\<not> b \<and> invar\<rbrace>\<^sub>D"
  unfolding while_gfp_invr_vrt_ndes_def  
  using while_gfp_hoare_ndes_minimal assms
  by blast
    
lemma while_lfp_hoare_ndes_minimal [hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes I0: "`p\<Rightarrow> invar`"
  assumes induct_step:"\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"    
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom>\<^sub>N b do body od\<lbrace>\<not> b \<and> invar\<rbrace>\<^sub>D"
  unfolding while_lfp_ndes_def
  by (simp add: from_until_lfp_hoare_ndes_minimal[OF BH WF, where e=e]
                skip_d_hoare_ndes_intro[OF I0] induct_step)  

lemma while_lfp_invr_hoare_ndes_minimal [hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes I0: "`p\<Rightarrow> invar`"
  assumes induct_step:"\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"    
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom>\<^sub>N b invr invar do body od\<lbrace>\<not> b \<and> invar\<rbrace>\<^sub>D"
  unfolding while_lfp_invr_ndes_def
  using while_lfp_hoare_ndes_minimal assms
  by blast  

lemma while_lfp_invr_vrt_hoare_ndes_minimal [hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes I0: "`p\<Rightarrow> invar`"
  assumes induct_step:"\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"    
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom>\<^sub>N b invr invar vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>\<not> b \<and> invar\<rbrace>\<^sub>D"
  unfolding while_lfp_invr_vrt_ndes_def
  using while_lfp_hoare_ndes_minimal assms
  by blast    

lemma while_gfp_hoare_ndes_consequence[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And> st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"      
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top>\<^sup>N b do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding while_gfp_ndes_def
  by (simp add: I0' 
      from_until_gfp_hoare_ndes_consequence[OF BH WF skip_d_hoare_ndes_intro[OF seq_step] 
                                               PHI _ induct_step I0])  

lemma while_gfp_invr_hoare_ndes_consequence[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And> st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"      
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top>\<^sup>N b invr invar do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding while_gfp_invr_ndes_def
  by (rule while_gfp_hoare_ndes_consequence[OF BH WF seq_step PHI I0' induct_step I0])

lemma while_gfp_invr_vrt_hoare_ndes_consequence[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And> st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"      
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top>\<^sup>N b invr invar vrt \<guillemotleft>R\<guillemotright>do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding while_gfp_invr_vrt_ndes_def  
  by (rule while_gfp_hoare_ndes_consequence[OF BH WF seq_step PHI I0' induct_step I0])
  
lemma while_lfp_hoare_ndes_consequence[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And> st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"      
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom>\<^sub>N b do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding while_lfp_ndes_def
  by (simp add: I0' 
      from_until_lfp_hoare_ndes_consequence[OF BH WF skip_d_hoare_ndes_intro[OF seq_step] 
                                               PHI _ induct_step I0])  

lemma while_lfp_invr_hoare_ndes_consequence[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And> st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"      
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom>\<^sub>N b invr invar  do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding while_lfp_invr_ndes_def  
  using while_lfp_hoare_ndes_consequence assms 
  by blast

lemma while_lfp_invr_vrt_hoare_ndes_consequence[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And> st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"      
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom>\<^sub>N b invr invar vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding while_lfp_invr_vrt_ndes_def  
  using while_lfp_hoare_ndes_consequence assms 
  by blast
    
lemma while_gfp_hoare_ndes_sp[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"      
  assumes induct_step:"\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top>\<^sup>N b do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  by (rule while_gfp_hoare_ndes_consequence [OF BH WF seq_step uimp_refl uimp_refl induct_step I0])  

lemma while_gfp_invr_hoare_ndes_sp[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"      
  assumes induct_step:"\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top>\<^sup>N b invr invar do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding while_gfp_invr_ndes_def  
  by (rule while_gfp_hoare_ndes_consequence [OF BH WF seq_step uimp_refl uimp_refl induct_step I0])  

lemma while_gfp_invr_vrt_hoare_ndes_sp[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"      
  assumes induct_step:"\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top>\<^sup>N b invr invar vrt \<guillemotleft>R\<guillemotright>do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding while_gfp_invr_vrt_ndes_def  
  by (rule while_gfp_hoare_ndes_consequence [OF BH WF seq_step uimp_refl uimp_refl induct_step I0])  
      
lemma while_lfp_hoare_ndes_sp[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"      
  assumes induct_step:"\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom>\<^sub>N b do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  by (rule while_lfp_hoare_ndes_consequence [OF BH WF seq_step uimp_refl uimp_refl induct_step I0])  
    
lemma while_lfp_invr_hoare_ndes_sp[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"      
  assumes induct_step:"\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom>\<^sub>N b invr invar do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding while_lfp_invr_ndes_def  
  by (rule while_lfp_hoare_ndes_consequence [OF BH WF seq_step uimp_refl uimp_refl induct_step I0]) 
    
lemma while_lfp_invr_vrt_hoare_ndes_sp[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"      
  assumes induct_step:"\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0 :"\<And> st. `q' st  \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom>\<^sub>N b invr invar vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding while_lfp_invr_vrt_ndes_def  
  by (rule while_lfp_hoare_ndes_consequence [OF BH WF seq_step uimp_refl uimp_refl induct_step I0])  

lemma while_gfp_hoare_ndes_wp[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And> st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"      
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top>\<^sup>N b do body od\<lbrace>q\<rbrace>\<^sub>D"
  by (rule while_gfp_hoare_ndes_consequence[OF BH WF seq_step PHI I0' induct_step uimp_refl])

lemma while_gfp_invr_hoare_ndes_wp[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And> st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"      
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top>\<^sup>N b invr invar do body od\<lbrace>q\<rbrace>\<^sub>D"  
  unfolding while_gfp_invr_ndes_def  
  using while_gfp_hoare_ndes_wp assms
  by blast  

lemma while_gfp_invr_vrt_hoare_ndes_wp[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And> st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"      
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"
  shows "\<lbrace>p\<rbrace>while\<^sup>\<top>\<^sup>N b invr invar vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>q\<rbrace>\<^sub>D"  
  unfolding while_gfp_invr_vrt_ndes_def  
  using while_gfp_hoare_ndes_wp assms
  by blast  
    
lemma while_lfp_hoare_ndes_wp[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And> st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"      
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom>\<^sub>N b do body od\<lbrace>q\<rbrace>\<^sub>D"
  by (rule while_lfp_hoare_ndes_consequence[OF BH WF seq_step PHI I0' induct_step uimp_refl])

lemma while_lfp_invr_hoare_ndes_wp[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And> st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"      
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom>\<^sub>N b invr invar do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding while_lfp_invr_ndes_def  
  using while_lfp_hoare_ndes_wp assms
  by blast  

lemma while_lfp_invr_vrt_hoare_ndes_wp[hoare_des]:
  assumes BH :"body is H1"
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And> st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"      
  assumes induct_step:"\<And> st. \<lbrace>p' st\<rbrace> body \<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"
  shows "\<lbrace>p\<rbrace>while\<^sub>\<bottom>\<^sub>N b invr invar vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding while_lfp_invr_vrt_ndes_def  
  using while_lfp_hoare_ndes_wp assms
  by blast   
    
subsection {*Hoare for do_while-loop*}   

(*TODO: ADD LAWS FOR DO_WHILE*)

lemma do_while_gfp_hoare_ndes_minimal[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes induct_step:"\<And>st.\<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>D"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sup>\<top>\<^sup>N b od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding do_while_gfp_ndes_def
  by (simp add: from_until_gfp_hoare_ndes_minimal [OF BH WF seq_step, where e=e] induct_step)

lemma do_while_lfp_hoare_ndes_minimal[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes induct_step:"\<And>st.\<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>D"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom>\<^sub>N b od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding do_while_lfp_ndes_def
  by (simp add: from_until_lfp_hoare_ndes_minimal [OF BH WF seq_step, where e=e] induct_step)

lemma do_while_gfp_invr_hoare_ndes_minimal[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes induct_step:"\<And>st.\<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>D"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sup>\<top>\<^sup>N b invr invar od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding do_while_gfp_invr_ndes_def
  by (simp add: from_until_gfp_hoare_ndes_minimal [OF BH WF seq_step, where e=e] induct_step)

lemma do_while_lfp_invr_hoare_ndes_minimal[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes induct_step:"\<And>st.\<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>D"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom>\<^sub>N b invr invar od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding do_while_lfp_invr_ndes_def
  by (simp add: from_until_lfp_hoare_ndes_minimal [OF BH WF seq_step, where e=e] induct_step)
    
lemma do_while_gfp_invr_vrt_hoare_ndes_minimal[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes induct_step:"\<And>st.\<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>D"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sup>\<top>\<^sup>N b invr invar vrt \<guillemotleft>R\<guillemotright> od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding do_while_gfp_invr_vrt_ndes_def
  by (simp add: from_until_gfp_hoare_ndes_minimal [OF BH WF seq_step, where e=e] induct_step)

lemma do_while_lfp_invr_vrt_hoare_ndes_minimal[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D" 
  assumes induct_step:"\<And>st.\<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>D"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom>\<^sub>N b invr invar vrt \<guillemotleft>R\<guillemotright> od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding do_while_lfp_invr_vrt_ndes_def
  by (simp add: from_until_lfp_hoare_ndes_minimal [OF BH WF seq_step, where e=e] induct_step)
    
lemma do_while_gfp_hoare_ndes_consequence[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes PHI:"`\<not>b \<and> invar \<Rightarrow> q`"   
  assumes I0:"\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And>st.\<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0':"\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sup>\<top>\<^sup>N b od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding do_while_gfp_ndes_def
  by (simp add: I0 from_until_gfp_hoare_ndes_consequence[OF BH WF seq_step PHI _ induct_step I0'])   

lemma do_while_lfp_hoare_ndes_consequence[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes PHI:"`\<not>b \<and> invar \<Rightarrow> q`"   
  assumes I0:"\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And>st.\<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0':"\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom>\<^sub>N b od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding do_while_lfp_ndes_def
  by (simp add: I0 from_until_lfp_hoare_ndes_consequence[OF BH WF seq_step PHI _ induct_step I0'])   
    
lemma do_while_gfp_invr_hoare_ndes_consequence[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes PHI:"`\<not>b \<and> invar \<Rightarrow> q`"   
  assumes I0:"\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And>st.\<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0':"\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sup>\<top>\<^sup>N b invr invar od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding do_while_gfp_invr_ndes_def
  by (simp add: I0 from_until_gfp_hoare_ndes_consequence[OF BH WF seq_step PHI _ induct_step I0'])   

lemma do_while_lfp_invr_hoare_ndes_consequence[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes PHI:"`\<not>b \<and> invar \<Rightarrow> q`"   
  assumes I0:"\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And>st.\<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0':"\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom>\<^sub>N b invr invar od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding do_while_lfp_invr_ndes_def
  by (simp add: I0 from_until_lfp_hoare_ndes_consequence[OF BH WF seq_step PHI _ induct_step I0'])   

lemma do_while_gfp_invr_vrt_hoare_ndes_consequence[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes PHI:"`\<not>b \<and> invar \<Rightarrow> q`"   
  assumes I0:"\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And>st.\<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0':"\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sup>\<top>\<^sup>N b invr invar vrt \<guillemotleft>R\<guillemotright> od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding do_while_gfp_invr_vrt_ndes_def
  by (simp add: I0 from_until_gfp_hoare_ndes_consequence[OF BH WF seq_step PHI _ induct_step I0'])   

lemma do_while_lfp_invr_vrt_hoare_ndes_consequence[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes PHI:"`\<not>b \<and> invar \<Rightarrow> q`"   
  assumes I0:"\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And>st.\<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0':"\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom>\<^sub>N b invr invar vrt \<guillemotleft>R\<guillemotright> od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding do_while_lfp_invr_vrt_ndes_def
  by (simp add: I0 from_until_lfp_hoare_ndes_consequence[OF BH WF seq_step PHI _ induct_step I0'])   

lemma do_while_gfp_hoare_ndes_sp[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"     
  assumes induct_step:"\<And>st.\<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0':"\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sup>\<top>\<^sup>N b od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding do_while_gfp_ndes_def    
  by (simp add: from_until_gfp_hoare_ndes_consequence[OF BH WF seq_step uimp_refl _ induct_step I0'])   
    
lemma do_while_lfp_hoare_ndes_sp[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"     
  assumes induct_step:"\<And>st.\<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0':"\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom>\<^sub>N b od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding do_while_lfp_ndes_def    
  by (simp add: from_until_lfp_hoare_ndes_consequence[OF BH WF seq_step uimp_refl _ induct_step I0'])   
    
lemma do_while_gfp_invr_hoare_ndes_sp[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"     
  assumes induct_step:"\<And>st.\<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0':"\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sup>\<top>\<^sup>N b invr invar od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding do_while_gfp_invr_ndes_def    
  by (simp add: from_until_gfp_hoare_ndes_consequence[OF BH WF seq_step uimp_refl _ induct_step I0'])   
    
lemma do_while_lfp_invr_hoare_ndes_sp[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"     
  assumes induct_step:"\<And>st.\<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0':"\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom>\<^sub>N b invr invar od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding do_while_lfp_invr_ndes_def    
  by (simp add: from_until_lfp_hoare_ndes_consequence[OF BH WF seq_step uimp_refl _ induct_step I0'])   

lemma do_while_gfp_invr_vrt_hoare_ndes_sp[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"     
  assumes induct_step:"\<And>st.\<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0':"\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sup>\<top>\<^sup>N b invr invar vrt \<guillemotleft>R\<guillemotright> od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding do_while_gfp_invr_vrt_ndes_def    
  by (simp add: from_until_gfp_hoare_ndes_consequence[OF BH WF seq_step uimp_refl _ induct_step I0'])   
    
lemma do_while_lfp_invr_vrt_hoare_ndes_sp[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"     
  assumes induct_step:"\<And>st.\<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0':"\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"  
  shows  "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom>\<^sub>N b invr invar vrt \<guillemotleft>R\<guillemotright> od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"
  unfolding do_while_lfp_invr_vrt_ndes_def    
  by (simp add: from_until_lfp_hoare_ndes_consequence[OF BH WF seq_step uimp_refl _ induct_step I0'])   

lemma do_while_gfp_hoare_ndes_wp[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes PHI:"`\<not>b \<and> invar \<Rightarrow> q`"   
  assumes I0:"\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And>st.\<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"    
  shows  "\<lbrace>p\<rbrace>do body while\<^sup>\<top>\<^sup>N b od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding do_while_gfp_ndes_def
  by (simp add: I0 from_until_gfp_hoare_ndes_consequence[OF BH WF seq_step PHI _ induct_step uimp_refl])   
    
lemma do_while_lfp_hoare_ndes_wp[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes PHI:"`\<not>b \<and> invar \<Rightarrow> q`"   
  assumes I0:"\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And>st.\<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"    
  shows  "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom>\<^sub>N b od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding do_while_lfp_ndes_def
  by (simp add: I0 from_until_lfp_hoare_ndes_consequence[OF BH WF seq_step PHI _ induct_step uimp_refl])   

lemma do_while_gfp_invr_hoare_ndes_wp[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes PHI:"`\<not>b \<and> invar \<Rightarrow> q`"   
  assumes I0:"\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And>st.\<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"    
  shows  "\<lbrace>p\<rbrace>do body while\<^sup>\<top>\<^sup>N b invr invar od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding do_while_gfp_invr_ndes_def
  by (simp add: I0 from_until_gfp_hoare_ndes_consequence[OF BH WF seq_step PHI _ induct_step uimp_refl])   
    
lemma do_while_lfp_invr_hoare_ndes_wp[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes PHI:"`\<not>b \<and> invar \<Rightarrow> q`"   
  assumes I0:"\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And>st.\<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"    
  shows  "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom>\<^sub>N b invr invar od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding do_while_lfp_invr_ndes_def
  by (simp add: I0 from_until_lfp_hoare_ndes_consequence[OF BH WF seq_step PHI _ induct_step uimp_refl])   
     
lemma do_while_gfp_invr_vrt_hoare_ndes_wp[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes PHI:"`\<not>b \<and> invar \<Rightarrow> q`"   
  assumes I0:"\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And>st.\<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"    
  shows  "\<lbrace>p\<rbrace>do body while\<^sup>\<top>\<^sup>N b invr invar vrt \<guillemotleft>R\<guillemotright> od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding do_while_gfp_invr_vrt_ndes_def
  by (simp add: I0 from_until_gfp_hoare_ndes_consequence[OF BH WF seq_step PHI _ induct_step uimp_refl])   
    
lemma do_while_lfp_invr_vrt_hoare_ndes_wp[hoare_des]:
  assumes BH: "body is H1"
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>D"
  assumes PHI:"`\<not>b \<and> invar \<Rightarrow> q`"   
  assumes I0:"\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step:"\<And>st.\<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"    
  shows  "\<lbrace>p\<rbrace>do body while\<^sub>\<bottom>\<^sub>N b invr invar vrt \<guillemotleft>R\<guillemotright> od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding do_while_lfp_invr_vrt_ndes_def
  by (simp add: I0 from_until_lfp_hoare_ndes_consequence[OF BH WF seq_step PHI _ induct_step uimp_refl])   

subsection {*Hoare for for-loop*}   
(*TODO: ADD LAWS FOR FOR_loops*)    

lemma for_gfp_hoare_ndes_minimal:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;; incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows  "\<lbrace>p\<rbrace>for\<^sup>\<top>\<^sup>N (init, b, incr)do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"  
  unfolding for_gfp_ndes_def  
  by (simp add: from_until_gfp_hoare_ndes_minimal[OF seq_is_H1[OF BH INCRH] WF seq_step, where e=e] induct_step)  

lemma for_lfp_hoare_ndes_minimal:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;; incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows  "\<lbrace>p\<rbrace>for\<^sub>\<bottom>\<^sub>N (init, b, incr)do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"  
  unfolding for_lfp_ndes_def  
  by (simp add: from_until_lfp_hoare_ndes_minimal[OF seq_is_H1[OF BH INCRH] WF seq_step, where e=e] induct_step)  
    
lemma for_gfp_invr_hoare_ndes_minimal:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;; incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows  "\<lbrace>p\<rbrace>for\<^sup>\<top>\<^sup>N (init, b, incr) invr invar do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"  
  unfolding for_gfp_invr_ndes_def  
  by (simp add: from_until_gfp_hoare_ndes_minimal[OF seq_is_H1[OF BH INCRH] WF seq_step, where e=e] induct_step)  

lemma for_lfp_invr_hoare_ndes_minimal:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;; incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows  "\<lbrace>p\<rbrace>for\<^sub>\<bottom>\<^sub>N (init, b, incr) invr invar do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"  
  unfolding for_lfp_invr_ndes_def  
  by (simp add: from_until_lfp_hoare_ndes_minimal[OF seq_is_H1[OF BH INCRH] WF seq_step, where e=e] induct_step)  

lemma for_gfp_invr_vrt_hoare_ndes_minimal:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;; incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows  "\<lbrace>p\<rbrace>for\<^sup>\<top>\<^sup>N (init, b, incr) invr invar vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"  
  unfolding for_gfp_invr_vrt_ndes_def  
  by (simp add: from_until_gfp_hoare_ndes_minimal[OF seq_is_H1[OF BH INCRH] WF seq_step, where e=e] induct_step)  

lemma for_lfp_invr_vrt_hoare_ndes_minimal:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;; incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  shows  "\<lbrace>p\<rbrace>for\<^sub>\<bottom>\<^sub>N (init, b, incr) invr invar vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"  
  unfolding for_lfp_invr_vrt_ndes_def  
  by (simp add: from_until_lfp_hoare_ndes_minimal[OF seq_is_H1[OF BH INCRH] WF seq_step, where e=e] induct_step)  

lemma for_gfp_hoare_ndes_consequence:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0: "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;; incr\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0': "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows  "\<lbrace>p\<rbrace>for\<^sup>\<top>\<^sup>N (init, b, incr)do body od\<lbrace>q\<rbrace>\<^sub>D"  
  unfolding for_gfp_ndes_def  
  by (simp add: I0 from_until_gfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                             WF seq_step PHI _ induct_step I0'])

lemma for_lfp_hoare_ndes_consequence:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0: "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;; incr\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0': "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows  "\<lbrace>p\<rbrace>for\<^sub>\<bottom>\<^sub>N (init, b, incr)do body od\<lbrace>q\<rbrace>\<^sub>D"  
  unfolding for_lfp_ndes_def  
  by (simp add: I0 from_until_lfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                             WF seq_step PHI _ induct_step I0'])
                                                         
lemma for_gfp_invr_hoare_ndes_consequence:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0: "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;; incr\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0': "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows  "\<lbrace>p\<rbrace>for\<^sup>\<top>\<^sup>N (init, b, incr) invr invar do body od\<lbrace>q\<rbrace>\<^sub>D"  
  unfolding for_gfp_invr_ndes_def  
  by (simp add: I0 from_until_gfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                             WF seq_step PHI _ induct_step I0'])

lemma for_lfp_invr_hoare_ndes_consequence:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0: "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;; incr\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0': "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows  "\<lbrace>p\<rbrace>for\<^sub>\<bottom>\<^sub>N (init, b, incr) invr invar do body od\<lbrace>q\<rbrace>\<^sub>D"  
  unfolding for_lfp_invr_ndes_def  
  by (simp add: I0 from_until_lfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                             WF seq_step PHI _ induct_step I0'])
                                                         
lemma for_gfp_invr_vrt_hoare_ndes_consequence:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0: "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;; incr\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0': "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows  "\<lbrace>p\<rbrace>for\<^sup>\<top>\<^sup>N (init, b, incr) invr invar vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>q\<rbrace>\<^sub>D"  
  unfolding for_gfp_invr_vrt_ndes_def  
  by (simp add: I0 from_until_gfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                             WF seq_step PHI _ induct_step I0'])

lemma for_lfp_invr_vrt_hoare_ndes_consequence:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0: "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;; incr\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0': "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows  "\<lbrace>p\<rbrace>for\<^sub>\<bottom>\<^sub>N (init, b, incr) invr invar vrt \<guillemotleft>R\<guillemotright>do body od\<lbrace>q\<rbrace>\<^sub>D"  
  unfolding for_lfp_invr_vrt_ndes_def  
  by (simp add: I0 from_until_lfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                             WF seq_step PHI _ induct_step I0'])

lemma for_gfp_hoare_ndes_sp:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"   
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;; incr\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0': "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows  "\<lbrace>p\<rbrace>for\<^sup>\<top>\<^sup>N (init, b, incr)do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"  
  unfolding for_gfp_ndes_def  
  by (simp add: from_until_gfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                          WF seq_step uimp_refl _ induct_step I0'])
                                                         
lemma for_lfp_hoare_ndes_sp:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"   
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;; incr\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0': "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows  "\<lbrace>p\<rbrace>for\<^sub>\<bottom>\<^sub>N (init, b, incr)do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"  
  unfolding for_lfp_ndes_def  
  by (simp add: from_until_lfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                          WF seq_step uimp_refl _ induct_step I0'])
   
lemma for_gfp_invr_hoare_ndes_sp:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"   
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;; incr\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0': "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows  "\<lbrace>p\<rbrace>for\<^sup>\<top>\<^sup>N (init, b, incr) invr invar do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"  
  unfolding for_gfp_invr_ndes_def  
  by (simp add: from_until_gfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                          WF seq_step uimp_refl _ induct_step I0'])

lemma for_lfp_invr_hoare_ndes_sp:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"   
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;; incr\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0': "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows  "\<lbrace>p\<rbrace>for\<^sub>\<bottom>\<^sub>N (init, b, incr) invr invar do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"  
  unfolding for_lfp_invr_ndes_def  
  by (simp add:  from_until_lfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                           WF seq_step uimp_refl _ induct_step I0'])

lemma for_gfp_invr_vrt_hoare_ndes_sp:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"   
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;; incr\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0': "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows  "\<lbrace>p\<rbrace>for\<^sup>\<top>\<^sup>N (init, b, incr) invr invar vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"  
  unfolding for_gfp_invr_vrt_ndes_def  
  by (simp add: from_until_gfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                          WF seq_step uimp_refl _ induct_step I0'])
                                                         
lemma for_lfp_invr_vrt_hoare_ndes_sp:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"   
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;; incr\<lbrace>q' st\<rbrace>\<^sub>D"  
  assumes I0': "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows  "\<lbrace>p\<rbrace>for\<^sub>\<bottom>\<^sub>N (init, b, incr) invr invar vrt \<guillemotleft>R\<guillemotright>do body od\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>D"  
  unfolding for_lfp_invr_vrt_ndes_def  
  by (simp add: from_until_lfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                           WF seq_step uimp_refl _ induct_step I0'])

lemma for_gfp_hoare_ndes_wp:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0: "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;; incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"
  shows  "\<lbrace>p\<rbrace>for\<^sup>\<top>\<^sup>N (init, b, incr)do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding for_gfp_ndes_def     
  by (simp add: I0 from_until_gfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                           WF seq_step PHI  _ induct_step uimp_refl])
   
lemma for_lfp_hoare_ndes_wp:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0: "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;; incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"
  shows  "\<lbrace>p\<rbrace>for\<^sub>\<bottom>\<^sub>N (init, b, incr)do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding for_lfp_ndes_def     
  by (simp add: I0 from_until_lfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                           WF seq_step PHI  _ induct_step uimp_refl])

lemma for_gfp_invr_hoare_ndes_wp:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0: "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;; incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"
  shows  "\<lbrace>p\<rbrace>for\<^sup>\<top>\<^sup>N (init, b, incr) invr invar do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding for_gfp_invr_ndes_def     
  by (simp add: I0 from_until_gfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                           WF seq_step PHI  _ induct_step uimp_refl])
   
lemma for_lfp_invr_hoare_ndes_wp:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0: "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;; incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"
  shows  "\<lbrace>p\<rbrace>for\<^sub>\<bottom>\<^sub>N (init, b, incr) invr invar do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding for_lfp_invr_ndes_def     
  by (simp add: I0 from_until_lfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                           WF seq_step PHI  _ induct_step uimp_refl])
                                                       
lemma for_gfp_invr_vrt_hoare_ndes_wp:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0: "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;; incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"
  shows  "\<lbrace>p\<rbrace>for\<^sup>\<top>\<^sup>N (init, b, incr) invr invar vrt \<guillemotleft>R\<guillemotright>do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding for_gfp_invr_vrt_ndes_def     
  by (simp add: I0 from_until_gfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                           WF seq_step PHI  _ induct_step uimp_refl])
   
lemma for_lfp_invr_vrt_hoare_ndes_wp:
  assumes BH: "body is H1"
  assumes INCRH: "incr is H1"
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>D"  
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0: "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;; incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"
  shows  "\<lbrace>p\<rbrace>for\<^sub>\<bottom>\<^sub>N (init, b, incr) invr invar  vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>q\<rbrace>\<^sub>D"
  unfolding for_lfp_invr_vrt_ndes_def     
  by (simp add: I0 from_until_lfp_hoare_ndes_consequence [OF seq_is_H1[OF BH INCRH] 
                                                           WF seq_step PHI  _ induct_step uimp_refl])

end

