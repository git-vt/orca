theory utp_hoare_des

imports "../../../../utp/utp_rec_total_des"

begin
section {*Hoare logic for designs*}  
named_theorems hoare_des

subsection {*Hoare triple definition*}

definition hoare_d :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>D") where
[upred_defs]:"\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>D = ((p \<turnstile>\<^sub>n \<lceil>r\<rceil>\<^sub>>) \<sqsubseteq> Q)"

lemma hoare_true_assisgns_d_t [hoare_des]: 
  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>D\<lbrace>true\<rbrace>\<^sub>D"
  by rel_auto

lemma hoare_true_skip_d_t [hoare_des]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>D\<lbrace>true\<rbrace>\<^sub>D"
  by rel_auto

lemma hoare_false_d_t [hoare_des]: 
  "\<lbrace>false\<rbrace>C\<lbrace>q\<rbrace>\<^sub>D"
  by rel_auto

subsection {*Precondition weakening*}

lemma hoare_pre_str_d_t[hoare_des]:
  assumes "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" and "\<lbrace>p\<^sub>2\<rbrace>C\<lbrace>q\<rbrace>\<^sub>D"
  shows "\<lbrace>p\<^sub>1\<rbrace>C\<lbrace>q\<rbrace>\<^sub>D" 
  by (insert assms) rel_auto

subsection {*Post-condition strengthening*}

lemma hoare_post_weak_d_t[hoare_des]:
  assumes "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>2\<rbrace>\<^sub>D" and "`q\<^sub>2 \<Rightarrow> q\<^sub>1`"
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>1\<rbrace>\<^sub>D" 
 by (insert assms) rel_auto

subsection {*Hoare and assertion logic*}

lemma hoare_d_conj_d_t [hoare_des]: 
  assumes"\<lbrace>p\<rbrace>C\<lbrace>r\<rbrace>\<^sub>D" and "\<lbrace>p\<rbrace>C\<lbrace>s\<rbrace>\<^sub>D"
  shows "\<lbrace>p\<rbrace>C\<lbrace>r \<and> s\<rbrace>\<^sub>D"
  by (insert assms) rel_auto

subsection {*Hoare SKIP*}

lemma skip_d_hoare_d_t [hoare_des]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>D\<lbrace>p\<rbrace>\<^sub>D"
  by rel_auto

subsection {*Hoare for assignment*}

lemma assigns_d_hoare_d_t [hoare_des]: 
  assumes"`p \<Rightarrow> \<sigma> \<dagger> q`" 
  shows  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>D\<lbrace>q\<rbrace>\<^sub>D"
  by (insert assms) rel_auto

lemma assigns_d_hoare_d'_t [hoare_des]: 
  "\<lbrace>\<sigma> \<dagger> p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>D\<lbrace>p\<rbrace>\<^sub>D"
  by rel_auto

lemma assigns_d_floyd_d_t [hoare_des]:
  assumes "vwb_lens x"
  shows \<open>\<lbrace>p\<rbrace>x :=\<^sub>D e\<lbrace>\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrace>\<^sub>D\<close>
    using assms
  apply rel_simp
  apply transfer
  apply (rule_tac x = \<open>get\<^bsub>x\<^esub> more\<close> in exI)
  apply auto
  done

subsection {*Hoare for Sequential Composition*}

lemma seq_hoare_d_t [hoare_des]: 
  assumes"\<lbrace>p\<rbrace>C\<^sub>1\<lbrace>s\<rbrace>\<^sub>D" and "\<lbrace>s\<rbrace>C\<^sub>2\<lbrace>r\<rbrace>\<^sub>D" 
  shows"\<lbrace>p\<rbrace>C\<^sub>1 ;; C\<^sub>2\<lbrace>r\<rbrace>\<^sub>D"
  by (insert assms, rel_auto) metis+ 

subsection {*Hoare for Conditional*}

lemma cond_d_hoare_d_t [hoare_des]: 
  assumes "\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>D" and "\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>D" 
  shows "\<lbrace>p\<rbrace>C\<^sub>1 \<triangleleft> \<lceil>b\<rceil>\<^sub>D\<^sub>< \<triangleright> C\<^sub>2\<lbrace>q\<rbrace>\<^sub>D"
  by (insert assms, rel_auto) metis+ 

lemma cond_d_hoare_d'_t [hoare_des]: 
  assumes "\<lbrace>p\<rbrace>\<lceil>b\<rceil>\<^sub>D\<^sub>< \<and> C\<^sub>1\<lbrace>q\<rbrace>\<^sub>D" and "\<lbrace>p\<rbrace>\<lceil>\<not>b\<rceil>\<^sub>D\<^sub>< \<and> C\<^sub>2\<lbrace>q\<rbrace>\<^sub>D" 
  shows "\<lbrace>p\<rbrace>bif\<^sub>D b then C\<^sub>1 else C\<^sub>2 eif \<lbrace>q\<rbrace>\<^sub>D"
  by (insert assms, rel_auto) 
    
lemma cond_d_hoare_d'_t':
  assumes \<open>\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>D\<close> and \<open>\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>s\<rbrace>\<^sub>D\<close>
  shows \<open>\<lbrace>p\<rbrace>bif\<^sub>D b then C\<^sub>1 else C\<^sub>2 eif\<lbrace>q \<or> s\<rbrace>\<^sub>D\<close>
  by (insert assms, rel_auto) metis+
    
subsection {*Hoare for recursion*}
  
lemma nu_ndesign_rec_hoare_d_partial [hoare_des]:
  assumes induct_step:
    "\<And> P. P is \<^bold>N \<Longrightarrow> \<lbrace>Pre\<rbrace> P \<lbrace>Post\<rbrace>\<^sub>D \<Longrightarrow> \<lbrace>Pre\<rbrace> F P \<lbrace>Post\<rbrace>\<^sub>D"  
  shows "\<lbrace>Pre\<rbrace>\<nu>\<^sub>N F\<lbrace>Post\<rbrace>\<^sub>D" 
proof -
  have is_ndesign: "Pre \<turnstile>\<^sub>n \<lceil>Post\<rceil>\<^sub>> is \<^bold>N"
    using ndesign_H1_H3[of Pre "\<lceil>Post\<rceil>\<^sub>>"]
    by simp 
  also have fp_refine_spec:"Pre \<turnstile>\<^sub>n \<lceil>Post\<rceil>\<^sub>> \<sqsubseteq> F (Pre \<turnstile>\<^sub>n \<lceil>Post\<rceil>\<^sub>>)"
    by (rule induct_step[unfolded hoare_d_def, OF  is_ndesign, simplified]) 
  ultimately show ?thesis 
    unfolding hoare_d_def
    by (rule normal_design_theory_continuous.GFP_upperbound)
qed

lemma mu_d_rec_hoare_d_t [hoare_des]:
  assumes WF: "wf R"
  assumes  M: "Mono\<^bsub>uthy_order NDES\<^esub> F"  
  assumes  H: "F \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  assumes induct_step:
    "\<And>st P. P is \<^bold>N \<Longrightarrow> \<lbrace>(Pre \<and> (E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>)\<rbrace> P \<lbrace>Post\<rbrace>\<^sub>D \<Longrightarrow> \<lbrace>Pre \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> F P \<lbrace>Post\<rbrace>\<^sub>D"  
  shows "\<lbrace>Pre\<rbrace>\<mu>\<^sub>N F \<lbrace>Post\<rbrace>\<^sub>D" 
proof -
  { fix e 
    have "(Pre \<and> E =\<^sub>u \<guillemotleft>e\<guillemotright>) \<turnstile>\<^sub>n \<lceil>Post\<rceil>\<^sub>> \<sqsubseteq> F ((Pre \<and> (E, \<guillemotleft>e\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n \<lceil>Post\<rceil>\<^sub>>)"
      by (rule induct_step[unfolded hoare_d_def, 
                           OF ndesign_H1_H3[of "(Pre \<and> (E, \<guillemotleft>e\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>)" "\<lceil>Post\<rceil>\<^sub>>"] order_refl]) 
  }
  then show ?thesis  
    unfolding hoare_d_def 
    by (rule ndesign_mu_wf_refine_intro[OF WF M H, of _ E])
qed

  
lemma mu_d_rec_hoare_d_t'[hoare_des]:
  assumes WF: "wf R"
  assumes  M: "Mono\<^bsub>uthy_order NDES\<^esub> F"  
  assumes  H: "F \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"  
  assumes induct_step:
    "\<And> st P. P is \<^bold>N \<Longrightarrow> \<lbrace>(Pre \<and> (E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>)\<rbrace> P \<lbrace>Post\<rbrace>\<^sub>D \<Longrightarrow> \<lbrace>Pre \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> F P \<lbrace>Post\<rbrace>\<^sub>D"  
  assumes I0: "`Pre' \<Rightarrow> Pre`"
  shows "\<lbrace>Pre'\<rbrace>\<mu>\<^sub>N F \<lbrace>Post\<rbrace>\<^sub>D" 
  by (rule hoare_pre_str_d_t[OF I0 mu_d_rec_hoare_d_t[OF WF M H induct_step], simplified])
          
subsection {*Hoare for frames*}

lemma antiframe_hoare_d_t[hoare_des]:
  assumes "vwb_lens a"
  assumes "a \<sharp> r" 
  assumes "a \<natural> q"    
  assumes "\<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>D"  
  shows "\<lbrace>p \<and> r\<rbrace> antiframe\<^sub>D a P \<lbrace>q \<and> r\<rbrace>\<^sub>D"
  using assms by (rel_simp)

lemma antiframe_goare_d_t_stronger[hoare_des]:
  assumes "vwb_lens a"
  assumes "a \<sharp> r" 
  assumes "a \<natural> q"    
  assumes "\<lbrace>p \<and> r\<rbrace>P\<lbrace>q\<rbrace>\<^sub>D"  
  shows "\<lbrace>p \<and> r\<rbrace> antiframe\<^sub>D a P \<lbrace>q \<and> r\<rbrace>\<^sub>D"
  using assms by (rel_simp)
        
lemma frame_hoare_d_t[hoare_des]:
  assumes "vwb_lens a"
  assumes "a \<natural> r" 
  assumes "a \<sharp> q"    
  assumes "\<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>D"  
  shows "\<lbrace>p \<and> r\<rbrace> frame\<^sub>D a P \<lbrace>q \<and> r\<rbrace>\<^sub>D"
  using assms by (rel_simp)  

lemma frame_hoare_d_t_stronger[hoare_des]:
  assumes "vwb_lens a"
  assumes "a \<natural> r" 
  assumes "a \<sharp> q"    
  assumes "\<lbrace>p \<and> r\<rbrace>P\<lbrace>q\<rbrace>\<^sub>D"  
  shows "\<lbrace>p \<and> r\<rbrace> frame\<^sub>D a P \<lbrace>q \<and> r\<rbrace>\<^sub>D"
  using assms by (rel_simp) 
    
subsection {*Hoare for While-loop*}   
    
lemma while_hoare_ndesign_t [hoare_des]:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`"
  assumes BH :"body is H1"  
  assumes induct_step:"\<And> st. \<lbrace>b \<and> I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>I \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  assumes PHI:"`(\<not> b \<and> I) \<Rightarrow> Post`"  
  shows "\<lbrace>Pre\<rbrace>while\<^sub>N b invr I do body od\<lbrace>Post\<rbrace>\<^sub>D"
  unfolding  While_inv_ndes_def While_lfp_ndes_def
proof (rule mu_d_rec_hoare_d_t'[OF WF _ _ _ I0, where  E = "E"], goal_cases)
  case 1
  then show ?case by (rule mono_Monotone_utp_order[OF if_d_mono, of "\<H>\<^bsub>NDES\<^esub>" b body SKIP\<^sub>D])
next
  case 2
  then show ?case by (rule weaker_if_d_seq_r_H1_H3_closed[OF BH skip_d_is_H1_H3])
next
  case (3 e P)
  assume P_is_N: "P is \<^bold>N " 
  assume P_is_wf:"\<lbrace>I \<and> (E, \<guillemotleft>e\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>P\<lbrace>Post\<rbrace>\<^sub>D"  
  show ?case
    proof (rule cond_d_hoare_d_t, goal_cases)
      case 1
      then show ?case
        proof (rule seq_hoare_d_t[of _ _ "I \<and>(E,\<guillemotleft>e\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>"], goal_cases)
          case 1
          then show ?case using induct_step by assumption
        next
          case 2
          then show ?case using P_is_wf by assumption 
        qed

    next
      case 2
      then show ?case 
        proof (rule hoare_pre_str_d_t[of _ Post], goal_cases)
          case 1
          then show ?case using PHI by pred_simp 
        next
          case 2
          then show ?case by (rule skip_d_hoare_d_t) 
        qed
    qed
qed
  
lemma while_vrt_hoare_ndesign_t [hoare_des]:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`"
  assumes BH :" body is H1"  
  assumes induct_step:"\<And> st. \<lbrace>b \<and> I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>I \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  assumes PHI:"`(\<not> b \<and> I) \<Rightarrow> Post`"  
  shows "\<lbrace>Pre\<rbrace>while\<^sub>N b invr I vrt E do body od\<lbrace>Post\<rbrace>\<^sub>D"
  using assms while_hoare_ndesign_t[of R Pre I body b E Post]
  by (simp add: While_inv_ndes_def While_inv_vrt_ndes_def)

lemma while_inv_vrt_hoare_ndesign_t' [hoare_des]:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`"
  assumes BH :" body is H1"  
  assumes induct_step:"\<And> st. \<lbrace>b \<and> I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>I \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  assumes PHI:"`(\<not> b \<and> I) \<Rightarrow> Post`"  
  shows "\<lbrace>Pre\<rbrace>while\<^sub>N b invr I vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>Post\<rbrace>\<^sub>D"
  using assms while_hoare_ndesign_t[of R Pre I body b E Post]
  by (simp add: While_inv_ndes_def While_inv_vrt_ndes_def)    
    
end