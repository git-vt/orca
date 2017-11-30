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
 \<open>\<lbrace>\<guillemotleft>vwb_lens x\<guillemotright> \<and> p\<rbrace>x :=\<^sub>D e\<lbrace>\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrace>\<^sub>D\<close>
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

lemma ndesign_mu_refine_intro:
  assumes "(C \<turnstile>\<^sub>n S) \<sqsubseteq> F(C \<turnstile>\<^sub>n S)" "` \<lceil>C\<rceil>\<^sub>D\<^sub>< \<Rightarrow> (\<mu>\<^sub>N F \<Leftrightarrow> \<nu>\<^sub>N F)`"
  shows "(C \<turnstile>\<^sub>n S) \<sqsubseteq> \<mu>\<^sub>N F"
proof -
   from assms have "(C \<turnstile>\<^sub>n S) \<sqsubseteq> \<nu>\<^sub>N F"
     by (simp add: ndesign_H1_H3 normal_design_theory_continuous.GFP_upperbound)
  with assms show ?thesis
    by (rel_auto, metis (no_types, lifting))
qed


lemma H3_design:
  assumes  "$ok\<acute> \<sharp> Q"
  shows "H3(\<lceil>P\<rceil>\<^sub>< \<turnstile> Q) = \<lceil>P\<rceil>\<^sub>< \<turnstile> Q"
  using assms
  by rel_blast
    
lemma design_is_H1_H3 [closure]:
  "$ok\<acute> \<sharp> Q \<Longrightarrow> (\<lceil>P\<rceil>\<^sub>< \<turnstile> Q) is \<^bold>N"
  by (simp add: H1_design H3_design Healthy_def')

lemma H3_rdesign:
  "H3(\<lceil>P\<rceil>\<^sub>< \<turnstile>\<^sub>r Q) = \<lceil>P\<rceil>\<^sub>< \<turnstile>\<^sub>r Q"
  by rel_blast

lemma reverse_impl_refine:
  "`Q2 \<Rightarrow> Q1`  = (Q1 \<sqsubseteq>  Q2)"
  by pred_auto    
lemma H1_H2_mu_refine_intro: "\<^bold>N(P) = (\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D (P))"
  thm H1_H3_impl_H2[unfolded Healthy_def, of P]
  oops

lemma 
  assumes "P is \<^bold>N"
  assumes "P \<sqsubseteq> F P"
  assumes "`\<lceil>pre\<^sub>D(P)\<rceil>\<^sub>D  \<Rightarrow> \<mu>\<^sub>N F \<Leftrightarrow> \<nu>\<^sub>N F`"  
  shows   "P \<sqsubseteq> \<mu>\<^sub>N F" 
  thm utp_designs.H1_H2_mu_refine_intro
  thm  H1_H2_eq_rdesign 
    thm H1_H3_eq_design
oops

 (*regarde sa*) 
  
lemma nu_refine_intro[]:
  assumes \<open>(C \<Rightarrow> S) \<sqsubseteq> F(C \<Rightarrow> S)\<close>
  shows \<open>(C \<Rightarrow> S) \<sqsubseteq> \<nu> F\<close>
  using assms
  by (simp add: lfp_lowerbound)
find_theorems name:"normal_design_theory_continuous.weak.LFP"    
thm nu_refine_intro
  
lemma mu_nd_rec_hoare_d_partial [hoare_des]:
  assumes  M: "Mono\<^bsub>uthy_order NDES\<^esub> F"  
  assumes  H: "F \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  assumes induct_step:
    "\<And> P. P is \<^bold>N \<Longrightarrow> \<lbrace>Pre\<rbrace> P \<lbrace>Post\<rbrace>\<^sub>D \<Longrightarrow> \<lbrace>Pre\<rbrace> F P \<lbrace>Post\<rbrace>\<^sub>D"  
  shows "\<lbrace>Pre\<rbrace>\<mu>\<^sub>N F \<lbrace>Post\<rbrace>\<^sub>D" 
  unfolding hoare_d_def
    
 proof -          
  {
    have "Pre  \<turnstile>\<^sub>n \<lceil>Post\<rceil>\<^sub>> \<sqsubseteq> \<mu>\<^sub>N F" 
      proof -
        from M H normal_design_theory_continuous.LFP_lemma3 mono_Monotone_utp_order
        have 1: "\<mu>\<^sub>N F \<sqsubseteq>  F (\<mu>\<^sub>N F)" by blast
        have 2:"F(Pre  \<turnstile>\<^sub>n \<lceil>Post\<rceil>\<^sub>>) \<sqsubseteq> F (\<mu>\<^sub>N F)"
          apply (rule Mono_utp_orderD [OF M, of "(\<mu>\<^sub>N F)" "(Pre  \<turnstile>\<^sub>n \<lceil>Post\<rceil>\<^sub>>)"])
            apply simp+
            apply rel_blast
        by simp    
   (* 
    hence 0: "(Pre \<and> (E, \<guillemotleft>e\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Post \<sqsubseteq> \<mu>\<^sub>N B"
      by rel_blast
    from M H normal_design_theory_continuous.LFP_lemma3 mono_Monotone_utp_order
    have 1: "\<mu>\<^sub>N B \<sqsubseteq>  B (\<mu>\<^sub>N B)"
      by blast
    from 0 1 have 2:"(Pre \<and> (E,\<guillemotleft>e\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Post \<sqsubseteq> B (\<mu>\<^sub>N B)"
      by simp
    have 3: "B ((Pre \<and> (E, \<guillemotleft>e\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Post) \<sqsubseteq> B (\<mu>\<^sub>N B)"
      by (auto intro: Mono_utp_orderD M 0)
    have 4:"(Pre \<and> E =\<^sub>u \<guillemotleft>e\<guillemotright>) \<turnstile>\<^sub>n Post \<sqsubseteq> \<dots>" 
      by (rule induct_step)
    show ?case
      using order_trans[OF 3 4] H M normal_design_theory_continuous.LFP_lemma2 dual_order.trans mono_Monotone_utp_order 
      by blast
  qed*)
   sorry 
  }
  thus ?thesis
    unfolding hoare_d_def .
qed
    
lemma mu_d_rec_hoare_d_t [hoare_des]:
  assumes WF: "wf R"
  assumes  M: "Mono\<^bsub>uthy_order NDES\<^esub> F"  
  assumes  H: "F \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  assumes induct_step:
    "\<And> st P. P is \<^bold>N \<Longrightarrow> \<lbrace>(Pre \<and> (E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>)\<rbrace> P \<lbrace>Post\<rbrace>\<^sub>D \<Longrightarrow> \<lbrace>Pre \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> F P \<lbrace>Post\<rbrace>\<^sub>D"  
  shows "\<lbrace>Pre\<rbrace>\<mu>\<^sub>N F \<lbrace>Post\<rbrace>\<^sub>D" 
  unfolding hoare_d_def 
  apply (rule ndesign_mu_wf_refine_intro[OF WF M H, of _ E])
  apply (rule induct_step[unfolded hoare_d_def])
  apply (simp add: ndesign_H1_H3)  
  apply pred_simp 
  done

lemma mu_d_rec_hoare_d_t'[hoare_des]:
  assumes WF: "wf R"
  assumes  M: "Mono\<^bsub>uthy_order NDES\<^esub> F"  
  assumes  H: "F \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"  
  assumes induct_step:
    "\<And> st P. P is \<^bold>N \<Longrightarrow> \<lbrace>(Pre \<and> (E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>)\<rbrace> P \<lbrace>Post\<rbrace>\<^sub>D \<Longrightarrow> \<lbrace>Pre \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> F P \<lbrace>Post\<rbrace>\<^sub>D"  
  assumes I0: "`Pre' \<Rightarrow> Pre  `"
  shows "\<lbrace>Pre'\<rbrace>\<mu>\<^sub>N F \<lbrace>Post\<rbrace>\<^sub>D" 
  apply (rule hoare_pre_str_d_t[OF I0])  
  apply (rule mu_d_rec_hoare_d_t[OF WF M H induct_step])
  apply assumption+
  done      
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

lemma while_hoare_d_t [hoare_des]:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`"
  assumes BH :" body is H1"  
  assumes induct_step:"\<And> st. \<lbrace>b \<and> I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>I \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  assumes PHI:"`(\<not> b \<and> I) \<Rightarrow> Post`"  
  shows "\<lbrace>Pre\<rbrace>while\<^sub>D b invr I do body od\<lbrace>Post\<rbrace>\<^sub>D"
proof -
  have M: "mono (\<lambda>X. bif\<^sub>D b then body ;; X else SKIP\<^sub>D eif)"
    by (auto intro: monoI seqr_mono cond_mono) 
  have H: "(\<lambda>X. bif\<^sub>D b then body ;; X else SKIP\<^sub>D eif) \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H" 
    using BH
    apply pred_simp apply rel_simp  apply smt done   
  from mono_Monotone_utp_order [OF M, of "\<H>\<^bsub>DES\<^esub>"] H
          design_theory_continuous.LFP_weak_unfold  
  have M_des: "Mono\<^bsub>uthy_order DES\<^esub>(\<lambda>X. bif\<^sub>D b then body ;; X else SKIP\<^sub>D eif)"
    by auto
  have *:"(I \<turnstile>\<^sub>n \<lceil>Post\<rceil>\<^sub>>  \<sqsubseteq> \<mu>\<^sub>D (\<lambda>X. bif\<^sub>D b then body ;; X else SKIP\<^sub>D eif))"  
     unfolding ndesign_def rdesign_def
    apply (rule design_mu_wf_refine_intro[where Pre="\<lceil>I\<rceil>\<^sub>D\<^sub><" and E = "E", OF WF M_des H])  
    apply pred_simp
   apply pred_simp
  apply (rule  cond_refine_des)
    subgoal for st
      apply (rule_tac seq_refine_unrest_des[where s= "I \<and> (E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>" ])
            apply pred_simp
           apply pred_simp
       apply (rule order_trans[OF induct_step[unfolded hoare_d_def],  where st1 = st]) 
        apply pred_simp
        apply pred_simp
      done
     apply (rule skip_refine_des)      
     using PHI
       apply rel_blast
  done    
  show ?thesis    
  unfolding  hoare_d_def While_inv_des_def While_lfp_des_def
     unfolding  hoare_d_def While_inv_ndes_def While_lfp_ndes_def
    by (rule hoare_pre_str_d_t[unfolded hoare_d_def ,of _ "I", OF I0 *]) 
qed
  
lemma while_hoare_d [hoare_safe]:
  assumes "\<lbrace>p \<and> b\<rbrace>C\<lbrace>p\<rbrace>\<^sub>D"
  shows "\<lbrace>p\<rbrace>while\<^sub>N b do C od\<lbrace>\<not>b \<and> p\<rbrace>\<^sub>D"
   apply (simp add: While_lfp_ndes_def )
   apply (rule mu_d_rec_hoare_d_t')
   oops
     
lemma if_d_mono:
  "mono (\<lambda>X. bif\<^sub>D b then P ;; X else Q eif)"
  by (auto intro: monoI seqr_mono cond_mono) 

lemma blah1:
  assumes 1: "P is H1"
  and     2: "Q is \<^bold>N"
  shows " (P;; Q) is \<^bold>N" 
proof -
 from 1 2 have "\<lfloor>pre\<^sub>D Q\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D Q = Q"
    by (metis ndesign_form)
  then show ?thesis
    using 1 2 
    by (metis (no_types) H1_H2_impl_H1 H1_H3_impl_H2 H3_def H3_ndesign Healthy_def seqr_assoc weaker_seq_r_H1_H2_closed)
qed

lemma blah2:
  assumes 1: "P is H1"
  and     2: "Q is \<^bold>N"
  shows "(\<lambda>X. bif\<^sub>D b then P ;; X else Q eif) \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"   
  proof (rule  FuncSet.Pi_I)
    fix x :: "('b, 'a) rel_des"
    assume 11: "x \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
    have ndesign_split: "\<forall>u. \<not> (u is \<^bold>N) \<or> \<lfloor>pre\<^sub>D u::'a hrel\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D u = u"
      using ndesign_form by blast
    have seq_is_ndesign: "P ;; x is (\<lambda>u. \<^bold>N (u::'a hrel_des))"
      using 11 1 blah1 by blast
    then have "bif\<^sub>D b then P ;; x else Q eif = 
               bif\<^sub>D b then \<lfloor>pre\<^sub>D (P ;; x)::'a hrel\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D (P ;; x) else \<lfloor>pre\<^sub>D Q\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D Q eif"
      using ndesign_split 2 by presburger
    then have H3_if_d_idemp: "H3 bif\<^sub>D b then P ;; x else Q eif = bif\<^sub>D b then P ;; x else Q eif"
      by (simp add: H3_ndesign ndesign_dcond)
    have H3_seq_idemp: "(P ;; x::'a hrel_des) = H3 (P ;; x)"
      using seq_is_ndesign ndesign_split by (metis (no_types) H3_ndesign)
    have "Q = H3 Q"
      using ndesign_split 2 by (metis (no_types) H3_ndesign)
    then show "bif\<^sub>D b then P ;; x else Q eif \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
      using H3_seq_idemp H3_if_d_idemp seq_is_ndesign 2 by (simp add: H1_def Healthy_def' spec_cond_dist)
  qed

lemma while_hoare_ndesign_t [hoare_des]:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`"
  assumes BH :"body is H1"  
  assumes induct_step:"\<And> st. \<lbrace>b \<and> I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>I \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  assumes PHI:"`(\<not> b \<and> I) \<Rightarrow> Post`"  
  shows "\<lbrace>Pre\<rbrace>while\<^sub>N b invr I do body od\<lbrace>Post\<rbrace>\<^sub>D"
proof -
  have H: "(\<lambda>X. bif\<^sub>D b then body ;; X else SKIP\<^sub>D eif) \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H" 
    using BH
    apply pred_simp apply rel_simp  apply smt done   
  from mono_Monotone_utp_order [OF if_d_mono, of "\<H>\<^bsub>NDES\<^esub>" b body SKIP\<^sub>D] H
    normal_design_theory_continuous.LFP_weak_unfold  
  have M_des: "Mono\<^bsub>uthy_order NDES\<^esub>(\<lambda>X. bif\<^sub>D b then body ;; X else SKIP\<^sub>D eif)"
    by simp
  have *:"(I \<turnstile>\<^sub>n \<lceil>Post\<rceil>\<^sub>>  \<sqsubseteq> \<mu>\<^sub>N (\<lambda>X. bif\<^sub>D b then body ;; X else SKIP\<^sub>D eif))"
  proof (rule ndesign_mu_wf_refine_intro[where Pre="I" and E = "E", OF WF M_des H])
    { fix st
      have if_false_part: "(\<not> \<lceil>b\<rceil>\<^sub>D\<^sub>< \<and> \<lceil>I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rceil>\<^sub>D\<^sub><) \<turnstile> \<lceil>Post\<rceil>\<^sub>D\<^sub>> \<sqsubseteq> SKIP\<^sub>D"     
        using PHI by rel_blast
      have seq_left_part: "(\<lceil>b\<rceil>\<^sub>D\<^sub>< \<and> \<lceil>I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rceil>\<^sub>D\<^sub><) \<turnstile> \<lceil>I \<and> (E, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rceil>\<^sub>D\<^sub>> \<sqsubseteq> body"        
      proof (rule order_trans[OF induct_step[unfolded hoare_d_def],  where st1 = st]) 
        show "(\<lceil>b\<rceil>\<^sub>D\<^sub>< \<and> \<lceil>I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rceil>\<^sub>D\<^sub><) \<turnstile> \<lceil>I \<and> (E, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rceil>\<^sub>D\<^sub>> \<sqsubseteq>
              (b \<and> I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n \<lceil>I \<and> (E, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rceil>\<^sub>>"
          by pred_simp
      qed    
      have seq_right_part: 
        "\<lceil>I \<and> (E, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rceil>\<^sub>D\<^sub>< \<turnstile> \<lceil>Post\<rceil>\<^sub>D\<^sub>> \<sqsubseteq> \<lceil>I \<and> (E, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rceil>\<^sub>D\<^sub>< \<turnstile> \<lceil>Post\<rceil>\<^sub>D\<^sub>>" 
        by pred_simp 
      from seq_left_part seq_right_part 
      have seq_both_sides:
        "(\<lceil>b\<rceil>\<^sub>D\<^sub>< \<and> \<lceil>I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rceil>\<^sub>D\<^sub><) \<turnstile> \<lceil>Post\<rceil>\<^sub>D\<^sub>> \<sqsubseteq> body ;; (\<lceil>I \<and> (E, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rceil>\<^sub>D\<^sub>< \<turnstile> \<lceil>Post\<rceil>\<^sub>D\<^sub>>)"
        by (rule_tac seq_refine_unrest_des[where s= "I \<and> (E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>" ],simp_all add: unrest)
      from seq_both_sides  if_false_part   
      have "(I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n \<lceil>Post\<rceil>\<^sub>> \<sqsubseteq> bif\<^sub>D b then body ;;
            ((I \<and> (E, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n \<lceil>Post\<rceil>\<^sub>>) else SKIP\<^sub>D eif"
        unfolding ndesign_def rdesign_def
        by (rule  cond_refine_des)
      thus "(I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n \<lceil>Post\<rceil>\<^sub>> \<sqsubseteq> bif\<^sub>D b then body ;;
            ((I \<and> (E, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n \<lceil>Post\<rceil>\<^sub>>) else SKIP\<^sub>D eif"  
        unfolding ndesign_def rdesign_def . 
    }
  qed   
  show ?thesis    
    unfolding hoare_d_def While_inv_ndes_def While_lfp_ndes_def
    by (rule hoare_pre_str_d_t[unfolded hoare_d_def , OF I0 *]) 
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

lemma while_vrt_hoare_ndesign_t' [hoare_des]:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`"
  assumes BH :" body is H1"  
  assumes induct_step:"\<And> st. \<lbrace>b \<and> I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>I \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  assumes PHI:"`(\<not> b \<and> I) \<Rightarrow> Post`"  
  shows "\<lbrace>Pre\<rbrace>while\<^sub>N b invr I vrt \<guillemotleft>R\<guillemotright> do body od\<lbrace>Post\<rbrace>\<^sub>D"
  using assms while_hoare_ndesign_t[of R Pre I body b E Post]
  by (simp add: While_inv_ndes_def While_inv_vrt_ndes_def)    
    
end