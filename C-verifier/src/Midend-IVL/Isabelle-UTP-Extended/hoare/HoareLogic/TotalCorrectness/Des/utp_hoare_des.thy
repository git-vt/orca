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

lemma hoare_r_conj_d_t [hoare_des]: 
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
  assumes \<open>vwb_lens x\<close>
  shows \<open>\<lbrace>p\<rbrace>x :=\<^sub>D e\<lbrace>\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrace>\<^sub>D\<close>
  apply (insert assms)
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

    
subsection {*Helpers*}
lemma cond_refine_des: 
  assumes "((b \<and> p) \<turnstile> q) \<sqsubseteq> C\<^sub>1" and "((\<not>b \<and> p) \<turnstile> q)\<sqsubseteq> C\<^sub>2" 
  shows "(p \<turnstile> q) \<sqsubseteq> (C\<^sub>1 \<triangleleft> b \<triangleright> C\<^sub>2)"
  using assms by rel_blast
    
lemma seq_refine_unrest_des:
  assumes "out\<alpha> \<sharp> p" "in\<alpha> \<sharp> q"
  assumes "(p \<turnstile> \<lceil>s\<rceil>\<^sub>D\<^sub>>) \<sqsubseteq> P" and "(\<lceil>s\<rceil>\<^sub>D\<^sub>< \<turnstile> q) \<sqsubseteq> Q"
  shows "(p \<turnstile> q) \<sqsubseteq> (P ;; Q)"
  apply (insert assms)  
  apply rel_auto
   apply metis+ 
  done
    
lemma skip_refine_des:
  "`(SKIP\<^sub>D \<Rightarrow> (p \<turnstile> q))` \<Longrightarrow> (p \<turnstile> q) \<sqsubseteq> SKIP\<^sub>D"
  by pred_auto   
    
subsection {*Hoare for While-loop*}   

lemma while_hoare_r_t [hoare_des]:
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


lemma while_hoare_ndesign_t [hoare_des]:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`"
  assumes BH :" body is H1"  
  assumes induct_step:"\<And> st. \<lbrace>b \<and> I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>I \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D"  
  assumes PHI:"`(\<not> b \<and> I) \<Rightarrow> Post`"  
  shows "\<lbrace>Pre\<rbrace>while\<^sub>N b invr I do body od\<lbrace>Post\<rbrace>\<^sub>D"
proof -
  have M: "mono (\<lambda>X. bif\<^sub>D b then body ;; X else SKIP\<^sub>D eif)"
    by (auto intro: monoI seqr_mono cond_mono) 
  have H: "(\<lambda>X. bif\<^sub>D b then body ;; X else SKIP\<^sub>D eif) \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H" 
    using BH
    apply pred_simp apply rel_simp  apply smt done   
  from mono_Monotone_utp_order [OF M, of "\<H>\<^bsub>NDES\<^esub>"] H
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
    unfolding  hoare_d_def While_inv_ndes_def While_lfp_ndes_def
    by (rule hoare_pre_str_d_t[unfolded hoare_d_def ,of _ "I", OF I0 *]) 
qed

end