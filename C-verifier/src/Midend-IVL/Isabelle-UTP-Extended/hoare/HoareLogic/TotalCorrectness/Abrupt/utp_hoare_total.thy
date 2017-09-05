section \<open>Verification Condition Testing\<close>

theory utp_hoare_total
  imports "../../../AlgebraicLaws/Abrupt/algebraic_laws_abrupt"
begin
named_theorems hoare_total

subsection {*Hoare triple definition*}

definition hoare_rd :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_cpa \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>A\<^sub>B\<^sub>R") where
[upred_defs]:"\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
  ((\<lceil>p\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<and> $ok \<and> \<not>$abrupt  \<Rightarrow> \<lceil>r\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>> \<and> $ok\<acute> \<and> \<not>$abrupt\<acute>) \<sqsubseteq> Q)"

lemma hoare_true_t [hoare_total]:
  shows "\<lbrace>p\<rbrace>(\<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> \<lceil>Q\<rceil>\<^sub>A\<^sub>B\<^sub>R)\<lbrace>true\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  apply pred_simp
  apply auto
 oops

lemma hoare_true_assisgns_abr_t [hoare_total]: 
  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R\<lbrace>true\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto

lemma hoare_true_skip_abr_t [hoare_total]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R\<lbrace>true\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto

lemma hoare_false_t [hoare_total]: 
  "\<lbrace>false\<rbrace>C\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto

subsection {*Precondition strengthening*}

lemma hoare_pre_str_t[hoare_total]:
  assumes "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" and "\<lbrace>p\<^sub>2\<rbrace>C\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  shows "\<lbrace>p\<^sub>1\<rbrace>C\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R" 
  by (insert assms) rel_auto

subsection {*Post-condition weakening*}

lemma hoare_post_weak_t[hoare_total]:
  assumes "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>2\<rbrace>\<^sub>A\<^sub>B\<^sub>R" and "`q\<^sub>2 \<Rightarrow> q\<^sub>1`"
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>1\<rbrace>\<^sub>A\<^sub>B\<^sub>R" 
 by (insert assms) rel_auto

subsection {*Hoare and assertion logic*}

lemma hoare_r_conj_t [hoare_total]: 
  assumes"\<lbrace>p\<rbrace>C\<lbrace>r\<rbrace>\<^sub>A\<^sub>B\<^sub>R" and "\<lbrace>p\<rbrace>C\<lbrace>s\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  shows "\<lbrace>p\<rbrace>C\<lbrace>r \<and> s\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by (insert assms) rel_auto

subsection {*Hoare SKIP*}

lemma skip_abr_hoare_r_t [hoare_total]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R\<lbrace>p\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto

subsection {*Hoare for assignment*}

lemma assigns_abr_hoare_r_t [hoare_total]: 
  assumes"`p \<Rightarrow> \<sigma> \<dagger> q`" 
  shows  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by (insert assms) rel_auto

lemma assigns_abr_hoare_r'_t [hoare_total]: 
  "\<lbrace>\<sigma> \<dagger> p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R\<lbrace>p\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto

lemma assigns_abr_floyd_r_t [hoare_total]:
  assumes \<open>vwb_lens x\<close>
  shows   \<open>\<lbrace>p\<rbrace>x \<Midarrow> e\<lbrace>\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrace>\<^sub>A\<^sub>B\<^sub>R\<close>
  apply (insert assms)
  apply rel_simp
  apply transfer
  apply (rule_tac x = \<open>get\<^bsub>xa\<^esub> more\<close> in exI)
  apply auto
  done

subsection {*Hoare for Sequential Composition*}

lemma seq_hoare_r_t [hoare_total]: 
  assumes"\<lbrace>p\<rbrace>C\<^sub>1\<lbrace>s\<rbrace>\<^sub>A\<^sub>B\<^sub>R" and "\<lbrace>s\<rbrace>C\<^sub>2\<lbrace>r\<rbrace>\<^sub>A\<^sub>B\<^sub>R" 
  shows"\<lbrace>p\<rbrace>C\<^sub>1 ;; C\<^sub>2\<lbrace>r\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by (insert assms, rel_auto) metis+ 

subsection {*Hoare for Conditional*}

lemma cond_hoare_r_t [hoare_total]: 
  assumes "\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R" and "\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R" 
  shows "\<lbrace>p\<rbrace>C\<^sub>1 \<triangleleft> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<triangleright> C\<^sub>2\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by (insert assms, rel_auto) metis+ 

lemma cond_abr_hoare_r_t [hoare_total]: 
  assumes "\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R" and "\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R" 
  shows "\<lbrace>p\<rbrace>bif b then C\<^sub>1 else C\<^sub>2 eif \<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by (insert assms, rel_auto) metis+ 

subsection {*Hoare for assert*}

lemma assert_hoare_r_t [hoare_total]: 
  assumes "\<lbrace>c \<and> p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R" and "\<lbrace>\<not>c \<and> p\<rbrace>\<bottom>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R" 
  shows "\<lbrace>p\<rbrace> c\<^sub>\<bottom>\<^sub>C \<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  unfolding rassert_abr_def using cond_abr_hoare_r_t assms
  by blast

subsection {*Hoare for assume*}

lemma assume_hoare_r_t [hoare_total]: 
  assumes "\<lbrace>c \<and> p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R" and "\<lbrace>\<not>c \<and> p\<rbrace>\<top>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R" 
  shows "\<lbrace>p\<rbrace>c\<^sup>\<top>\<^sup>C\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  unfolding rassume_abr_def using cond_abr_hoare_r_t assms
  by blast

subsection {*Hoare for While-loop*}

lemma while_hoare_r_t [hoare_total]:
  assumes "\<lbrace>p \<and> b \<rbrace> C\<lbrace>p\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  shows "\<lbrace>p\<rbrace>while b do C od\<lbrace>\<not>b \<and> p\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  using assms
  apply (simp add: While_def hoare_rd_def)
  apply (rule_tac gfp_upperbound)
  by (simp add: While_def hoare_rd_def, rule_tac lfp_lowerbound)(rel_blast) 

lemma while_hoare_r'_t [hoare_total]:
  assumes "\<lbrace>p \<and> b\<rbrace>C\<lbrace>p\<rbrace>\<^sub>A\<^sub>B\<^sub>R" and "`p \<and> \<not>b \<Rightarrow> q`"
  shows "\<lbrace>p\<rbrace>while b do C od\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  using assms
  by (metis hoare_post_weak_t while_hoare_r_t inf_commute)

lemma while_invr_hoare_r_t [hoare_total]:
  assumes "\<lbrace>p \<and> b\<rbrace>C\<lbrace>p\<rbrace>\<^sub>A\<^sub>B\<^sub>R" and "`pre \<Rightarrow> p`" and "`(\<not>b \<and> p) \<Rightarrow> post`"
  shows "\<lbrace>pre\<rbrace>while b invr p do C od\<lbrace>post\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by (metis assms hoare_pre_str_t while_hoare_r'_t While_inv_def inf_commute)

end