section \<open>Verification Condition Testing\<close>

theory utp_hoare_total
  imports algebraic_laws_designs
begin
named_theorems hoare_total

subsection {*Hoare triple definition*}

definition hoare_rd :: "'\<alpha> cond \<Rightarrow> ('f,'\<alpha>) hrel_cp \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>D") where
[upred_defs]:"\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>D = ((\<lceil>p\<rceil>\<^sub>C\<^sub>< \<and> $ok \<and> \<not>$abrupt \<and> $fault =\<^sub>u \<guillemotleft>None\<guillemotright> \<Rightarrow> 
                          \<lceil>r\<rceil>\<^sub>C\<^sub>> \<and> $ok\<acute> \<and> \<not>$abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright>) \<sqsubseteq> Q)"

lemma hoare_true [hoare_total]: 
  assumes "ok\<sharp>\<sharp>C" "abrupt\<sharp>\<sharp>C" "fault\<sharp>\<sharp>C"
  shows "\<lbrace>p\<rbrace>C\<lbrace>true\<rbrace>\<^sub>D"
  using assms oops

lemma hoare_false_t [hoare_total]: "\<lbrace>false\<rbrace>C\<lbrace>q\<rbrace>\<^sub>D"
  by rel_auto

subsection {*Precondition strengthening*}

lemma hoare_pre_str_t[hoare_total]:
  assumes "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" and "\<lbrace>p\<^sub>2\<rbrace>C\<lbrace>q\<rbrace>\<^sub>D"
  shows "\<lbrace>p\<^sub>1\<rbrace>C\<lbrace>q\<rbrace>\<^sub>D" 
  by (insert assms) rel_auto

subsection {*Post-condition weakening*}

lemma hoare_post_weak_t[hoare_total]:
  assumes "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>2\<rbrace>\<^sub>D" and "`q\<^sub>2 \<Rightarrow> q\<^sub>1`"
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>1\<rbrace>\<^sub>D" 
 by (insert assms) rel_auto

subsection {*Hoare and assertion logic*}

lemma hoare_r_conj_t [hoare_total]: 
  assumes"\<lbrace>p\<rbrace>C\<lbrace>r\<rbrace>\<^sub>D" and "\<lbrace>p\<rbrace>C\<lbrace>s\<rbrace>\<^sub>D"  
  shows "\<lbrace>p\<rbrace>C\<lbrace>r \<and> s\<rbrace>\<^sub>D"
  by (insert assms) rel_auto

subsection {*Hoare SKIP*}

lemma skip_hoare_r_t [hoare_total]: "\<lbrace>p\<rbrace>SKIP\<lbrace>p\<rbrace>\<^sub>D"
  by rel_auto

subsection {*Hoare for assignment*}

lemma assigns_hoare_r_t [hoare_total]: 
  assumes"`p \<Rightarrow> \<sigma> \<dagger> q`" 
  shows  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>C\<lbrace>q\<rbrace>\<^sub>D"
  by (insert assms) rel_auto

lemma assigns_hoare_r'_t [hoare_total]: "\<lbrace>\<sigma> \<dagger> p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>C\<lbrace>p\<rbrace>\<^sub>D"
  by rel_auto

subsection {*Hoare for Sequential Composition*}

lemma seq_hoare_r_t [hoare_total]: 
  assumes"\<lbrace>p\<rbrace>C\<^sub>1\<lbrace>s\<rbrace>\<^sub>D" and "\<lbrace>s\<rbrace>C\<^sub>2\<lbrace>r\<rbrace>\<^sub>D" 
  shows"\<lbrace>p\<rbrace>C\<^sub>1 ;; C\<^sub>2\<lbrace>r\<rbrace>\<^sub>D"
  by (insert assms) rel_blast

subsection {*Hoare for Conditional*}

lemma cond_hoare_r_t [hoare_total]: 
  assumes "\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>D" and "\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>D" 
  shows "\<lbrace>p\<rbrace>C\<^sub>1 \<triangleleft> \<lceil>b\<rceil>\<^sub>C\<^sub>< \<triangleright> C\<^sub>2\<lbrace>q\<rbrace>\<^sub>D"
  by (insert assms) rel_blast

subsection {*Hoare for assert*}

lemma assert_hoare_r_t [hoare_total]: 
  assumes "\<lbrace>c \<and> p\<rbrace>SKIP\<lbrace>q\<rbrace>\<^sub>D" and "\<lbrace>\<not>c \<and> p\<rbrace>\<bottom>\<^sub>D\<lbrace>q\<rbrace>\<^sub>D" 
  shows "\<lbrace>p\<rbrace> c\<^sub>\<bottom>\<^sub>C \<lbrace>q\<rbrace>\<^sub>D"
  by (insert assms) rel_blast

subsection {*Hoare for assume*}

lemma assume_hoare_r_t [hoare_total]: 
  assumes "\<lbrace>c \<and> p\<rbrace>SKIP\<lbrace>q\<rbrace>\<^sub>D" and "\<lbrace>\<not>c \<and> p\<rbrace>\<top>\<^sub>D\<lbrace>q\<rbrace>\<^sub>D" 
  shows "\<lbrace>p\<rbrace>c\<^sup>\<top>\<^sup>C\<lbrace>q\<rbrace>\<^sub>D"
  by (insert assms) rel_blast

subsection {*Hoare for While-loop*}

lemma while_hoare_r_t [hoare_total]:
  assumes "\<lbrace>p \<and> b \<rbrace> C\<lbrace>p\<rbrace>\<^sub>D"
  shows "\<lbrace>p\<rbrace>while b do C od\<lbrace>\<not>b \<and> p\<rbrace>\<^sub>D"
  using assms
  by (simp add: While_def hoare_rd_def, rule_tac lfp_lowerbound)(rel_blast) 


lemma while_hoare_r'_t [hoare_total]:
  assumes "\<lbrace>p \<and> b\<rbrace>C\<lbrace>p\<rbrace>\<^sub>D" and "`p \<and> \<not>b \<Rightarrow> q`"
  shows "\<lbrace>p\<rbrace>while b do C od\<lbrace>q\<rbrace>\<^sub>D"
  using assms
  by (metis hoare_post_weak_t while_hoare_r_t inf_commute)

lemma while_invr_hoare_r_t [hoare_total]:
  assumes "\<lbrace>p \<and> b\<rbrace>C\<lbrace>p\<rbrace>\<^sub>D" and "`pre \<Rightarrow> p`" and "`(\<not>b \<and> p) \<Rightarrow> post`"
  shows "\<lbrace>pre\<rbrace>while b invr p do C od\<lbrace>post\<rbrace>\<^sub>D"
  by (metis assms hoare_pre_str_t while_hoare_r'_t While_inv_def inf_commute)

end