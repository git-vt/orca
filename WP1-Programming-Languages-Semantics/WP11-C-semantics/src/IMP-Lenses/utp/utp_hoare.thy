subsection {* Relational Hoare calculus *}

theory utp_hoare
imports "../Algebraic_Laws"
begin

named_theorems hoare

subsection {*Hoare triple definition*}

text {*A Hoare triple is represented by a pre-condition @{text P} a post-condition @{text Q}
       and a program @{text C}. It says whenever the pre-condition @{text P} holds on the initial state
       then the post-condition @{text Q} must hold on the final state and this 
       after the execution of the program @{text C}.*}

definition hoare_r :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>u") where
"\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u = ((\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>r\<rceil>\<^sub>>) \<sqsubseteq> Q)"

declare hoare_r_def [upred_defs]

lemma hoare_true [hoare]: "\<lbrace>p\<rbrace>C\<lbrace>true\<rbrace>\<^sub>u"
  by rel_auto

lemma hoare_false [hoare]: "\<lbrace>false\<rbrace>C\<lbrace>q\<rbrace>\<^sub>u"
  by rel_auto

subsection {*Hoare for Consequence*}

lemma hoare_r_conseq [hoare]: 
  assumes "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" and "\<lbrace>p\<^sub>2\<rbrace>C\<lbrace>q\<^sub>2\<rbrace>\<^sub>u" and "`q\<^sub>2 \<Rightarrow> q\<^sub>1`" 
  shows   "\<lbrace>p\<^sub>1\<rbrace>C\<lbrace>q\<^sub>1\<rbrace>\<^sub>u"
  by (insert assms) rel_auto

subsection {*Precondition strengthening*}

lemma hoare_pre_str[hoare]:
  assumes "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" and "\<lbrace>p\<^sub>2\<rbrace>C\<lbrace>q\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<^sub>1\<rbrace>C\<lbrace>q\<rbrace>\<^sub>u" 
  by (insert assms) rel_auto

subsection {*Post-condition weakening*}

lemma hoare_post_weak[hoare]:
  assumes "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>2\<rbrace>\<^sub>u" and "`q\<^sub>2 \<Rightarrow> q\<^sub>1`"
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>1\<rbrace>\<^sub>u" 
 by (insert assms) rel_auto

subsection {*Hoare and assertion logic*}

lemma hoare_r_conj [hoare]: 
  assumes"\<lbrace>p\<rbrace>C\<lbrace>r\<rbrace>\<^sub>u" and "\<lbrace>p\<rbrace>C\<lbrace>s\<rbrace>\<^sub>u"  
  shows "\<lbrace>p\<rbrace>C\<lbrace>r \<and> s\<rbrace>\<^sub>u"
  by (insert assms) rel_auto

subsection {*Hoare SKIP*}

lemma skip_hoare_r [hoare]: "\<lbrace>p\<rbrace>SKIP\<lbrace>p\<rbrace>\<^sub>u"
  by rel_auto

subsection {*Hoare for assignment*}

lemma assigns_hoare_r [hoare]: 
  assumes"`p \<Rightarrow> \<sigma> \<dagger> q`" 
  shows  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>a\<lbrace>q\<rbrace>\<^sub>u"
  by (insert assms) rel_auto

lemma assigns_hoare_r' [hoare]: "\<lbrace>\<sigma> \<dagger> p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>a\<lbrace>p\<rbrace>\<^sub>u"
  by rel_auto

subsection {*Hoare for Sequential Composition*}

lemma seq_hoare_r [hoare]: 
  assumes"\<lbrace>p\<rbrace>C\<^sub>1\<lbrace>s\<rbrace>\<^sub>u" and "\<lbrace>s\<rbrace>C\<^sub>2\<lbrace>r\<rbrace>\<^sub>u" 
  shows"\<lbrace>p\<rbrace>C\<^sub>1 ;; C\<^sub>2\<lbrace>r\<rbrace>\<^sub>u"
  by (insert assms) rel_auto

subsection {*Hoare for Conditional*}

lemma cond_hoare_r [hoare]: 
  assumes "\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>u" and "\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>C\<^sub>1 \<triangleleft> b \<triangleright>\<^sub>r C\<^sub>2\<lbrace>q\<rbrace>\<^sub>u"
  by (insert assms) rel_auto

subsection {*Hoare for assert*}

lemma assert_hoare_r [hoare]: 
  assumes "\<lbrace>c \<and> p\<rbrace>SKIP\<lbrace>q\<rbrace>\<^sub>u" and "\<lbrace>\<not>c \<and> p\<rbrace>true\<lbrace>q\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>c\<^sub>\<bottom>\<lbrace>q\<rbrace>\<^sub>u"
  unfolding rassert_def using assms cond_hoare_r [of c p SKIP q ]
  by auto

subsection {*Hoare for assume*}

lemma assume_hoare_r [hoare]: 
  assumes "\<lbrace>c \<and> p\<rbrace>SKIP\<lbrace>q\<rbrace>\<^sub>u" and "\<lbrace>\<not>c \<and> p\<rbrace>false\<lbrace>q\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>c\<^sup>\<top>\<lbrace>q\<rbrace>\<^sub>u"
  unfolding rassume_def using assms cond_hoare_r [of c p SKIP q ]
  by auto

subsection {*Hoare for While-loop*}

lemma while_hoare_r [hoare]:
  assumes "\<lbrace>p \<and> b\<rbrace>C\<lbrace>p\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>WHILE b DO C OD\<lbrace>\<not>b \<and> p\<rbrace>\<^sub>u"
  using assms
  by (simp add: While_def hoare_r_def, rule_tac lfp_lowerbound) (rel_auto)

lemma while_hoare_r' [hoare]:
  assumes "\<lbrace>p \<and> b\<rbrace>C\<lbrace>p\<rbrace>\<^sub>u" and "`p \<and> \<not>b \<Rightarrow> q`"
  shows "\<lbrace>p\<rbrace>WHILE b DO C OD\<lbrace>q\<rbrace>\<^sub>u"
  using assms
  by (metis conj_comm hoare_r_conseq p_imp_p taut_true while_hoare_r)

lemma while_invr_hoare_r [hoare]:
  assumes "\<lbrace>p \<and> b\<rbrace>C\<lbrace>p\<rbrace>\<^sub>u" and "`pre \<Rightarrow> p`" and "`(\<not>b \<and> p) \<Rightarrow> post`"
  shows "\<lbrace>pre\<rbrace>while b invr p do C od\<lbrace>post\<rbrace>\<^sub>u"
  by (metis assms hoare_r_conseq while_hoare_r while_inv_def)

subsection {*testing features*}

text {*block_test1 is a scenario. The scenario represent a program where i is name of the variable
       in the scope of the initial state s. In the scenario, and using the command block,
       we create a new variable with the same name inside the block ie., inside the new scope. 
       Now i is a local var for the scope t.
       In that case we can use a restore function on the state s to set the variable to its
       previous value ie.,its value in the scope s, and this before we exit the block.*}

lemma   blocks_test1:
  assumes "weak_lens i"
  shows "\<lbrace>true\<rbrace>
          i :== \<guillemotleft>2::int\<guillemotright>;; 
          block (i :== \<guillemotleft>5\<guillemotright>) (SKIP) (\<lambda> (s, s') (t, t').  i:== \<guillemotleft>\<lbrakk>\<langle>id\<rangle>\<^sub>s i\<rbrakk>\<^sub>e s\<guillemotright>) (\<lambda> (s, s') (t, t').  SKIP) 
         \<lbrace>&i =\<^sub>u \<guillemotleft>2::int\<guillemotright>\<rbrace>\<^sub>u"
  by (insert assms) rel_auto

text {*block_test2 is similar to  block_test1 but the var i is a global var.
       In that case we can use restore function and the state t to set the variable to its
       latest value, ie.,its value in in the scope t,probably modified inside the scope of the block.*}

lemma   blocks_test2:
  assumes "weak_lens i"
  shows "\<lbrace>true\<rbrace>
          i :== \<guillemotleft>2::int\<guillemotright>;; 
          block (i :== \<guillemotleft>5\<guillemotright>) (SKIP) (\<lambda> (s, s') (t, t').  i:== \<guillemotleft>\<lbrakk>\<langle>id\<rangle>\<^sub>s i\<rbrakk>\<^sub>e t\<guillemotright>) (\<lambda> (s, s') (t, t').  SKIP) 
         \<lbrace>&i =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>\<^sub>u"
  by (insert assms) rel_auto





end