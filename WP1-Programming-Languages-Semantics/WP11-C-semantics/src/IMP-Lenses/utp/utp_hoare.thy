subsection {* Relational Hoare calculus *}

theory utp_hoare
imports "../Algebraic_Laws"
begin

named_theorems hoare

definition hoare_r :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>u") where
"\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u = ((\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>r\<rceil>\<^sub>>) \<sqsubseteq> Q)"

declare hoare_r_def [upred_defs]

lemma hoare_r_conj [hoare]: 
  assumes"\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u" and "\<lbrace>p\<rbrace>Q\<lbrace>s\<rbrace>\<^sub>u"  
  shows "\<lbrace>p\<rbrace>Q\<lbrace>r \<and> s\<rbrace>\<^sub>u"
  by (insert assms) rel_auto

lemma hoare_r_conseq [hoare]: 
  assumes "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" and "\<lbrace>p\<^sub>2\<rbrace>S\<lbrace>q\<^sub>2\<rbrace>\<^sub>u" and "`q\<^sub>2 \<Rightarrow> q\<^sub>1`" 
  shows   "\<lbrace>p\<^sub>1\<rbrace>S\<lbrace>q\<^sub>1\<rbrace>\<^sub>u"
  by (insert assms) rel_auto

lemma assigns_hoare_r [hoare]: 
  assumes"`p \<Rightarrow> \<sigma> \<dagger> q`" 
  shows  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>a\<lbrace>q\<rbrace>\<^sub>u"
  by (insert assms) rel_auto

lemma skip_hoare_r [hoare]: "\<lbrace>p\<rbrace>SKIP\<lbrace>p\<rbrace>\<^sub>u"
  by rel_auto

lemma seq_hoare_r [hoare]: 
  assumes"\<lbrace>p\<rbrace>Q\<^sub>1\<lbrace>s\<rbrace>\<^sub>u" and "\<lbrace>s\<rbrace>Q\<^sub>2\<lbrace>r\<rbrace>\<^sub>u" 
  shows"\<lbrace>p\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>r\<rbrace>\<^sub>u"
  by (insert assms) rel_auto

lemma cond_hoare_r [hoare]: 
  assumes "\<lbrace>b \<and> p\<rbrace>S\<lbrace>q\<rbrace>\<^sub>u" and "\<lbrace>\<not>b \<and> p\<rbrace>T\<lbrace>q\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>S \<triangleleft> b \<triangleright>\<^sub>r T\<lbrace>q\<rbrace>\<^sub>u"
  by (insert assms) rel_auto

lemma while_hoare_r [hoare]:
  assumes "\<lbrace>p \<and> b\<rbrace>S\<lbrace>p\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>WHILE b DO S OD\<lbrace>\<not>b \<and> p\<rbrace>\<^sub>u"
  using assms
  by (simp add: While_def hoare_r_def, rule_tac lfp_lowerbound) (rel_auto)

lemma while_invr_hoare_r [hoare]:
  assumes "\<lbrace>p \<and> b\<rbrace>S\<lbrace>p\<rbrace>\<^sub>u" "`pre \<Rightarrow> p`" "`(\<not>b \<and> p) \<Rightarrow> post`"
  shows "\<lbrace>pre\<rbrace>while b invr p do S od\<lbrace>post\<rbrace>\<^sub>u"
  by (metis assms hoare_r_conseq while_hoare_r while_inv_def)

end