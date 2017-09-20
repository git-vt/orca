subsection {* Relational Hoare calculus *}

theory utp_hoare
imports "../../AlgebraicLaws/Rel&Des/Algebraic_Laws"
begin

named_theorems hoare and hoare_safe

method hoare_split uses hr = 
  ((simp add: assigns_r_comp usubst unrest)?, -- {* Eliminate assignments where possible *}
   (auto 
    intro: hoare intro!: hoare_safe hr
    simp add: assigns_r_comp conj_comm conj_assoc usubst unrest))[1] -- {* Apply Hoare logic laws *}

method hoare_auto uses hr = (hoare_split hr: hr; rel_auto?)
  
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

lemma skip_hoare_r [hoare_safe]: "\<lbrace>p\<rbrace>II\<lbrace>p\<rbrace>\<^sub>u"
  by rel_auto

subsection {*Hoare for assignment*}

lemma assigns_hoare_r [hoare_safe]:
  assumes"`p \<Rightarrow> \<sigma> \<dagger> q`"
  shows  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>a\<lbrace>q\<rbrace>\<^sub>u"
  by (insert assms) rel_auto

lemma assigns_hoare_r' [hoare]: "\<lbrace>\<sigma> \<dagger> p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>a\<lbrace>p\<rbrace>\<^sub>u"
  by rel_auto

lemma assigns_naive_rule:
  assumes "x\<sharp>e" and "weak_lens x" 
  shows   "\<lbrace>p\<rbrace>x :== e\<lbrace>&x=\<^sub>ue\<rbrace>\<^sub>u"
  using assms
  by pred_simp   
    
lemma assigns_floyd_r [hoare]:
  assumes \<open>vwb_lens x\<close>
  shows   \<open>\<lbrace>p\<rbrace>x :== e\<lbrace>\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrace>\<^sub>u\<close>
  apply (insert assms)
  apply pred_simp
  apply transfer
  apply (rule_tac x = \<open>get\<^bsub>x\<^esub> a\<close> in exI)
  (*subgoal for a x p e
   apply (rule exI[where x="get\<^bsub>x\<^esub> a"])*)
  apply auto
  done

subsection {*Hoare for Sequential Composition*}

lemma seq_hoare_r:
  assumes"\<lbrace>p\<rbrace>C\<^sub>1\<lbrace>s\<rbrace>\<^sub>u" and "\<lbrace>s\<rbrace>C\<^sub>2\<lbrace>r\<rbrace>\<^sub>u"
  shows"\<lbrace>p\<rbrace>C\<^sub>1 ;; C\<^sub>2\<lbrace>r\<rbrace>\<^sub>u"
  by (insert assms) rel_auto
    
lemma seq_hoare_invariant [hoare_safe]: 
  assumes "\<lbrace>p\<rbrace>Q\<^sub>1\<lbrace>p\<rbrace>\<^sub>u" and "\<lbrace>p\<rbrace>Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>u"
  using assms 
  by (auto simp: seq_hoare_r)

lemma seq_hoare_stronger_pre_1 [hoare_safe]: 
  assumes "\<lbrace>p \<and> q\<rbrace>Q\<^sub>1\<lbrace>p \<and> q\<rbrace>\<^sub>u" and "\<lbrace>p \<and> q\<rbrace>Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>u" 
  shows "\<lbrace>p \<and> q\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>u"
  using assms 
  by (auto simp: seq_hoare_r)

lemma seq_hoare_stronger_pre_2 [hoare_safe]: 
  assumes "\<lbrace>p \<and> q\<rbrace>Q\<^sub>1\<lbrace>p \<and> q\<rbrace>\<^sub>u" and "\<lbrace>p \<and> q\<rbrace>Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>u" 
  shows "\<lbrace>p \<and> q\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>u"
  using assms 
  by (auto simp: seq_hoare_r)
   
lemma seq_hoare_inv_r_2 [hoare]: 
  assumes "\<lbrace>p\<rbrace>Q\<^sub>1\<lbrace>q\<rbrace>\<^sub>u" and "\<lbrace>q\<rbrace>Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>u" 
  shows   "\<lbrace>p\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>u"
  using assms 
  by (auto simp: seq_hoare_r)
 
lemma seq_hoare_inv_r_3 [hoare]: 
  assumes "\<lbrace>p\<rbrace>Q\<^sub>1\<lbrace>p\<rbrace>\<^sub>u" and "\<lbrace>p\<rbrace>Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>Q\<^sub>1 ;; Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>u"
  using assms 
  by (auto simp: seq_hoare_r)
    
subsection {*Hoare for Conditional*}

lemma cond_hoare_r [hoare_safe]: 
  assumes "\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>u" and "\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>C\<^sub>1 \<triangleleft> b \<triangleright>\<^sub>r C\<^sub>2\<lbrace>q\<rbrace>\<^sub>u"
  by (insert assms) rel_auto

subsection {*Hoare for assert*}

lemma assert_hoare_r [hoare_safe]: 
  assumes "\<lbrace>c \<and> p\<rbrace>II\<lbrace>q\<rbrace>\<^sub>u" and "\<lbrace>\<not>c \<and> p\<rbrace>true\<lbrace>q\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>c\<^sub>\<bottom>\<lbrace>q\<rbrace>\<^sub>u"
  unfolding rassert_def using assms cond_hoare_r [of c p _ q ]
  by auto

subsection {*Hoare for assume*}

lemma assume_hoare_r [hoare_safe]: 
  assumes "\<lbrace>c \<and> p\<rbrace>II\<lbrace>q\<rbrace>\<^sub>u" and "\<lbrace>\<not>c \<and> p\<rbrace>false\<lbrace>q\<rbrace>\<^sub>u" 
  shows "\<lbrace>p\<rbrace>c\<^sup>\<top>\<lbrace>q\<rbrace>\<^sub>u"
  unfolding rassume_def using assms cond_hoare_r [of c p _ q ]
  by auto

subsection {*Hoare for While-loop*}

lemma while_hoare_r [hoare_safe]:
  assumes "\<lbrace>p \<and> b\<rbrace>C\<lbrace>p\<rbrace>\<^sub>u"
  shows "\<lbrace>p\<rbrace>while b do C od\<lbrace>\<not>b \<and> p\<rbrace>\<^sub>u"
  using assms
  apply (simp add: while_def hoare_r_def)apply ( rule_tac lfp_lowerbound) apply(rel_auto)
  done

lemma while_hoare_r' [hoare_safe]:
  assumes "\<lbrace>p \<and> b\<rbrace>C\<lbrace>p\<rbrace>\<^sub>u" and "`p \<and> \<not>b \<Rightarrow> q`"
  shows "\<lbrace>p\<rbrace>while b do C od\<lbrace>q\<rbrace>\<^sub>u"
  using assms
  by (metis conj_comm hoare_r_conseq p_imp_p taut_true while_hoare_r)


lemma while_invr_hoare_r  [hoare_safe]:
  assumes "\<lbrace>p \<and> b\<rbrace>C\<lbrace>p\<rbrace>\<^sub>u" and "`pre \<Rightarrow> p`" and "`(\<not>b \<and> p) \<Rightarrow> post`"
  shows "\<lbrace>pre\<rbrace>while b invr p do C od\<lbrace>post\<rbrace>\<^sub>u"
  by (metis assms hoare_r_conseq while_hoare_r while_inv_def)


text {* Frame rule: If starting $S$ in a state satisfying $p establishes q$ in the final state, then
  we can insert an invariant predicate $r$ when $S$ is framed by $a$, provided that $r$ does not
  refer to variables in the frame, and $q$ does not refer to variables outside the frame. *}
    
lemma frame_hoare_r [hoare_safe]: 
  assumes "vwb_lens a" "a \<sharp> r" "a \<natural> q" "\<lbrace>p \<and> r\<rbrace>S\<lbrace>q\<rbrace>\<^sub>u"
  shows "\<lbrace>p \<and> r\<rbrace>a:[S]\<lbrace>q \<and> r\<rbrace>\<^sub>u"
  using assms by (rel_simp)

lemma frame_hoare_r' [hoare_safe]: 
  assumes "vwb_lens a" "a \<sharp> r" "a \<natural> q" "\<lbrace>r \<and> p\<rbrace>S\<lbrace>q\<rbrace>\<^sub>u"
  shows "\<lbrace>r \<and> p\<rbrace>a:[S]\<lbrace>r \<and> q\<rbrace>\<^sub>u"
  using assms
  by (simp add: frame_hoare_r utp_pred_laws.inf.commute)    

end