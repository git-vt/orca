section \<open>Verification Condition Testing\<close>

theory VCG
  imports "utp/utp_hoare"
begin

subsection \<open>Tactics for Theorem Proving\<close>
text \<open>The tactics below are used to prove the validity of complex Hoare triples/expressions
semi-automatically in a more efficient manner than using @{method rel_auto} by itself.\<close>

subsection \<open>Using Eisbach methods\<close>

text \<open>Some proof subgoals require extra cleanup beyond plain simp/auto, so we need a simpset for
those.\<close>
named_theorems last_simps
declare lens_indep_sym[last_simps]
declare mod_pos_pos_trivial[last_simps]

definition ax :: "int \<Rightarrow> int" where
  "ax a \<equiv> a * 2"

text \<open>Some proof subgoals require theorem unfolding.\<close>
named_theorems unfolds
declare lens_indep_def[unfolds]
declare ax_def[unfolds]

method while_pre =
  (rule seq_hoare_r)?,
  (rule assume_hoare_r)?,
  (rule skip_hoare_r)?

(* trying with other while loops to find the right patterns *)
method even_count declares last_simps =
  rule seq_hoare_r;
  (rule seq_hoare_r[of _ _ true])?, (* ? needed as it attempts application of the rule to the first subgoal as well *)
  (rule assigns_hoare_r')?, (* ? needed again to avoid error *)
  while_pre;
  (rule while_invr_hoare_r)?,
  (rule seq_hoare_r)?;
  (rule assigns_hoare_r')?,
  (rule cond_hoare_r)?,
  (unfold unfolds)?,
  insert last_simps;
  rel_auto

method increment =
  rule seq_hoare_r[of _ _ true];
  while_pre;
  (rule while_invr_hoare_r)?,
  unfold unfolds;
  rel_auto

method rules =
  ((rule seq_hoare_r|
      rule skip_hoare_r|
      rule while_invr_hoare_r|
      (rule cond_hoare_r; simp?, (rule hoare_false)?)| (* not sure if s/,/;/ is needed *)
      rule assigns_hoare_r'| (* infixr seqr means this is not useful chained with seq rule *)
      rule assert_hoare_r|
      rule assume_hoare_r
    )+
  )?

(* VCG for partial solving; applies hoare rules (possibly generating more subgoals) and attempts
to solve the first *)
method vcg_step =
  while_pre|fail

method vcg declares last_simps = (even_count last_simps: last_simps)|increment|
  ((intro hoare_r_conj)?; (* intro rather than rule means it will be repeatedly applied *)
    rules;
    (rel_auto|
      pred_auto| (* also has simp version *)
      pred_blast),
    (auto simp: last_simps)?
  )

(* Need weakest precondition reasoning? *)

subsubsection \<open>Building swap (SEQ+ASN)\<close>

lemma swap_test:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
      and "x \<bowtie> y" and "x \<bowtie> z" and "y \<bowtie> z"
  shows "\<lbrace>&x =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>b\<guillemotright>\<rbrace>
          z :== &x;;
          x :== &y;;
          y :== &z
         \<lbrace>&x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>a\<guillemotright>\<rbrace>\<^sub>u"
  using assms
  by rel_auto (simp add: lens_indep_sym)

lemma swap_test_manual:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
      and "x \<bowtie> y" and "x \<bowtie> z" and "y \<bowtie> z"
  shows "\<lbrace>&x =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>b\<guillemotright>\<rbrace>
          z :== &x;;
          x :== &y;;
          y :== &z
         \<lbrace>&x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>a\<guillemotright>\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (intro hoare_r_conj)

  apply (rule seq_hoare_r)
  prefer 2
  apply (rule seq_hoare_r)
  apply (rule assigns_hoare_r')
  apply (rule assigns_hoare_r')
  apply simp
  defer

  apply (rule seq_hoare_r)
  prefer 2
  apply (rule seq_hoare_r)
  apply (rule assigns_hoare_r')
  apply (rule assigns_hoare_r')
  apply simp

  apply rel_simp
  apply (simp add: lens_indep_sym)
  oops (* Not sure why this isn't working even though the VCG based on it does. *)
(* ML_prf \<open>\<close> *)

lemma swap_test_method:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
      and "x \<bowtie> y" and "x \<bowtie> z" and "y \<bowtie> z"
  shows "\<lbrace>&x =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>b\<guillemotright>\<rbrace>
          z :== &x;;
          x :== &y;;
          y :== &z
         \<lbrace>&x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>a\<guillemotright>\<rbrace>\<^sub>u"
  using assms
  by vcg

lemma swap_testx:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
      and "x \<bowtie> y" 
      and "x \<sharp> a" and "y \<sharp> a" and "z \<sharp> a"
      and "x \<sharp> b" and "y \<sharp> b" and "z \<sharp> b"
  shows "\<lbrace>&x =\<^sub>u a \<and> &y =\<^sub>u b\<rbrace>
          z :== &x;;
          x :== &y;;
          y :== &z
         \<lbrace>&x =\<^sub>u b \<and> &y =\<^sub>u a\<rbrace>\<^sub>u = \<lbrace>&x =\<^sub>u a \<and> &y =\<^sub>u b\<rbrace>
          z :== &x;;
          x :== &y
         \<lbrace>&x =\<^sub>u b \<and> &z =\<^sub>u a\<rbrace>\<^sub>u"
  using assms
  by rel_simp

subsubsection \<open>Building COND\<close>

lemma if_true:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>1"
      and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
          x :== &x - exp\<^sub>2 \<triangleleft> true \<triangleright>\<^sub>r (x :== &x + exp\<^sub>2)
         \<lbrace>&x =\<^sub>u exp\<^sub>1 - exp\<^sub>2\<rbrace>\<^sub>u"
  using assms
  by rel_simp

lemma if_true_manual:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>1"
      and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
          x :== &x - exp\<^sub>2 \<triangleleft> true \<triangleright>\<^sub>r (x :== &x + exp\<^sub>2)
         \<lbrace>&x =\<^sub>u exp\<^sub>1 - exp\<^sub>2\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule cond_hoare_r)
  defer
  apply simp
  apply (rule hoare_false)

  apply simp
  apply rel_simp
  done

lemma if_true_method:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>1"
      and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
          x :== &x - exp\<^sub>2 \<triangleleft> true \<triangleright>\<^sub>r (x :== &x + exp\<^sub>2)
         \<lbrace>&x =\<^sub>u exp\<^sub>1 - exp\<^sub>2\<rbrace>\<^sub>u"
  using assms
  by vcg

lemma if_false:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>1"
      and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
          x :== &x - exp\<^sub>2 \<triangleleft> false \<triangleright>\<^sub>r (x :== &x + exp\<^sub>2)
         \<lbrace>&x =\<^sub>u exp\<^sub>1 + exp\<^sub>2\<rbrace>\<^sub>u"
  using assms
  by rel_simp

lemma if_false_manual:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>1"
      and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
          x :== &x - exp\<^sub>2 \<triangleleft> false \<triangleright>\<^sub>r (x :== &x + exp\<^sub>2)
         \<lbrace>&x =\<^sub>u exp\<^sub>1 + exp\<^sub>2\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule cond_hoare_r)
  
  apply simp
  apply (rule hoare_false)

  apply simp
  apply rel_auto
  done

lemma if_false_method:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>1"
      and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
          x :== &x - exp\<^sub>2 \<triangleleft> false \<triangleright>\<^sub>r (x :== &x + exp\<^sub>2)
         \<lbrace>&x =\<^sub>u exp\<^sub>1 + exp\<^sub>2\<rbrace>\<^sub>u"
  using assms
  by vcg

lemma if_base:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>2"
      and "x \<sharp> exp\<^sub>3"
  shows "\<lbrace>true\<rbrace>
          x :== exp\<^sub>2 \<triangleleft> exp\<^sub>1 \<triangleright>\<^sub>r (x :== exp\<^sub>3)
         \<lbrace>&x =\<^sub>u exp\<^sub>2 \<or> &x =\<^sub>u exp\<^sub>3\<rbrace>\<^sub>u"
  using assms
  by rel_auto

lemma if_manual:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>2"
      and "x \<sharp> exp\<^sub>3"
  shows "\<lbrace>true\<rbrace>
          x :== exp\<^sub>2 \<triangleleft> exp\<^sub>1 \<triangleright>\<^sub>r (x :== exp\<^sub>3)
         \<lbrace>&x =\<^sub>u exp\<^sub>2 \<or> &x =\<^sub>u exp\<^sub>3\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule cond_hoare_r)
  apply simp

  defer
  apply simp

  apply rel_simp
  apply pred_simp (* needed for UTP predicates; pred_blast needed for sets *)
  done

lemma if_method:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>2"
      and "x \<sharp> exp\<^sub>3"
  shows "\<lbrace>true\<rbrace>
          x :== exp\<^sub>2 \<triangleleft> exp\<^sub>1 \<triangleright>\<^sub>r (x :== exp\<^sub>3)
         \<lbrace>&x =\<^sub>u exp\<^sub>2 \<or> &x =\<^sub>u exp\<^sub>3\<rbrace>\<^sub>u"
  using assms
  by vcg

subsubsection \<open>Building WHILE\<close>

lemma even_count_manual:
  assumes "vwb_lens i" and "weak_lens a" and "vwb_lens j" and "weak_lens n"
      and "i \<bowtie> a" and "i \<bowtie> j" and "i \<bowtie> n" and "a \<bowtie> j" and "a \<bowtie> n" and "j \<bowtie> n"
  shows
  "\<lbrace>&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright>\<rbrace>
      i :== &a ;; j :== \<guillemotleft>0::int\<guillemotright> ;;
      (&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> &j =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &i =\<^sub>u &a)\<^sup>\<top> ;;
    while &i <\<^sub>u &n
      invr &a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> &j =\<^sub>u (((&i + 1) - &a) div 2) \<and> &i \<le>\<^sub>u &n \<and> &i \<ge>\<^sub>u &a
      do (j :== &j + \<guillemotleft>1\<guillemotright> \<triangleleft> &i mod \<guillemotleft>2\<guillemotright> =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<triangleright>\<^sub>r II) ;; i :== &i + \<guillemotleft>1\<guillemotright> od
    \<lbrace>&j =\<^sub>u \<guillemotleft>1::int\<guillemotright>\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule seq_hoare_r)
   prefer 2
   apply (rule seq_hoare_r[of _ _ true])
    apply (rule assigns_hoare_r')
   apply (rule seq_hoare_r)
    apply (rule assume_hoare_r)
    apply (rule skip_hoare_r)
   prefer 2
   apply (rule while_invr_hoare_r)
     apply (rule seq_hoare_r)
      prefer 2
      apply (rule assigns_hoare_r')
     apply (rule cond_hoare_r)
      prefer 6
      unfolding lens_indep_def
      apply rel_auto
     apply rel_auto
     using mod_pos_pos_trivial
    apply rel_auto
   apply rel_auto
  apply rel_auto
  apply rel_auto
  done

lemma even_count_method:
  assumes "vwb_lens i" and "weak_lens a" and "vwb_lens j" and "weak_lens n"
      and "i \<bowtie> a" and "i \<bowtie> j" and "i \<bowtie> n" and "a \<bowtie> j" and "a \<bowtie> n" and "j \<bowtie> n"
  shows
  "\<lbrace>&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright>\<rbrace>
      i :== &a ;; j :== \<guillemotleft>0::int\<guillemotright> ;;
      (&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> &j =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &i =\<^sub>u &a)\<^sup>\<top> ;;
    while &i <\<^sub>u &n
      invr &a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> &j =\<^sub>u (((&i + 1) - &a) div 2) \<and> &i \<le>\<^sub>u &n \<and> &i \<ge>\<^sub>u &a
      do (j :== &j + \<guillemotleft>1\<guillemotright> \<triangleleft> &i mod \<guillemotleft>2\<guillemotright> =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<triangleright>\<^sub>r II) ;; i :== &i + \<guillemotleft>1\<guillemotright> od
    \<lbrace>&j =\<^sub>u \<guillemotleft>1::int\<guillemotright>\<rbrace>\<^sub>u"
  by (insert assms) vcg

lemma increment_manual:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
    x :== \<guillemotleft>0\<guillemotright>;;
   (&x =\<^sub>u \<guillemotleft>0\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>5\<guillemotright>)\<^sup>\<top>;;
    while &x <\<^sub>u &y
      invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u \<guillemotleft>5\<guillemotright>
      do x :== &x + \<guillemotleft>1\<guillemotright> od
    \<lbrace>&x =\<^sub>u \<guillemotleft>5\<guillemotright>\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule seq_hoare_r[of _ _ true])
  defer
  apply (rule seq_hoare_r)
  apply (rule assume_hoare_r)
  apply (rule skip_hoare_r)
  defer
  apply (rule while_invr_hoare_r)
  unfolding lens_indep_def
  apply rel_auto
  apply rel_auto
  apply rel_auto
  apply rel_auto
  apply rel_auto
  done

lemma increment_method:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
    x :== \<guillemotleft>0\<guillemotright>;;
   (&x =\<^sub>u \<guillemotleft>0\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>5\<guillemotright>)\<^sup>\<top>;;
    while &x <\<^sub>u &y
      invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u \<guillemotleft>5\<guillemotright>
      do x :== &x + \<guillemotleft>1\<guillemotright> od
    \<lbrace>&x =\<^sub>u \<guillemotleft>5\<guillemotright>\<rbrace>\<^sub>u"
  by (insert assms) vcg

end
