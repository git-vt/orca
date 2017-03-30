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
(* declare lens_indep_def[last_simps] (* causes the VCG to hang *) *)

method vcg_rules = 
  ((rule seq_hoare_r|
    (rule skip_hoare_r)|
    (rule while_invr_hoare_r)|
    (rule cond_hoare_r; simp?, (rule hoare_false)?)| (* not sure if s/,/;/ is needed *)
    (rule assigns_hoare_r')| (* infixr seqr means this is not useful chained with seq rule *)
    (rule assigns_hoare_r)|
    (rule assert_hoare_r)|
    (rule assume_hoare_r)
   )+
  )?

method vcg declares last_simps =
  (intro hoare_r_conj)?; (* intro rather than rule means it will be repeatedly applied *)
  vcg_rules;
  (rel_auto|
   pred_auto| (* also has simp version *)
   pred_blast),
  (auto simp: last_simps)?
(* maybe want another VCG that does single-goal solving *)

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
  apply (rule assigns_hoare_r)

  defer
  apply simp
  apply (rule assigns_hoare_r)

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
      i:== &a ;; j :== \<guillemotleft>0::int\<guillemotright> ;;
      (&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> &j =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &i =\<^sub>u &a)\<^sup>\<top>;;
    while  &i <\<^sub>u &n
      invr  &a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> &j =\<^sub>u (((&i + 1) - &a) div 2) \<and> &i \<le>\<^sub>u &n \<and>  &i \<ge>\<^sub>u &a
      do (j :== &j + \<guillemotleft>1\<guillemotright> \<triangleleft> &i mod \<guillemotleft>2\<guillemotright> =\<^sub>u  \<guillemotleft>0::int\<guillemotright>\<triangleright>\<^sub>r II) ;;  i :== &i + \<guillemotleft>1\<guillemotright> od
    \<lbrace>&j =\<^sub>u \<guillemotleft>1::int\<guillemotright>\<rbrace>\<^sub>u"
apply (insert assms)
apply (rule seq_hoare_r)
 prefer 2
 apply (rule seq_hoare_r [of _ _ true]) (* The usage of `of` is an issue here *)
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
    apply (rule assigns_hoare_r)
    prefer 6
    apply (rule assigns_hoare_r)
    unfolding lens_indep_def
    apply rel_auto
   apply rel_auto
   using mod_pos_pos_trivial apply auto[1]
  apply rel_auto
 apply rel_auto
apply rel_auto
apply rel_auto
done

lemma even_count_method:
  assumes "vwb_lens i" and  "weak_lens a" and  "vwb_lens j"  and  "weak_lens n"and
          "i \<bowtie> a" and "i \<bowtie> j" and "i \<bowtie> n"  "a \<bowtie> j" and "a \<bowtie> n" and "j \<bowtie> n"
  shows
  "\<lbrace>&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright>\<rbrace>
      i:== &a ;; j :== \<guillemotleft>0::int\<guillemotright> ;;
      (&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> &j =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &i =\<^sub>u &a)\<^sup>\<top>;;
    while  &i <\<^sub>u &n
      invr  &a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> &j =\<^sub>u (((&i + 1) - &a) div 2) \<and> &i \<le>\<^sub>u &n \<and>  &i \<ge>\<^sub>u &a
      do (j :== &j + \<guillemotleft>1\<guillemotright> \<triangleleft> &i mod \<guillemotleft>2\<guillemotright> =\<^sub>u  \<guillemotleft>0::int\<guillemotright>\<triangleright>\<^sub>r II) ;;  i :== &i + \<guillemotleft>1\<guillemotright> od
    \<lbrace>&j =\<^sub>u \<guillemotleft>1::int\<guillemotright>\<rbrace>\<^sub>u"
  using assms
  apply vcg
  unfolding lens_indep_def
  oops

end
