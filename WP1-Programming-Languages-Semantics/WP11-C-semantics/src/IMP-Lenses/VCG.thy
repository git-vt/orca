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

method vcg declares last_simps =
  (intro hoare_r_conj)?, (* intro rather than rule means it will be repeatedly applied *)
  ((((rule seq_hoare_r; (rule assigns_hoare_r')?)|
     (rule cond_hoare_r; simp?, (rule hoare_false)?)| (* not sure if s/,/;/ is needed *)
     (rule assigns_hoare_r)

    )+)?,
    rel_simp,
    (simp add: last_simps)?)+
(* Need weakest precondition reasoning *)

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
          IF \<lceil>true\<rceil>\<^sub>< THEN x :== (&x - exp\<^sub>2) ELSE x :== (&x + exp\<^sub>2)
         \<lbrace>&x =\<^sub>u exp\<^sub>1 - exp\<^sub>2\<rbrace>\<^sub>u"
  using assms
  by rel_simp

lemma if_true_manual:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>1"
      and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
          IF \<lceil>true\<rceil>\<^sub>< THEN x :== (&x - exp\<^sub>2) ELSE x :== (&x + exp\<^sub>2)
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
          IF \<lceil>true\<rceil>\<^sub>< THEN x :== (&x - exp\<^sub>2) ELSE x :== (&x + exp\<^sub>2)
         \<lbrace>&x =\<^sub>u exp\<^sub>1 - exp\<^sub>2\<rbrace>\<^sub>u"
  using assms
  by vcg

lemma if_false:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>1"
      and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
          IF \<lceil>false\<rceil>\<^sub>< THEN x :== (&x - exp\<^sub>2) ELSE x :== (&x + exp\<^sub>2)
         \<lbrace>&x =\<^sub>u exp\<^sub>1 + exp\<^sub>2\<rbrace>\<^sub>u"
  using assms
  by rel_simp

lemma if_false_manual:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>1"
      and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
          IF \<lceil>false\<rceil>\<^sub>< THEN x :== (&x - exp\<^sub>2) ELSE x :== (&x + exp\<^sub>2)
         \<lbrace>&x =\<^sub>u exp\<^sub>1 + exp\<^sub>2\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule cond_hoare_r)
  
  apply (subst symbolic_exec_subst)+ (* don't exist anymore *)
  apply (rule hoare_false)

  apply (subst symbolic_exec_subst)+
  apply (subst subst_upd_var_def)+
  apply transfer'
  apply simp
  oops

lemma if_false_method:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>1"
      and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
          IF \<lceil>false\<rceil>\<^sub>< THEN x :== (&x - exp\<^sub>2) ELSE x :== (&x + exp\<^sub>2)
         \<lbrace>&x =\<^sub>u exp\<^sub>1 + exp\<^sub>2\<rbrace>\<^sub>u"
  using assms
  by vcg

lemma if_base:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>2"
      and "x \<sharp> exp\<^sub>3"
  shows "\<lbrace>true\<rbrace>
          IF \<lceil>exp\<^sub>1\<rceil>\<^sub>< THEN x :== exp\<^sub>2 ELSE x :== exp\<^sub>3
         \<lbrace>&x =\<^sub>u exp\<^sub>2 \<or> &x =\<^sub>u exp\<^sub>3\<rbrace>\<^sub>u"
  using assms
  by rel_auto

lemma if_manual:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>2"
      and "x \<sharp> exp\<^sub>3"
  shows "\<lbrace>true\<rbrace>
          IF \<lceil>exp\<^sub>1\<rceil>\<^sub>< THEN x :== exp\<^sub>2 ELSE x :== exp\<^sub>3
         \<lbrace>&x =\<^sub>u exp\<^sub>2 \<or> &x =\<^sub>u exp\<^sub>3\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule cond_hoare_r)
  apply simp
  apply (rule assigns_hoare_r)

  defer
  apply simp
  apply (rule assigns_hoare_r)

  apply rel_auto
  by (simp add: bop_ueval impl.rep_eq subst.rep_eq sup_uexpr.rep_eq taut.rep_eq unrest_upred.rep_eq
      var.rep_eq)

lemma if_method:
  assumes "weak_lens x"
      and "x \<sharp> exp\<^sub>2"
      and "x \<sharp> exp\<^sub>3"
  shows "\<lbrace>true\<rbrace>
          IF \<lceil>exp\<^sub>1\<rceil>\<^sub>< THEN x :== exp\<^sub>2 ELSE x :== exp\<^sub>3
         \<lbrace>&x =\<^sub>u exp\<^sub>2 \<or> &x =\<^sub>u exp\<^sub>3\<rbrace>\<^sub>u"
  using assms
  by vcg

subsubsection \<open>Building WHILE\<close>

lemma even_count:
   assumes "vwb_lens i" and  "weak_lens a" and  "vwb_lens j"  and  "weak_lens n"
       and "i \<bowtie> a" and "i \<bowtie> j" and "i \<bowtie> n"  "a \<bowtie> j" and "a \<bowtie> n" and "j \<bowtie> n" 
   shows
   "\<lbrace>&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright>\<rbrace>
     i :== &a;; j :== \<guillemotleft>0::int\<guillemotright>;;
     while &i <\<^sub>u &n
       invr &a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> &j =\<^sub>u (((&i + 1) - &a) div 2) \<and> &i \<le>\<^sub>u &n \<and> &i \<ge>\<^sub>u &a
       do (j :== &j + \<guillemotleft>1\<guillemotright> \<triangleleft> &i mod \<guillemotleft>2\<guillemotright> =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<triangleright>\<^sub>r SKIP);; i :== &i + \<guillemotleft>1\<guillemotright> od
     \<lbrace>&j =\<^sub>u \<guillemotleft>1::int\<guillemotright>\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule seq_hoare_r)
  prefer 2
  apply (rule seq_hoare_r)
  prefer 2
  apply (rule while_invr_hoare_r [of _ _ _ "&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> &i =\<^sub>u &a \<and> &j =\<^sub>u \<guillemotleft>0::int\<guillemotright>"])
  apply (rule seq_hoare_r)
  prefer 2
  apply (rule assigns_hoare_r')
  prefer 4
  apply (rule assigns_hoare_r)
  prefer 2
  apply (rule cond_hoare_r)
  apply (rule assigns_hoare_r)
  prefer 6
  apply (rule assigns_hoare_r)
  unfolding lens_indep_def
  apply rel_auto[1]
   apply rel_auto[1]
   apply (simp add: mod_pos_pos_trivial)
   apply rel_auto[1]
   prefer 2
     apply rel_auto[1]
   apply rel_auto[1]
done

end
