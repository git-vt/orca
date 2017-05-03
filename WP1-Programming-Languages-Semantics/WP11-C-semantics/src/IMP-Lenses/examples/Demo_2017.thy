theory Demo_2017
  imports "../hoare/VCG"
begin

section \<open>Testing swap (SEQ+ASN)\<close>

lemma swap_test_manual:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
  and "x \<bowtie> y" and "x \<bowtie> z" and "y \<bowtie> z"
  shows "\<lbrace>&x =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>b\<guillemotright>\<rbrace>
  z :== &x;;
  x :== &y;;
  y :== &z
  \<lbrace>&x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>a\<guillemotright>\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule seq_hoare_r)
   defer
   apply (rule seq_hoare_r)
    apply (rule assigns_hoare_r')
   apply (rule assigns_hoare_r')
  apply rel_simp
  apply (simp add: lens_indep_sym)
  done

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

section \<open>Testing WHILE\<close>

lemma even_count_manual:
  assumes "vwb_lens i" and "weak_lens start" and "vwb_lens j" and "weak_lens end"
  and "i \<bowtie> start" and "i \<bowtie> j" and "i \<bowtie> end" and "start \<bowtie> j" and "start \<bowtie> end" and "j \<bowtie> end"
  shows
  "\<lbrace>&start =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &end =\<^sub>u 1\<rbrace>
    i :== &start;; j :== 0;;
    (&start =\<^sub>u 0 \<and> &end =\<^sub>u 1 \<and> &j =\<^sub>u 0 \<and> &i =\<^sub>u &start)\<^sup>\<top> ;;
    while &i <\<^sub>u &end
    invr &start =\<^sub>u 0 \<and> &end =\<^sub>u 1 \<and> &j =\<^sub>u (((&i + 1) - &start) div 2) \<and> &i \<le>\<^sub>u &end \<and> &i \<ge>\<^sub>u &start
    do (j :== &j + 1 \<triangleleft> &i mod 2 =\<^sub>u 0 \<triangleright>\<^sub>r II) ;; i :== &i + 1 od
   \<lbrace>&j =\<^sub>u 1\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule seq_hoare_r)
   prefer 2
   apply (rule seq_hoare_r[of _ _ true](* , rule hoare_true *))
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
  assumes "vwb_lens i" and "weak_lens start" and "vwb_lens j" and "weak_lens end"
  and "i \<bowtie> start" and "i \<bowtie> j" and "i \<bowtie> end" and "start \<bowtie> j" and "start \<bowtie> end" and "j \<bowtie> end"
  shows
  "\<lbrace>&start =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &end =\<^sub>u 1\<rbrace>
    i :== &start;; j :== 0;;
    (&start =\<^sub>u 0 \<and> &end =\<^sub>u 1 \<and> &j =\<^sub>u 0 \<and> &i =\<^sub>u &start)\<^sup>\<top>;;
    while &i <\<^sub>u &end
    invr &start =\<^sub>u 0 \<and> &end =\<^sub>u 1 \<and> &j =\<^sub>u (((&i + 1) - &start) div 2) \<and> &start \<le>\<^sub>u &i \<and> &i \<le>\<^sub>u &end
    do (j :== &j + 1 \<triangleleft> &i mod 2 =\<^sub>u 0 \<triangleright>\<^sub>r II);; i :== &i + 1 od
   \<lbrace>&j =\<^sub>u 1\<rbrace>\<^sub>u"
  by (insert assms) vcg

lemma increment_manual:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x :== 0;;
  (&x =\<^sub>u 0 \<and> &y =\<^sub>u 5)\<^sup>\<top>;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>u"
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
  x :== 0;;
  (&x =\<^sub>u 0 \<and> &y =\<^sub>u 5)\<^sup>\<top>;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>u"
  by (insert assms) vcg

lemma double_increment_manual:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&x =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &y =\<^sub>u 5\<rbrace>
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od;;
  (&x =\<^sub>u 5 \<and> &y =\<^sub>u 5)\<^sup>\<top>;;
  while &x <\<^sub>u &y * 2
  invr &x \<le>\<^sub>u &y * 2 \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x =\<^sub>u 10\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule seq_hoare_r[of _ _ true])
   apply (rule while_invr_hoare_r)
     unfolding lens_indep_def
     apply rel_auto
    apply rel_auto
   apply rel_auto
  apply (rule seq_hoare_r)
   apply (rule assume_hoare_r)
    apply (rule skip_hoare_r)
   apply rel_auto
  apply (rule while_invr_hoare_r)
    apply rel_auto
   apply rel_auto
  apply rel_auto
  done

lemma double_increment_method:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&x =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &y =\<^sub>u 5\<rbrace>
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od;;
  (&x =\<^sub>u 5 \<and> &y =\<^sub>u 5)\<^sup>\<top>;;
  while &x <\<^sub>u &y * 2
  invr &x \<le>\<^sub>u &y * 2 \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x =\<^sub>u 10\<rbrace>\<^sub>u"
  by (insert assms) vcg

section \<open>Testing COND+WHILE\<close>

lemma if_increment_manual:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&x =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &y =\<^sub>u 5\<rbrace>
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<triangleleft> b \<triangleright>\<^sub>r
  while &x <\<^sub>u &y * 2
  invr &x \<le>\<^sub>u &y * 2 \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x \<in>\<^sub>u {5, 10}\<^sub>u\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule cond_hoare_r)
   unfolding lens_indep_def
   apply (rule while_invr_hoare_r)
     apply rel_auto
    apply rel_auto
   apply rel_auto
  apply (rule while_invr_hoare_r)
    apply rel_auto
   apply rel_auto
  apply rel_auto
  done

lemma if_increment_method:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&x =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &y =\<^sub>u 5\<rbrace>
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<triangleleft> b \<triangleright>\<^sub>r
  while &x <\<^sub>u &y * 2
  invr &x \<le>\<^sub>u &y * 2 \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x \<in>\<^sub>u {5, 10}\<^sub>u\<rbrace>\<^sub>u"
  by (insert assms) vcg

end