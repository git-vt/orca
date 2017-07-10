section \<open>Examples for infixl seq (;;)\<close>

theory examples_infixl_seq
  imports "../hoare/utp_hoare_total"
begin

text \<open>Burkhart Wolff suggests infixl rather than infixr (like how seL4 does it)\<close>
no_notation useq (infixr ";;" 51)
notation useq (infixl ";;" 51)

text \<open>Variable swapping\<close>

lemma swap_test1:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
  and "x \<bowtie> y" and "x \<bowtie> z" and "y \<bowtie> z"
  shows "\<lbrace>&x =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>b\<guillemotright>\<rbrace>
  z \<Midarrow> &x;;
  x \<Midarrow> &y;;
  y \<Midarrow> &z
  \<lbrace>&x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>a\<guillemotright>\<rbrace>\<^sub>D"
  apply (insert assms)
  apply (rule seq_hoare_r_t)
   apply (rule seq_hoare_r_t)
    defer
    apply (rule assigns_hoare_r'_t)
   apply (rule assigns_hoare_r'_t)
  apply (rule assigns_hoare_r_t)
  apply pred_simp
  apply (simp add: lens_indep_sym)
  done

lemma swap_test2:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
  and "x \<bowtie> y" and "x \<bowtie> z" and "y \<bowtie> z"
  shows "\<lbrace>&x =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>b\<guillemotright>\<rbrace>
  z \<Midarrow> &x;;
  x \<Midarrow> &y;;
  y \<Midarrow> &z
  \<lbrace>&x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>a\<guillemotright>\<rbrace>\<^sub>D"
  apply (insert assms)
  apply (rule seq_hoare_r_t)
   defer
   apply (rule assigns_hoare_r'_t)
  apply (rule seq_hoare_r_t)
   defer
   apply (rule assigns_hoare_r'_t)
  apply (rule assigns_hoare_r_t)
  apply pred_simp
  apply (simp add: lens_indep_sym)
  done

subsection \<open>Adding in loops\<close>

lemma increment:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x \<Midarrow> 0;;
  (&x =\<^sub>u 0 \<and> &y =\<^sub>u 5)\<^sup>\<top>\<^sup>C;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x \<Midarrow> &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>D"
  apply (insert assms)
  apply (rule seq_hoare_r_t)
   apply (rule seq_hoare_r_t[of _ _ true])
    apply (rule assigns_hoare_r_t)
    apply pred_auto
   apply (rule assume_hoare_r_t)
    apply (rule skip_hoare_r_t)
   apply rel_auto
  apply (rule while_invr_hoare_r_t)
    apply (rule assigns_hoare_r_t)
    unfolding lens_indep_def
    apply pred_auto
   apply pred_auto
  apply pred_auto
  done

lemma increment2:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x \<Midarrow> 0;;
  (&x =\<^sub>u 0 \<and> &y =\<^sub>u 5)\<^sup>\<top>\<^sup>C;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x \<Midarrow> &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>D"
  apply (insert assms)
  apply (rule seq_hoare_r_t)
   defer
   apply (rule while_invr_hoare_r_t)
     apply (rule assigns_hoare_r_t)
     unfolding lens_indep_def
     apply pred_auto
    defer
    apply pred_auto
   apply (rule seq_hoare_r_t)
    defer
    apply (rule assume_hoare_r_t)
     apply (rule skip_hoare_r_t)
    apply rel_auto
   apply pred_auto
  apply (rule assigns_hoare_r_t)
  apply pred_auto
  oops (*  (rule seq_hoare_r_t[of _ _ true]) is necessary to instantiate ?s27 *)

end