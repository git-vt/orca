section \<open>Examples for infixl seq (;;)\<close>

theory examples_infixl_seq
  imports "../hoare/utp_hoare_total"
begin

text \<open>Burkhart Wolff suggests infixl rather than infixr (like how seL4 does it)\<close>
no_notation useq (infixr ";;" 51)
notation useq (infixl ";;" 51)

text \<open>Variable swapping\<close>

lemma swap_test_manual1:
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

lemma swap_test_manual2:
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

end