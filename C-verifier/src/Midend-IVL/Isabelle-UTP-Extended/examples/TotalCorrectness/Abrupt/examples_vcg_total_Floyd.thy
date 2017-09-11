section \<open>Examples using ML-level VCG for Total Correctness\<close>

theory examples_vcg_total_Floyd
  imports "../../../../../Backend/VCG/VCG_total_Floyd"
begin

subsection Increment

lemma increment_semimanual:
  assumes \<open>vwb_lens x\<close> and \<open>x \<bowtie> y\<close>
  shows
  \<open>\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x \<Midarrow> 0;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x \<Midarrow> &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>A\<^sub>B\<^sub>R\<close>
  apply (insert assms)
  apply (rule hoare_post_weak_t)
   apply (rule seq_hoare_r_t)
    apply (rule assigns_abr_floyd_r_t)
    apply solve_vcg
   apply (rule while_invr_hoare_r_t')
     apply solve_vcg
    apply (rule assigns_abr_floyd_r_t)
    apply solve_vcg
   apply solve_vcg
  apply solve_vcg
  done

lemma increment_method:
  assumes \<open>vwb_lens x\<close> and \<open>x \<bowtie> y\<close>
  shows
  \<open>\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x \<Midarrow> 0;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x \<Midarrow> &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>A\<^sub>B\<^sub>R\<close>
  apply (insert assms)
  by exp_vcg

lemma even_count_method:
  assumes \<open>lens_indep_all [i, start, j, endd]\<close>
  shows            
  \<open>\<lbrace>&start =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &endd =\<^sub>u 1\<rbrace>
    i \<Midarrow> &start;;
    j \<Midarrow> 0;;
    while &i <\<^sub>u &endd
    invr &start =\<^sub>u 0 \<and> &endd =\<^sub>u 1 \<and> &j =\<^sub>u (((&i + 1) - &start) div 2) \<and> &i \<le>\<^sub>u &endd \<and> &i \<ge>\<^sub>u &start
    do
      bif &i mod 2 =\<^sub>u 0 then
        j \<Midarrow> &j + 1
      else
        SKIP\<^sub>A\<^sub>B\<^sub>R
      eif;;
      i \<Midarrow> &i + 1
    od
  \<lbrace>&j =\<^sub>u 1\<rbrace>\<^sub>A\<^sub>B\<^sub>R\<close>
  apply (insert assms) unfolding lens_indep_all_alt
  apply exp_vcg
   apply solve_vcg 
   apply (elim disjE conjE)
    apply simp
    apply auto[1]
   apply (simp add: mod_pos_pos_trivial)
  apply solve_vcg
  done
    
end
