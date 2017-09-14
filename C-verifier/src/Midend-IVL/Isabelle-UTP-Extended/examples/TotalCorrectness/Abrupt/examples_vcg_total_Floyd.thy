section \<open>Examples using ML-level VCG for Total Correctness\<close>

theory examples_vcg_total_Floyd
  imports "../../../../../Backend/VCG/VCG_total_Floyd"
    "~~/src/HOL/Library/Multiset"
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

subsection \<open>Even count\<close>

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
  apply (insert assms)
  apply exp_vcg
   apply solve_vcg
   apply (elim disjE conjE) (* auto seems to go faster with this *)
    apply auto[1]
   apply (simp add: mod_pos_pos_trivial)
  apply solve_vcg
  done

subsection Sorting

text \<open>We need multisets for concise list invariants. Also, int/nat conversion is sometimes needed as
some loop methods mix array indices and loop variables (which sometimes rely on going below 0 for
termination).\<close>

syntax
  "_umset" :: \<open>('a list, '\<alpha>) uexpr \<Rightarrow> ('a multiset, '\<alpha>) uexpr\<close> ("mset\<^sub>u'(_')")
  "_uof_nat" :: \<open>(nat, '\<alpha>) uexpr \<Rightarrow> (int, '\<alpha>) uexpr\<close> ("int\<^sub>u'(_')")
  "_uof_int" :: \<open>(int, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr\<close> ("nat\<^sub>u'(_')")
translations
  "mset\<^sub>u(x)" == "CONST uop CONST mset x"
  "int\<^sub>u(n)" == "CONST uop CONST int n"
  "nat\<^sub>u(i)" == "CONST uop CONST nat i"

lemma insertion_sort:
  assumes \<open>lens_indep_all [i, x]\<close>
      and \<open>lens_indep_all [array, old_array]\<close>
      and \<open>vwb_lens j\<close> and \<open>i \<bowtie> j\<close> and \<open>x \<bowtie> j\<close>
      and \<open>i \<bowtie> array\<close> and \<open>i \<bowtie> old_array\<close>
      and \<open>x \<bowtie> array\<close> and \<open>x \<bowtie> old_array\<close>
      and \<open>j \<bowtie> array\<close> and \<open>j \<bowtie> old_array\<close>
  shows
  \<open>\<lbrace>#\<^sub>u(&array) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> mset\<^sub>u(&array) =\<^sub>u mset\<^sub>u(&old_array)\<rbrace>
  i \<Midarrow> 1;;
  while &i <\<^sub>u #\<^sub>u(&array)
  invr &i >\<^sub>u 0 \<and> #\<^sub>u(&array) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> mset\<^sub>u(&array) =\<^sub>u mset\<^sub>u(&old_array) \<and> sorted\<^sub>u(take\<^sub>u(&i-1, &array)) do
    x \<Midarrow> &array\<lparr>&i\<rparr>\<^sub>u;;
    j \<Midarrow> int\<^sub>u(&i - 1);;
    while &j \<ge>\<^sub>u 0 \<and> &x <\<^sub>u &array\<lparr>nat\<^sub>u(&j)\<rparr>\<^sub>u
    invr &i <\<^sub>u #\<^sub>u(&array) \<and> &i >\<^sub>u 0 \<and> &i >\<^sub>u nat\<^sub>u(&j) \<and> #\<^sub>u(&array) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> sorted\<^sub>u(take\<^sub>u(&i-1, &array)) do
      array \<Midarrow> &array(nat\<^sub>u(&j+1) \<mapsto> &array\<lparr>nat\<^sub>u(&j)\<rparr>\<^sub>u)\<^sub>u;;
      j \<Midarrow> &j - 1
    od;;
    array \<Midarrow> &array(nat\<^sub>u(&j+1) \<mapsto> &x)\<^sub>u;;
    i \<Midarrow> &i + 1
  od
  \<lbrace>#\<^sub>u(&array) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> sorted\<^sub>u(&array) \<and> mset\<^sub>u(&array) =\<^sub>u mset\<^sub>u(&old_array)\<rbrace>\<^sub>A\<^sub>B\<^sub>R\<close>
  apply (insert assms)
  apply exp_vcg
     apply solve_vcg
     apply (elim disjE conjE) (* makes auto slightly faster here *)
     apply auto[1] (* simp: sorted_list_dupl doesn't help *)

end
