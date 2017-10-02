section \<open>Examples using ML-level VCG for Total Correctness\<close>

theory examples_vcg_total_Floyd
imports
  "../../../utils/utp_extensions"
  "../../../../../Backend/VCG/VCG_total_Floyd"
begin

subsection Increment

lemma increment_semimanual:
  assumes \<open>vwb_lens x\<close> and \<open>x \<bowtie> y\<close>
  shows
  \<open>\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x \<Midarrow> 0;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x \<Midarrow> (&x + 1) od
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
  do x \<Midarrow> (&x + 1) od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>A\<^sub>B\<^sub>R\<close>
  by (insert assms) exp_vcg

subsection \<open>Even count\<close>

lemma even_count_method:
  assumes \<open>lens_indep_all [i, start, j, endd]\<close>
  shows            
  \<open>\<lbrace>&start =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &endd =\<^sub>u 1\<rbrace>
    i \<Midarrow> &start;;
    j \<Midarrow> 0;;
    while &i <\<^sub>u &endd
    invr &start =\<^sub>u 0 \<and> &endd =\<^sub>u 1 \<and> &j =\<^sub>u ((&i + 1) - &start) div 2 \<and> &i \<le>\<^sub>u &endd \<and> &i \<ge>\<^sub>u &start
    do
      bif &i mod 2 =\<^sub>u 0 then
        j \<Midarrow> (&j + 1)
      else
        SKIP\<^sub>A\<^sub>B\<^sub>R
      eif;;
      i \<Midarrow> (&i + 1)
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

definition \<open>outer_invr i array old_array \<equiv>
  i > 0
\<and> mset array = mset old_array
\<and> sorted (take i array) (* everything up to i-1 is sorted *)
\<close>
abbreviation \<open>outer_invr\<^sub>u \<equiv> trop outer_invr\<close>

lemma outer_invr_init[vcg_simps]:
  assumes \<open>mset array = mset old_array\<close>
  shows \<open>outer_invr (Suc 0) array old_array\<close>
  unfolding outer_invr_def
  using assms
  by (metis One_nat_def sorted_single sorted_take take_0 take_Suc zero_less_one)

definition \<open>inner_invr i j array old_array \<equiv>
  i < length array
\<and> i > 0
\<and> i \<ge> j
\<and> mset array = mset old_array
\<and> (let xs\<^sub>1 = take j array; x = array!j; xs\<^sub>2 = drop (Suc j) (take (Suc i) array) in
  sorted (xs\<^sub>1 @ xs\<^sub>2) \<and> (\<forall>y \<in> set xs\<^sub>2. x < y))
\<close>
abbreviation \<open>inner_invr\<^sub>u \<equiv> qtop inner_invr\<close>

lemma inner_invr_init[vcg_simps]:
  assumes \<open>outer_invr i array old_array\<close>
      and \<open>j = i\<close>
      and \<open>i < length array\<close>
    shows \<open>inner_invr i j array old_array\<close>
  using assms unfolding outer_invr_def inner_invr_def
  by auto

text \<open>The below function provides an easy-to-understand swap-elements-at-i-and-(i-1) function.\<close>
definition \<open>swap_at i xs = xs[i := xs!(i-1), i-1 := xs!i]\<close>
abbreviation \<open>swap_at\<^sub>u \<equiv> bop swap_at\<close>

lemma inner_invr_step[vcg_simps]:
  assumes \<open>inner_invr i j array old_array\<close>
    and \<open>j > 0\<close>
    and \<open>array!(j- Suc 0) > array!j\<close>
  shows \<open>inner_invr i (j - Suc 0) (swap_at j array) old_array\<close>
  using assms unfolding inner_invr_def Let_def
  apply clarsimp
  apply (safe; (simp add: swap_at_def; fail)?)
proof goal_cases
  case 1
  then show ?case by (simp add: swap_at_def mset_swap)
next
  assume 2: \<open>0 < j\<close>
    \<open>array!j < array!(j - Suc 0)\<close>
    \<open>i < length array\<close>
    \<open>j \<le> i\<close>
    \<open>mset array = mset old_array\<close>
    \<open>sorted (take j array @ drop (Suc j) (take (Suc i) array))\<close>
    \<open>\<forall>x \<in> set (drop (Suc j) (take (Suc i) array)). array!j < x\<close>
  define xs\<^sub>1 where \<open>xs\<^sub>1 = take j array\<close>
  define xs\<^sub>2 where \<open>xs\<^sub>2 = drop (Suc j) (take (Suc i) array)\<close>
  define x where \<open>x = array ! j\<close>
  obtain xs\<^sub>1' y where xs_last: \<open>xs\<^sub>1 = xs\<^sub>1' @ [y]\<close>
    unfolding xs\<^sub>1_def using 2
    by (metis Suc_pred diff_le_self le_less_trans take_hd_drop)
  have xs_butlast: \<open>xs\<^sub>1' = take (j - Suc 0) array\<close>
    by (smt "2"(3) "2"(4) Suc_pred append1_eq_conv assms(2) diff_le_self le_less_trans take_hd_drop
        xs\<^sub>1_def xs_last)
  have y: \<open>y = array ! (j - Suc 0)\<close>
    by (metis (no_types, lifting) "2"(3) "2"(4) Cons_nth_drop_Suc One_nat_def Suc_pred assms(2)
        diff_le_self le_less_trans list.sel(1) nth_append_length take_hd_drop xs\<^sub>1_def xs_butlast
        xs_last)
  have xs\<^sub>1'_is_a_taker: \<open>xs\<^sub>1' = take (j - Suc 0) (swap_at j array)\<close>
    by (simp add: swap_at_def xs_butlast)
  have y_concat_xs\<^sub>2: \<open>y # xs\<^sub>2 = drop j (take (Suc i) (swap_at j array))\<close>
    using \<open>j > 0\<close>
    apply (auto simp: swap_at_def drop_take list_update_swap)
    by (smt "2"(3) "2"(4) Cons_nth_drop_Suc Suc_diff_Suc drop_take drop_update_cancel le_less_trans
        length_list_update lessI nth_list_update_eq take_Suc_Cons xs\<^sub>2_def y)
  from 2 show \<open>sorted (take (j - Suc 0) (swap_at j array) @ drop j (take (Suc i) (swap_at j array)))\<close>
    by (fold xs\<^sub>1_def xs\<^sub>2_def xs_butlast xs\<^sub>1'_is_a_taker y_concat_xs\<^sub>2) (simp add: xs_last)
  {
    fix x
    assume \<open>x \<in> set (drop j (take (Suc i) (swap_at j array)))\<close>
    show \<open>swap_at j array!(j - Suc 0) < x\<close>
      by (smt "2"(2) "2"(3) "2"(4) "2"(7) One_nat_def \<open>x \<in> set (drop j (take (Suc i) (swap_at j
          array)))\<close> diff_le_self le_less_trans length_list_update nth_list_update_eq set_ConsD
          swap_at_def xs\<^sub>2_def y y_concat_xs\<^sub>2)
  }
qed

lemma disjE1:
  assumes \<open>P \<or> Q\<close>
    and \<open>P \<Longrightarrow> R\<close>
    and \<open>\<not> P \<Longrightarrow> Q \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by blast

lemma insert_with_sorted:
  assumes \<open>sorted (xs\<^sub>1 @ xs\<^sub>2)\<close>
      and \<open>\<forall>y \<in> set xs\<^sub>2. x < y\<close>
      and \<open>x \<ge> last xs\<^sub>1\<close>
      and \<open>xs\<^sub>1 \<noteq> []\<close>
  shows \<open>sorted (xs\<^sub>1 @ x # xs\<^sub>2)\<close>
  using assms
  by (auto simp: sorted_append sorted_Cons) (meson order_trans sorted_last)

lemma outer_invr_step[vcg_simps]:
  assumes \<open>inner_invr i j array old_array\<close>
    and \<open>j = 0 \<or> \<not> array ! j < array ! (j - Suc 0)\<close>
  shows \<open>outer_invr (Suc i) array old_array\<close>
  using assms unfolding inner_invr_def outer_invr_def Let_def
  apply (erule_tac disjE1)
   apply auto
   apply (metis Cons_nth_drop_Suc Suc_leI drop_0 length_greater_0_conv length_take less_imp_le
      min.absorb2 nth_take sorted.simps)
  apply (drule (1) insert_with_sorted)
    apply auto
   apply (smt One_nat_def diff_Suc_less last_conv_nth le_less_trans length_take list.size(3)
      min.absorb2 not_le_imp_less not_less_iff_gr_or_eq nth_take)
  using take_take[symmetric, where n = j and m = \<open>Suc i\<close> and xs = \<open>array\<close>]
    id_take_nth_drop[where xs = \<open>take (Suc i) array\<close> and i = j]
  by (auto simp: min_def)

lemma outer_invr_final[vcg_dests]:
  assumes \<open>outer_invr i array old_array\<close>
      and \<open>\<not> i < length array\<close>
    shows \<open>mset array = mset old_array\<close>
      and \<open>sorted array\<close>
  using assms unfolding outer_invr_def
  by auto

lemma insertion_sort:
  assumes \<open>lens_indep_all [i, j]\<close>
      and \<open>vwb_lens array\<close>
      and \<open>vwb_lens x\<close> and \<open>x \<bowtie> i\<close> and \<open>x \<bowtie> j\<close>
      and \<open>i \<bowtie> array\<close>
      and \<open>x \<bowtie> array\<close>
      and \<open>j \<bowtie> array\<close>
  shows
  \<open>\<lbrace>&array =\<^sub>u \<guillemotleft>old_array\<guillemotright>\<rbrace>
  i \<Midarrow> 1;;
  while &i <\<^sub>u #\<^sub>u(&array)
  invr outer_invr\<^sub>u (&i) (&array) \<guillemotleft>old_array\<guillemotright> do
    j \<Midarrow> &i;;
    while &j >\<^sub>u 0 \<and> &array(&j - 1)\<^sub>a >\<^sub>u &array(&j)\<^sub>a
    invr inner_invr\<^sub>u (&i) (&j) (&array) \<guillemotleft>old_array\<guillemotright> do
      array \<Midarrow> swap_at\<^sub>u (&j) (&array);;
      j \<Midarrow> (&j - 1)
    od;;
    i \<Midarrow> (&i + 1)
  od
  \<lbrace>mset\<^sub>u(&array) =\<^sub>u mset\<^sub>u(\<guillemotleft>old_array\<guillemotright>) \<and> sorted\<^sub>u(&array)\<rbrace>\<^sub>A\<^sub>B\<^sub>R\<close>
  by (insert assms) exp_vcg

subsubsection Quicksort

text \<open>The below function provides a more general swap\<^sub>u function.\<close>
definition \<open>swap xs i j = xs[i := xs!j, j := xs!i]\<close>
abbreviation \<open>swap\<^sub>u \<equiv> trop swap\<close>

(* more efficient to choose the pivot from the middle (or rather, the median of first/middle/last,
or even the nine-median method for large lists), but that's probably harder to set up for
verification *)
definition \<open>qs_partition
  A lo hi (* params (lo and hi are uexprs rather than lenses!) *)
  pivot i j (* locals *)
  res (* return value *)
\<equiv>
bob
INIT II
BODY
  pivot \<Midarrow> (&A :\<^sub>u 'a::ord list)(hi)\<^sub>a;;
  i \<Midarrow> (lo - 1);;
  j \<Midarrow> lo;;
  while &j <\<^sub>u hi invr true do (* TODO: invariant *)
    bif &A(&j)\<^sub>a <\<^sub>u &pivot then
      i \<Midarrow> (&i + 1);;
      A \<Midarrow> swap\<^sub>u (&A) (&i) (&j)
    else II eif
  od;;
  bif &A(hi)\<^sub>a <\<^sub>u &A(&i + 1)\<^sub>a then
      A \<Midarrow> swap\<^sub>u (&A) (&i + 1) hi
  else II eif;;
  res \<Midarrow> (&i + 1)
RESTORE \<lambda> (s, _) _. i \<Midarrow> cp_des (&i) s;; (* these may not be needed as they're reset anyway *)
                    j \<Midarrow> cp_des (&j) s;;
                    pivot \<Midarrow> cp_des (&pivot) s
RETURN \<lambda> _ _. II
eob\<close>

definition \<open>qsort
  A lo hi
  pivot i j (* locals *)
  res (* return value of inner function *)
\<equiv>
\<nu> X \<bullet>
bif &lo <\<^sub>u &hi then
  qs_partition A (&lo) (&hi) pivot i j res;;
  bob INIT II BODY
    hi \<Midarrow> (&res - 1);;
    X
  RESTORE \<lambda> (s, _) _. hi \<Midarrow> cp_des (&hi) s;;
                      res \<Midarrow> cp_des (&res) s
  RETURN \<lambda> _ _. II
  eob;;
  bob INIT II BODY
    lo \<Midarrow> (&res + 1);;
    X
  RESTORE \<lambda> (s, _) _. lo \<Midarrow> cp_des (&lo) s;;
                      res \<Midarrow> cp_des (&res) s
  RETURN \<lambda> _ _. II
  eob;;
  X
else
  II
eif
\<close>

lemma quicksort:
  assumes \<open>lens_indep_all [i, j, res]\<close> (* should res be in the alphabet? *)
      and \<open>vwb_lens array\<close> and \<open>vwb_lens pivot\<close>
      and \<open>pivot \<bowtie> i\<close> and \<open>pivot \<bowtie> j\<close> and \<open>pivot \<bowtie> res\<close>
      and \<open>i \<bowtie> array\<close>
      and \<open>j \<bowtie> array\<close>
      and \<open>lo \<bowtie> array\<close>
      and \<open>hi \<bowtie> array\<close>
      and \<open>pivot \<bowtie> array\<close>
      and \<open>res \<bowtie> array\<close>
  shows
  \<open>\<lbrace>&array =\<^sub>u \<guillemotleft>old_array\<guillemotright> \<and> &lo =\<^sub>u 0 \<and> &hi =\<^sub>u #\<^sub>u(&array) - 1\<rbrace>
    qsort A lo hi pivot i j res
  \<lbrace>mset\<^sub>u(&array) =\<^sub>u mset\<^sub>u(\<guillemotleft>old_array\<guillemotright>) \<and> sorted\<^sub>u(&array)\<rbrace>\<^sub>A\<^sub>B\<^sub>R\<close>
  unfolding qsort_def qs_partition_def
  apply (insert assms)
  apply exp_vcg

subsubsection \<open>Future: merge sort\<close>

end
