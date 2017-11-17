section \<open>Examples using VCG for Partial Correctness\<close>

theory examples_vcg_Floyd
imports
  "../../../../../Backend/VCG/VCG_rel_Floyd"
  "../../../utils/vcg_helpers"
begin

subsection Increment

lemma increment_semimanual:
  assumes \<open>vwb_lens x\<close> and \<open>x \<bowtie> y\<close>
  shows
  \<open>\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x :== 0;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== (&x + 1) od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>u\<close>
  apply (insert assms)
  apply (rule hoare_post_weak)
   apply (rule seq_hoare_r)
    apply (rule assigns_floyd_r)
    apply solve_vcg
   apply (rule while_invr_hoare_r')
     apply solve_vcg
    apply (rule assigns_floyd_r)
    apply solve_vcg
   apply solve_vcg
  apply solve_vcg
  done

lemma increment_method:
  assumes \<open>vwb_lens x\<close> and \<open>x \<bowtie> y\<close>
  shows
  \<open>\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x :== 0;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== (&x + 1) od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>u\<close>
  by (insert assms) exp_vcg

subsection \<open>Even count\<close>

lemma even_count_method:
  assumes \<open>lens_indep_all [i, start, j, endd]\<close>
  shows
  \<open>\<lbrace>&start =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &endd =\<^sub>u 1\<rbrace>
    i :== &start;;
    j :== 0;;
    while &i <\<^sub>u &endd
    invr &start =\<^sub>u 0 \<and> &endd =\<^sub>u 1 \<and> &j =\<^sub>u ((&i + 1) - &start) div 2 \<and> &i \<le>\<^sub>u &endd \<and> &i \<ge>\<^sub>u &start
    do
      (if\<^sub>u &i mod 2 =\<^sub>u 0 then
        j :== (&j + 1)
      else
        II) (* THIS PRIORITY SUCKS! *)
      ;;
      i :== (&i + 1)
    od
  \<lbrace>&j =\<^sub>u 1\<rbrace>\<^sub>u\<close>
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
  mset array = mset old_array
\<and> sorted (take i array) (* everything up to i-1 is sorted *)
\<close>
abbreviation \<open>outer_invr\<^sub>u \<equiv> trop outer_invr\<close>

lemma outer_invr_init[vcg_simps]:
  assumes \<open>mset array = mset old_array\<close>
  shows \<open>outer_invr (Suc 0) array old_array\<close>
  unfolding outer_invr_def
  using assms
  by (metis sorted_single sorted_take take_0 take_Suc)

definition \<open>inner_invr i j array old_array \<equiv>
  i < length array
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

lemma inner_invr_step[vcg_simps]:
  assumes \<open>inner_invr i j array old_array\<close>
    and \<open>j > 0\<close>
    and \<open>array!(j - Suc 0) > array!j\<close>
  shows \<open>inner_invr i (j - Suc 0) (swap_at j array) old_array\<close>
  using assms unfolding inner_invr_def Let_def
  apply clarsimp
  apply (safe; (simp add: swap_at_def; fail)?)
proof goal_cases
  case 1
  then show ?case by (simp add: swap_at_def Multiset.mset_swap)
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
  have xs\<^sub>1'_is_aaker: \<open>xs\<^sub>1' = take (j - Suc 0) (swap_at j array)\<close>
    by (simp add: swap_at_def xs_butlast)
  have y_concat_xs\<^sub>2: \<open>y # xs\<^sub>2 = drop j (take (Suc i) (swap_at j array))\<close>
    using \<open>j > 0\<close>
    apply (auto simp: swap_at_def drop_take list_update_swap)
    by (smt "2"(3) "2"(4) Cons_nth_drop_Suc Suc_diff_Suc drop_take drop_update_cancel le_less_trans
        length_list_update lessI nth_list_update_eq take_Suc_Cons xs\<^sub>2_def y)
  from 2 show \<open>sorted (take (j - Suc 0) (swap_at j array) @ drop j (take (Suc i) (swap_at j array)))\<close>
    by (fold xs\<^sub>1_def xs\<^sub>2_def xs_butlast xs\<^sub>1'_is_aaker y_concat_xs\<^sub>2) (simp add: xs_last)
  {
    fix x
    assume \<open>x \<in> set (drop j (take (Suc i) (swap_at j array)))\<close>
    show \<open>swap_at j array!(j - Suc 0) < x\<close>
      by (smt "2"(2) "2"(3) "2"(4) "2"(7) One_nat_def \<open>x \<in> set (drop j (take (Suc i) (swap_at j
          array)))\<close> diff_le_self le_less_trans length_list_update nth_list_update_eq set_ConsD
          swap_at_def xs\<^sub>2_def y y_concat_xs\<^sub>2)
  }
qed

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
      and \<open>vwb_lens array\<close> and \<open>array \<sharp> old_array\<close>
      and \<open>i \<bowtie> array\<close> and \<open>i \<sharp> old_array\<close>
      and \<open>j \<bowtie> array\<close> and \<open>j \<sharp> old_array\<close>
  shows
  \<open>\<lbrace>&array =\<^sub>u old_array\<rbrace>
  i :== 1;;
  while &i <\<^sub>u #\<^sub>u(&array)
  invr outer_invr\<^sub>u (&i) (&array) old_array do
    j :== &i;;
    (while &j >\<^sub>u 0 \<and> &array(&j - 1)\<^sub>a >\<^sub>u &array(&j)\<^sub>a
    invr inner_invr\<^sub>u (&i) (&j) (&array) old_array do
      array :== swap_at\<^sub>u (&j) (&array);;
      j :== (&j - 1)
    od);;
    i :== (&i + 1)
  od
  \<lbrace>mset\<^sub>u(&array) =\<^sub>u mset\<^sub>u(old_array) \<and> sorted\<^sub>u(&array)\<rbrace>\<^sub>u\<close>
  by (insert assms) exp_vcg

subsubsection Quicksort

text \<open>It's more efficient to choose the pivot from the middle (or rather, the median of
first/middle/last, or even the nine-median method for large lists), but that is probably harder to
set up for verification; the partitioning mechanism is also not the most efficient, but seems to be
the simplest to handle.\<close>

definition \<open>qs_partition_invr A oldA lo hi i j pivot \<equiv>
  mset (slice lo (Suc hi) A) = mset (slice lo (Suc hi) oldA)
\<and> take lo A = take lo oldA
\<and> drop (Suc hi) A = drop (Suc hi) oldA (* pivot at hi doesn't get moved until after the loop, tho *)
\<and> lo \<le> i
\<and> i \<le> j
\<and> j \<le> hi
\<and> lo < hi
\<and> hi < length A
\<and> (\<forall>x \<in> set (slice lo i A). x \<le> pivot)
\<and> (\<forall>x \<in> set (slice i j A). pivot \<le> x)
\<and> pivot = A!hi
\<close>
abbreviation \<open>qs_partition_invr\<^sub>u \<equiv> sepop qs_partition_invr\<close>

lemma qs_partition_invr_init[vcg_simps]:
  assumes \<open>A = oldA\<close>
    and \<open>lo < hi\<close>
    and \<open>hi < length A\<close>
  shows \<open>qs_partition_invr A oldA lo hi lo lo (A!hi)\<close>
  using assms unfolding qs_partition_invr_def pivot_invr_def slice_def
  by (smt drop_all empty_iff length_take less_imp_le less_trans list.set(1) min.absorb2 order_refl)

lemma qs_partition_invr_step1[vcg_simps]:
  fixes A :: \<open>_::order list\<close>
  assumes \<open>qs_partition_invr A oldA lo hi i j pivot\<close>
    and \<open>j < hi\<close>
    and \<open>A!j < pivot\<close> \<comment> \<open>version requiring swap and i increment\<close>
  shows \<open>qs_partition_invr (swap i j A) oldA lo hi (Suc i) (Suc j) pivot\<close>
  using assms unfolding qs_partition_invr_def swap_def
  apply auto
  subgoal
    using Multiset.mset_swap[of \<open>j - lo\<close> \<open>slice lo (Suc hi) A\<close> \<open>i - lo\<close>]
    by (simp add: slice_update_extract)
  subgoal for x
    by (cases \<open>i = j\<close>) (auto simp: slice_suc2_eq)
  subgoal for x
    apply (cases \<open>i = j\<close>)
     apply (auto simp: slice_set_conv_nth nth_list_update)
     apply fastforce
    by (metis Suc_leD less_antisym less_trans)
  done

lemma qs_partition_invr_step2_helper:
  fixes A :: \<open>_::order list\<close>
  assumes \<open>\<forall>x \<in> set (slice i j A). p \<le> x\<close>
      and \<open>p \<le> A!j\<close>
      and \<open>j < length A\<close>
  shows \<open>\<forall>x \<in> set (slice i (Suc j) A). p \<le> x\<close>
  using assms
  by (cases \<open>i \<le> j\<close>) (auto simp: slice_suc2_eq)

lemma qs_partition_invr_step2[vcg_simps]:
  fixes A :: \<open>_::linorder list\<close> \<comment> \<open>Can't do everything with partial ordering.\<close>
  assumes \<open>qs_partition_invr A oldA lo hi i j pivot\<close>
    and \<open>j < hi\<close>
    and \<open>\<not> A!j < pivot\<close> \<comment> \<open>so array doesn't change this step\<close>
  shows \<open>qs_partition_invr A oldA lo hi i (Suc j) pivot\<close>
  using assms unfolding qs_partition_invr_def pivot_invr_def
  using qs_partition_invr_step2_helper
 by (auto simp: slice_suc2_eq)

lemma pivot_slice_swap:
  fixes xs :: \<open>_::order list\<close>
  assumes \<open>lo \<le> i\<close>
      and \<open>i \<le> hi\<close>
      and \<open>hi < length xs\<close>
      and \<open>\<forall>x \<in> set (slice lo i xs). x \<le> xs!hi\<close>
      and \<open>\<forall>x \<in> set (slice i hi xs). xs!hi \<le> x\<close>
  shows \<open>pivot_invr (i - lo) (slice lo (Suc hi) (swap i hi xs))\<close>
  using assms unfolding pivot_invr_def
  (* min_absorb1 and min.absorb1 seem interchangeable *)
  by (auto simp: min.absorb1) (meson assms(4) order_trans qs_partition_invr_step2_helper)

lemma qs_partition_invr_final[vcg_simps]:
  fixes A :: \<open>_::order list\<close>
  assumes \<open>qs_partition_invr A oldA lo hi i j pivot\<close>
      and \<open>\<not> j < hi\<close>
  shows \<open>mset (slice lo (Suc hi) (swap i hi A)) = mset (slice lo (Suc hi) oldA)\<close>
    and \<open>pivot_invr (i - lo) (slice lo (Suc hi) (swap i hi A))\<close>
    and \<open>drop (Suc hi) (swap i hi A) = drop (Suc hi) oldA\<close>
    and \<open>take lo (swap i hi A) = take lo oldA\<close>
  using assms unfolding qs_partition_invr_def
  by (auto simp: pivot_slice_swap)

lemma quicksort_partition[vcg_simps]:
  fixes pivot :: \<open>_::linorder \<Longrightarrow> _\<close>
  assumes \<open>lens_indep_all [i, j, res]\<close>
      and \<open>vwb_lens pivot\<close> and \<open>vwb_lens A\<close>
      and \<open>pivot \<bowtie> i\<close> and \<open>pivot \<bowtie> j\<close> and \<open>pivot \<bowtie> res\<close>
      and \<open>A \<sharp> oldA\<close> and \<open>A \<sharp> lo\<close> and \<open>A \<sharp> hi\<close>
      and \<open>i \<bowtie> A\<close> and \<open>i \<sharp> oldA\<close> and \<open>i \<sharp> lo\<close> and \<open>i \<sharp> hi\<close>
      and \<open>j \<bowtie> A\<close> and \<open>j \<sharp> oldA\<close> and \<open>j \<sharp> lo\<close> and \<open>j \<sharp> hi\<close>
      and \<open>pivot \<bowtie> A\<close> and \<open>pivot \<sharp> oldA\<close> and \<open>pivot \<sharp> lo\<close> and \<open>pivot \<sharp> hi\<close>
      and \<open>res \<bowtie> A\<close> and \<open>res \<sharp> oldA\<close> and \<open>res \<sharp> lo\<close> and \<open>res \<sharp> hi\<close>
  shows
  \<open>\<lbrace>&A =\<^sub>u oldA
\<and> lo <\<^sub>u hi
\<and> hi <\<^sub>u #\<^sub>u(&A)\<rbrace>
  pivot :== &A(hi)\<^sub>a;;
  i :== lo;;
  j :== lo;;
  (while &j <\<^sub>u hi invr qs_partition_invr\<^sub>u (&A) oldA lo hi (&i) (&j) (&pivot) do
    (if\<^sub>u &A(&j)\<^sub>a <\<^sub>u &pivot then
      A :== swap\<^sub>u (&i) (&j) (&A);;
      i :== (&i + 1);;
      j :== (&j + 1)
    else j :== (&j + 1));;
    (qs_partition_invr\<^sub>u (&A) oldA lo hi (&i) (&j) (&pivot))\<^sub>\<bottom>
  od);;
  A :== swap\<^sub>u (&i) hi (&A);; (* Don't need `pivot < A!i` check, it's a minor optimization *)
  res :== &i
  \<lbrace>mset\<^sub>u(slice\<^sub>u lo (hi + 1) (&A)) =\<^sub>u mset\<^sub>u(slice\<^sub>u lo (hi + 1) oldA)
\<and> take\<^sub>u(lo, &A) =\<^sub>u take\<^sub>u(lo, oldA)
\<and> drop\<^sub>u(hi + 1, &A) =\<^sub>u drop\<^sub>u(hi + 1, oldA)
\<and> pivot_invr\<^sub>u (&res - lo) (slice\<^sub>u lo (hi + 1) (&A))\<rbrace>\<^sub>u\<close>
  by (insert assms) exp_vcg

context
  fixes pivot :: \<open>'a::linorder \<Longrightarrow> 'c\<close>
     and i res j:: "nat \<Longrightarrow> 'c" and  A :: "'a list \<Longrightarrow> 'c"
     and oldA:: \<open> ('a list, 'c) uexpr\<close> and  lo hi:: \<open>(nat, 'c) uexpr\<close>
  assumes INDEP:\<open>lens_indep_all [i, j, res]\<close>
       \<open>vwb_lens pivot\<close>  \<open>vwb_lens A\<close>
       \<open>pivot \<bowtie> i\<close>  \<open>pivot \<bowtie> j\<close>  \<open>pivot \<bowtie> res\<close>
       \<open>A \<sharp> oldA\<close>  \<open>A \<sharp> lo\<close>  \<open>A \<sharp> hi\<close>
       \<open>i \<bowtie> A\<close>  \<open>i \<sharp> oldA\<close>  \<open>i \<sharp> lo\<close>  \<open>i \<sharp> hi\<close>
       \<open>j \<bowtie> A\<close>  \<open>j \<sharp> oldA\<close>  \<open>j \<sharp> lo\<close>  \<open>j \<sharp> hi\<close>
       \<open>pivot \<bowtie> A\<close>  \<open>pivot \<sharp> oldA\<close>  \<open>pivot \<sharp> lo\<close>  \<open>pivot \<sharp> hi\<close>
       \<open>res \<bowtie> A\<close>  \<open>res \<sharp> oldA\<close>  \<open>res \<sharp> lo\<close>  \<open>res \<sharp> hi\<close>

begin

definition partition:: \<open>'c hrel\<close> where
  \<open>partition =
    pivot :== &A(hi)\<^sub>a;;
  i :== lo;;
  j :== lo;;
  (while &j <\<^sub>u hi invr qs_partition_invr\<^sub>u (&A) oldA lo hi (&i) (&j) (&pivot) do
    (if\<^sub>u &A(&j)\<^sub>a <\<^sub>u &pivot then
      A :== swap\<^sub>u (&i) (&j) (&A);;
      i :== (&i + 1);;
      j :== (&j + 1)
    else j :== (&j + 1));;
    (qs_partition_invr\<^sub>u (&A) oldA lo hi (&i) (&j) (&pivot))\<^sub>\<bottom>
  od);;
  A :== swap\<^sub>u (&i) hi (&A);;
  res :== &i\<close>

lemma \<open>\<lbrace>
    &A =\<^sub>u oldA
  \<and> lo <\<^sub>u hi
  \<and> hi <\<^sub>u #\<^sub>u(&A)
\<rbrace>
  partition
\<lbrace>
    mset\<^sub>u(slice\<^sub>u lo (hi + 1) (&A)) =\<^sub>u mset\<^sub>u(slice\<^sub>u lo (hi + 1) oldA)
  \<and> take\<^sub>u(lo, &A) =\<^sub>u take\<^sub>u(lo, oldA)
  \<and> drop\<^sub>u(hi + 1, &A) =\<^sub>u drop\<^sub>u(hi + 1, oldA)
  \<and> pivot_invr\<^sub>u (&res - lo) (slice\<^sub>u lo (hi + 1) (&A))
\<rbrace>\<^sub>u\<close>
  unfolding partition_def
  by (insert INDEP) exp_vcg

end

definition \<open>qs_partition
  A lo hi (* params (lo and hi are uexprs rather than lenses!) *)
  pivot i j (* locals *)
  res (* return value *)
\<equiv>
block II (
  pivot :== &A(hi)\<^sub>a;;
  i :== lo;; (* keeping i at 0 or greater to avoid nat/int conversions; this did require reworking
              the algorithm slightly. *)
  j :== lo;;
  (while &j <\<^sub>u hi invr true do (* TODO: invariant *)
    (if\<^sub>u &A(&j)\<^sub>a <\<^sub>u &pivot then
      A :== swap\<^sub>u (&i) (&j) (&A);;
      i :== (&i + 1)
    else II);;
    j :== (&j + 1)
  od);;
  A :== swap\<^sub>u (&i) hi (&A);;
  res :== &i
)
(\<lambda> (s, _) _. i :== stet (&i) s;; (* these may not be needed as they're reset anyway *)
             j :== stet (&j) s;;
             pivot :== stet (&pivot) s)
(\<lambda> _ _. II)
\<close>

lemma quicksort_exp:
  assumes \<open>lens_indep_all [i, j, res]\<close> (* should res be in the alphabet? *)
      and \<open>vwb_lens array\<close> and \<open>vwb_lens pivot\<close>
      and \<open>pivot \<bowtie> i\<close> and \<open>pivot \<bowtie> j\<close> and \<open>pivot \<bowtie> res\<close>
      and \<open>i \<bowtie> array\<close> and \<open>i \<sharp> old_array\<close>
      and \<open>j \<bowtie> array\<close> and \<open>j \<sharp> old_array\<close>
      and \<open>lo \<bowtie> array\<close> and \<open>lo \<sharp> old_array\<close>
      and \<open>hi \<bowtie> array\<close> and \<open>hi \<sharp> old_array\<close>
      and \<open>pivot \<bowtie> array\<close> and \<open>pivot \<sharp> old_array\<close>
      and \<open>res \<bowtie> array\<close> and \<open>res \<sharp> old_array\<close>
  shows
  \<open>\<lbrace>(&array :\<^sub>u (_::linorder) list) =\<^sub>u old_array \<and> &lo \<le>\<^sub>u &hi \<and> &hi <\<^sub>u #\<^sub>u(&array)\<rbrace>
   \<nu> X \<bullet>
  if\<^sub>u &lo <\<^sub>u &hi then
    qs_partition array (&lo) (&hi) pivot i j res;;
    block II
      (hi :== (&res - 1);; X)
      (\<lambda> (s, _) _. hi :== stet (&hi) s;;
                   res :== stet (&res) s)
      (\<lambda> _ _. II);;
    block II
      (lo :== (&res + 1);; X)
      (\<lambda> (s, _) _. lo :== stet (&lo) s;;
                   res :== stet (&res) s)
      (\<lambda> _ _. II)
  else
    II
  \<lbrace>mset\<^sub>u(slice\<^sub>u (&lo) (&hi + 1) (&array)) =\<^sub>u mset\<^sub>u(slice\<^sub>u (&lo) (&hi + 1) old_array)
\<and> take\<^sub>u(&lo, &array) =\<^sub>u take\<^sub>u(&lo, old_array)
\<and> drop\<^sub>u(&hi + 1, &array) =\<^sub>u drop\<^sub>u(&hi + 1, old_array)
\<and> #\<^sub>u(&array) =\<^sub>u #\<^sub>u(old_array)
\<and> sorted\<^sub>u(slice\<^sub>u (&lo) (&hi + 1) (&array))\<rbrace>\<^sub>u\<close>
  unfolding qs_partition_def
  apply (insert assms)
  apply (rule nu_hoare_r[OF upred_taut_refl])
  apply exp_vcg

lemma quicksort:
  assumes \<open>lens_indep_all [i, j, res]\<close> (* should res be in the alphabet? *)
      and \<open>vwb_lens array\<close> and \<open>vwb_lens pivot\<close>
      and \<open>pivot \<bowtie> i\<close> and \<open>pivot \<bowtie> j\<close> and \<open>pivot \<bowtie> res\<close>
      and \<open>i \<bowtie> array\<close> and \<open>i \<sharp> old_array\<close>
      and \<open>j \<bowtie> array\<close> and \<open>j \<sharp> old_array\<close>
      and \<open>lo \<bowtie> array\<close> and \<open>lo \<sharp> old_array\<close>
      and \<open>hi \<bowtie> array\<close> and \<open>hi \<sharp> old_array\<close>
      and \<open>pivot \<bowtie> array\<close> and \<open>pivot \<sharp> old_array\<close>
      and \<open>res \<bowtie> array\<close> and \<open>res \<sharp> old_array\<close>
  shows
  \<open>\<lbrace>(&array :\<^sub>u (_::linorder) list) =\<^sub>u old_array \<and> &lo =\<^sub>u 0 \<and> &hi =\<^sub>u #\<^sub>u(&array) - 1\<rbrace>
   \<nu> X [undefined ''pre''] \<bullet>
  if\<^sub>u &lo <\<^sub>u &hi then
    qs_partition array (&lo) (&hi) pivot i j res;;
    block II
      (hi :== (&res - 1);; X)
      (\<lambda> (s, _) _. hi :== stet (&hi) s;;
                   res :== stet (&res) s)
      (\<lambda> _ _. II);;
    block II
      (lo :== (&res + 1);; X)
      (\<lambda> (s, _) _. lo :== stet (&lo) s;;
                   res :== stet (&res) s)
      (\<lambda> _ _. II)
  else
    II
  \<lbrace>mset\<^sub>u(&array) =\<^sub>u mset\<^sub>u(old_array) \<and> sorted\<^sub>u(&array)\<rbrace>\<^sub>u\<close>
  unfolding qs_partition_def
  apply (insert assms)
  apply exp_vcg

subsubsection \<open>Future: merge sort\<close>

end
