section \<open>Helper definitions and lemmas\<close>

theory vcg_helpers
  imports utp_extensions
begin

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
  by (auto simp: sorted_append sorted_Cons) (smt One_nat_def Suc_pred diff_Suc_less
      dual_order.trans in_set_conv_nth last_conv_nth leD length_greater_0_conv not_less_eq_eq
      sorted_nth_mono)

section \<open>For sorting, etc.\<close>

text \<open>The below definition provides an easy-to-understand swap-elements-at-i-and-(i-1) function.\<close>
definition \<open>swap_at i xs = xs[i := xs!(i-1), i-1 := xs!i]\<close>
abbreviation \<open>swap_at\<^sub>u \<equiv> bop swap_at\<close>

text \<open>The below definition provides a more general swap function.\<close>
definition \<open>swap i j xs = xs[i := xs!j, j := xs!i]\<close>
abbreviation \<open>swap\<^sub>u \<equiv> trop swap\<close>

definition \<open>slice l u A \<equiv> drop l (take u A)\<close>
abbreviation \<open>slice\<^sub>u \<equiv> trop slice\<close>

definition \<open>pivot_invr i A \<equiv> \<forall>x \<in> set (take i A). \<forall>y \<in> set (drop i A). x \<le> y\<close>
abbreviation \<open>pivot_invr\<^sub>u \<equiv> bop pivot_invr\<close>

lemma slice_equal_indices[simp]: \<open>slice i i xs = []\<close>
  unfolding slice_def by auto

lemma slice_suc2_eq:
  assumes \<open>j < length xs\<close>
      and \<open>i \<le> j\<close>
    shows \<open>slice i (Suc j) xs = slice i j xs @ [xs!j]\<close>
  using assms unfolding slice_def
  by (metis diff_is_0_eq drop_0 drop_append length_take less_imp_le min.absorb2
      take_Suc_conv_app_nth)

lemma slice_update[simp]:
  assumes \<open>j \<le> k\<close>
  shows \<open>slice i j (xs[k := l]) = slice i j xs\<close>
  using assms unfolding slice_def by auto

lemma slice_update2[simp]:
  assumes \<open>k < i\<close>
  shows \<open>slice i j (xs[k := l]) = slice i j xs\<close>
  using assms unfolding slice_def
  by (simp add: drop_take)

lemma drop_set_conv_nth:
  \<open>set (drop i xs) = {xs!k | k. i \<le> k \<and> k < length xs}\<close>
  apply (induction xs rule: rev_induct)
   apply (auto simp: nth_append)
  by (metis (no_types, lifting) Suc_pred cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq
      drop_Cons' drop_Nil in_set_conv_nth length_drop length_pos_if_in_set lessI less_Suc0
      less_not_refl)

lemma take_set_conv_nth:
  \<open>set (take i xs) = {xs!k | k. k < min i (length xs)}\<close>
  apply (induction i)
   apply auto
   apply (smt in_set_conv_nth le_eq_less_or_eq length_take less_Suc_eq less_le_trans min.absorb2
      not_less_eq_eq nth_take take_all)
  using in_set_conv_nth by fastforce
 
lemma slice_set_conv_nth:
  \<open>set (slice i j xs) = {xs!k | k. i \<le> k \<and> k < j \<and> k < length xs}\<close>
  unfolding slice_def
  by (auto simp: drop_set_conv_nth take_set_conv_nth) force

lemma slice_update_extract:
  assumes \<open>lo \<le> i\<close>
     and \<open>i < hi\<close>
  shows \<open>slice lo hi (A[i := x]) = (slice lo hi A)[i-lo := x]\<close>
  using assms unfolding slice_def
  by (simp add: drop_update_swap take_update_swap)

lemma slice_length[simp]:
  assumes \<open>lo \<le> hi\<close>
      and \<open>hi \<le> length xs\<close>
  shows \<open>length (slice lo hi xs) = hi - lo\<close>
  using assms unfolding slice_def
  by auto

lemma nth_slice_offset[simp]:
  assumes \<open>i < hi - lo\<close>
      and \<open>lo \<le> hi\<close>
      and \<open>hi \<le> length xs\<close>
  shows \<open>(slice lo hi xs)!i = xs!(i + lo)\<close>
  using assms unfolding slice_def
  by (simp add: add.commute min.absorb2)

lemma swap_commute:
  \<open>swap i j xs = swap j i xs\<close>
  unfolding swap_def
  by (cases \<open>i = j\<close>) (auto simp: list_update_swap)

section \<open>Miscellaneous\<close>

lemma upred_taut_refl: \<open>`A \<Rightarrow> A`\<close>
  by pred_simp

text \<open>Minor helper for blocks.\<close>
abbreviation \<open>stet v s \<equiv> \<guillemotleft>\<lbrakk>v\<rbrakk>\<^sub>e s\<guillemotright>\<close>

end
