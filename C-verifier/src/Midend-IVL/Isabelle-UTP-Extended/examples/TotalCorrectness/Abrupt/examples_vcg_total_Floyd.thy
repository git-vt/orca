section \<open>Examples using ML-level VCG for Total Correctness\<close>

theory examples_vcg_total_Floyd
imports
  "~~/src/HOL/Library/Multiset"
  "../../../../../Backend/VCG/VCG_total_Floyd"
begin

recall_syntax \<comment> \<open>Fixes notation issue with inclusion of HOL libraries.\<close>
 (*TODO @Yakoub: Fix the F** of the priorities of the syntax*)
subsection Increment

lemma increment_semimanual:
  assumes \<open>vwb_lens x\<close> and \<open>x \<bowtie> y\<close>
  shows
  \<open>\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x \<Midarrow> 0;;
  while &x <\<^sub>u &y
  invr (&x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5)
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
    invr &start =\<^sub>u 0 \<and> &endd =\<^sub>u 1 \<and> &j =\<^sub>u (((&i + 1) - &start) div 2) \<and> &i \<le>\<^sub>u &endd \<and> &i \<ge>\<^sub>u &start
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

text \<open>We need multisets for concise list invariants. Also, int/nat conversion is sometimes needed as
some loop methods mix array indices and loop variables (which sometimes rely on going below 0 for
termination).\<close>

syntax
  "_umset" :: \<open>('a list, '\<alpha>) uexpr \<Rightarrow> ('a multiset, '\<alpha>) uexpr\<close> ("mset\<^sub>u'(_')")
  "_unat" :: \<open>(nat, '\<alpha>) uexpr \<Rightarrow> (int, '\<alpha>) uexpr\<close> ("int\<^sub>u'(_')")
  "_uint" :: \<open>(int, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr\<close> ("nat\<^sub>u'(_')")
translations
  "mset\<^sub>u(x)" == "CONST uop CONST mset x"
  "int\<^sub>u(n)" == "CONST uop CONST int n"
  "nat\<^sub>u(i)" == "CONST uop CONST nat i"

subsubsection \<open>Extra stuff to work more-arg functions into UTP\<close>

lift_definition qiop ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f) \<Rightarrow>
   ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr \<Rightarrow> ('d, '\<alpha>) uexpr \<Rightarrow> ('e, '\<alpha>) uexpr \<Rightarrow>
   ('f, '\<alpha>) uexpr\<close>
  is \<open>\<lambda>f u v w x y b. f (u b) (v b) (w b) (x b) (y b)\<close> .
lift_definition sxop ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g) \<Rightarrow>
   ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr \<Rightarrow> ('d, '\<alpha>) uexpr \<Rightarrow> ('e, '\<alpha>) uexpr \<Rightarrow>
   ('f, '\<alpha>) uexpr \<Rightarrow> ('g, '\<alpha>) uexpr\<close>
  is \<open>\<lambda>f u v w x y z b. f (u b) (v b) (w b) (x b) (y b) (z b)\<close> .
update_uexpr_rep_eq_thms \<comment> \<open>Necessary to get the above utilized by {pred,rel}_{auto,simp}\<close>

text \<open>The below lemmas do not seem useful in general but are included for completeness.\<close>
lemma qiop_ueval [ueval]: \<open>\<lbrakk>qiop f v x y z w\<rbrakk>\<^sub>eb = f (\<lbrakk>v\<rbrakk>\<^sub>eb) (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb) (\<lbrakk>z\<rbrakk>\<^sub>eb) (\<lbrakk>w\<rbrakk>\<^sub>eb)\<close>
  by transfer simp

lemma subst_qiop [usubst]: \<open>\<sigma> \<dagger> qiop f t u v w x = qiop f (\<sigma> \<dagger> t) (\<sigma> \<dagger> u) (\<sigma> \<dagger> v) (\<sigma> \<dagger> w) (\<sigma> \<dagger> x)\<close>
  by transfer simp

lemma unrest_qiop [unrest]: \<open>\<lbrakk>x \<sharp> t; x \<sharp> u; x \<sharp> v; x \<sharp> w; x \<sharp> y\<rbrakk> \<Longrightarrow> x \<sharp> qiop f t u v w y\<close>
  by transfer simp

lemma aext_qiop [alpha]:
  \<open>qiop f t u v w x \<oplus>\<^sub>p a = qiop f (t \<oplus>\<^sub>p a) (u \<oplus>\<^sub>p a) (v \<oplus>\<^sub>p a) (w \<oplus>\<^sub>p a) (x \<oplus>\<^sub>p a)\<close>
  by pred_auto

lemma lit_qiop_simp [lit_simps]:
  \<open>\<guillemotleft>i x y z u t\<guillemotright> = qiop i \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright> \<guillemotleft>z\<guillemotright> \<guillemotleft>u\<guillemotright> \<guillemotleft>t\<guillemotright>\<close>
  by transfer simp

lemma sxop_ueval [ueval]: \<open>\<lbrakk>sxop f v x y z w t\<rbrakk>\<^sub>eb = f (\<lbrakk>v\<rbrakk>\<^sub>eb) (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb) (\<lbrakk>z\<rbrakk>\<^sub>eb) (\<lbrakk>w\<rbrakk>\<^sub>eb) (\<lbrakk>t\<rbrakk>\<^sub>eb)\<close>
  by transfer simp

lemma subst_sxop [usubst]:
  \<open>\<sigma> \<dagger> sxop f t u v w x y = sxop f (\<sigma> \<dagger> t) (\<sigma> \<dagger> u) (\<sigma> \<dagger> v) (\<sigma> \<dagger> w) (\<sigma> \<dagger> x) (\<sigma> \<dagger> y)\<close>
  by transfer simp

lemma unrest_sxop [unrest]: \<open>\<lbrakk>x \<sharp> t; x \<sharp> u; x \<sharp> v; x \<sharp> w; x \<sharp> y; x \<sharp> z\<rbrakk> \<Longrightarrow> x \<sharp> sxop f t u v w y z\<close>
  by transfer simp

lemma aext_sxop [alpha]:
  \<open>sxop f t u v w x y \<oplus>\<^sub>p a = sxop f (t \<oplus>\<^sub>p a) (u \<oplus>\<^sub>p a) (v \<oplus>\<^sub>p a) (w \<oplus>\<^sub>p a) (x \<oplus>\<^sub>p a) (y \<oplus>\<^sub>p a)\<close>
  by pred_auto

lemma lit_sxop_simp [lit_simps]:
  \<open>\<guillemotleft>i x y z u t v\<guillemotright> = sxop i \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright> \<guillemotleft>z\<guillemotright> \<guillemotleft>u\<guillemotright> \<guillemotleft>t\<guillemotright> \<guillemotleft>v\<guillemotright>\<close>
  by transfer simp

subsubsection \<open>Actual proofs\<close>

definition \<open>outer_invr' i array old_array \<equiv>
  i > 0
\<and> mset array = mset old_array
\<and> sorted (take i array) (* everything up to i-1 is sorted *)
\<close>
abbreviation \<open>outer_invr \<equiv> trop outer_invr'\<close>

lemma outer_invr_init[vcg_simps]:
  assumes \<open>mset array = mset old_array\<close>
  shows \<open>outer_invr' (Suc 0) array old_array\<close>
  unfolding outer_invr'_def
  using assms
  by (metis One_nat_def sorted_single sorted_take take_0 take_Suc zero_less_one)

definition \<open>inner_invr' i j array old_array \<equiv>
  i < length array
\<and> i > 0
\<and> i \<ge> j
\<and> mset array = mset old_array
\<and> (let xs\<^sub>1 = take j array; x = array!j; xs\<^sub>2 = drop (Suc j) (take (Suc i) array) in
  sorted (xs\<^sub>1 @ xs\<^sub>2) \<and> (\<forall>y \<in> set xs\<^sub>2. x < y))
\<close>
abbreviation \<open>inner_invr \<equiv> qtop inner_invr'\<close>

lemma inner_invr_init[vcg_simps]:
  assumes \<open>outer_invr' i array old_array\<close>
      and \<open>j = i\<close>
      and \<open>i < length array\<close>
    shows \<open>inner_invr' i j array old_array\<close>
  using assms unfolding outer_invr'_def inner_invr'_def
  by auto

text \<open>The below function provides an easy-to-understand swap-elements-at-i-and-(i-1) function.\<close>
definition \<open>swap_at' i xs = xs[i := xs!(i-1), i-1 := xs!i]\<close>
abbreviation \<open>swap_at \<equiv> bop swap_at'\<close>
  
lemma inner_invr_step[vcg_simps]:
  assumes \<open>inner_invr' i j array old_array\<close>
    and \<open>j > 0\<close>
    and \<open>array!(j- Suc 0) > array!j\<close>
  shows \<open>inner_invr' i (j - Suc 0) (swap_at' j array) old_array\<close>
  using assms unfolding inner_invr'_def Let_def
  apply clarsimp
  apply (safe; (simp add: swap_at'_def; fail)?)
proof goal_cases
  case 1
  then show ?case by (simp add: swap_at'_def mset_swap)
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
  have xs\<^sub>1'_is_a_taker: \<open>xs\<^sub>1' = take (j - Suc 0) (swap_at' j array)\<close>
    by (simp add: swap_at'_def xs_butlast)
  have y_concat_xs\<^sub>2: \<open>y # xs\<^sub>2 = drop j (take (Suc i) (swap_at' j array))\<close>
    using \<open>j > 0\<close>
    apply (auto simp: swap_at'_def drop_take list_update_swap)
    by (smt "2"(3) "2"(4) Cons_nth_drop_Suc Suc_diff_Suc drop_take drop_update_cancel le_less_trans
        length_list_update lessI nth_list_update_eq take_Suc_Cons xs\<^sub>2_def y)
  from 2 show \<open>sorted (take (j - Suc 0) (swap_at' j array) @ drop j (take (Suc i) (swap_at' j array)))\<close>
    by (fold xs\<^sub>1_def xs\<^sub>2_def xs_butlast xs\<^sub>1'_is_a_taker y_concat_xs\<^sub>2) (simp add: xs_last)
  {
    fix x
    assume \<open>x \<in> set (drop j (take (Suc i) (swap_at' j array)))\<close>
    show \<open>swap_at' j array!(j - Suc 0) < x\<close>
      by (smt "2"(2) "2"(3) "2"(4) "2"(7) One_nat_def \<open>x \<in> set (drop j (take (Suc i) (swap_at' j
          array)))\<close> diff_le_self le_less_trans length_list_update nth_list_update_eq set_ConsD
          swap_at'_def xs\<^sub>2_def y y_concat_xs\<^sub>2)
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
  assumes \<open>inner_invr' i j array old_array\<close>
    and \<open>j = 0 \<or> \<not> array ! j < array ! (j - Suc 0)\<close>
  shows \<open>outer_invr' (Suc i) array old_array\<close>
  using assms unfolding inner_invr'_def outer_invr'_def Let_def
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
  assumes \<open>outer_invr' i array old_array\<close>
      and \<open>\<not> i < length array\<close>
    shows \<open>mset array = mset old_array\<close>
      and \<open>sorted array\<close>
  using assms unfolding outer_invr'_def
  by auto

lemma insertion_sort:
  assumes \<open>lens_indep_all [i, j]\<close>
      and \<open>lens_indep_all [array, old_array]\<close>
      and \<open>vwb_lens x\<close> and \<open>x \<bowtie> i\<close> and \<open>x \<bowtie> j\<close>
      and \<open>i \<bowtie> array\<close> and \<open>i \<bowtie> old_array\<close>
      and \<open>x \<bowtie> array\<close> and \<open>x \<bowtie> old_array\<close>
      and \<open>j \<bowtie> array\<close> and \<open>j \<bowtie> old_array\<close>
  shows
  \<open>\<lbrace>mset\<^sub>u(&array) =\<^sub>u mset\<^sub>u(&old_array)\<rbrace>
  i \<Midarrow> 1;;
  while &i <\<^sub>u #\<^sub>u(&array)
  invr outer_invr (&i) (&array) (&old_array) do
    j \<Midarrow> &i;;
    while (&j) >\<^sub>u 0 \<and> &array(&j - 1)\<^sub>a >\<^sub>u &array(&j)\<^sub>a
    invr inner_invr (&i) (&j) (&array) (&old_array) do
      array \<Midarrow> swap_at (&j) (&array);;
      j \<Midarrow> (&j - 1)
    od;;
    i \<Midarrow> (&i + 1)
  od
  \<lbrace>mset\<^sub>u(&array) =\<^sub>u mset\<^sub>u(&old_array) \<and> sorted\<^sub>u(&array)\<rbrace>\<^sub>A\<^sub>B\<^sub>R\<close>
  by (insert assms) exp_vcg

subsubsection \<open>Another insertion sort style\<close>

text \<open>This version of insertion sort does not use swapping, rather a shifting up of values and then
inserting the desired value in the right place.\<close>

definition \<open>inner_invr2' i j x array old_array \<equiv>
  i < length array
\<and> i > 0
\<and> i > nat j
(* below is not right (needs to use x), also needs some connection to old_array with mset somehow *)
\<and> (let xs\<^sub>1 = take (nat j) array; z = array!(nat j); xs\<^sub>2 = drop (Suc (nat j)) (take (Suc i) array) in
  sorted (xs\<^sub>1 @ xs\<^sub>2) \<and> (\<forall>y \<in> set xs\<^sub>2. z < y))
\<close>
abbreviation \<open>inner_invr2 \<equiv> qiop inner_invr2'\<close>

lemma inner_invr2_init[vcg_simps]:
  assumes \<open>outer_invr' i array old_array\<close>
      and \<open>nat j = i - 1\<close>
      and \<open>i < length array\<close>
      and \<open>x = array ! i\<close>
    shows \<open>inner_invr2' i j x array old_array\<close>
  using assms unfolding inner_invr2'_def outer_invr'_def
    
lemma inner_invr2_step[vcg_simps]:
  assumes \<open>inner_invr2' i j x array old_array\<close>
    and \<open>j \<ge> 0\<close>
  shows \<open>inner_invr2' i (j - 1) x (array[nat (j+1) := array!(nat j)]) old_array\<close>
  using assms unfolding inner_invr2'_def

lemma outer_invr2_step[vcg_simps]:
  assumes \<open>inner_invr2' i j x array old_array\<close>
      and \<open>j < 0 \<or> x \<le> array!(nat j)\<close>
    shows \<open>outer_invr' (Suc i) (array[nat (j + 1) := x]) old_array\<close>
  using assms unfolding inner_invr2'_def outer_invr'_def

lemma insertion_sort:
  assumes \<open>lens_indep_all [i, x]\<close>
      and \<open>lens_indep_all [array, old_array]\<close>
      and \<open>vwb_lens j\<close> and \<open>i \<bowtie> j\<close> and \<open>x \<bowtie> j\<close>
      and \<open>i \<bowtie> array\<close> and \<open>i \<bowtie> old_array\<close>
      and \<open>x \<bowtie> array\<close> and \<open>x \<bowtie> old_array\<close>
      and \<open>j \<bowtie> array\<close> and \<open>j \<bowtie> old_array\<close>
  shows
  \<open>\<lbrace>mset\<^sub>u(&array) =\<^sub>u mset\<^sub>u(&old_array)\<rbrace>
  i \<Midarrow> 1;;
  while &i <\<^sub>u #\<^sub>u(&array)
  invr outer_invr &i &array &old_array do
    x \<Midarrow> &array(&i)\<^sub>a;;
    j \<Midarrow> int\<^sub>u(&i - 1);;
    while &j \<ge>\<^sub>u 0 \<and> &x <\<^sub>u &array(nat\<^sub>u(&j))\<^sub>a
    invr inner_invr2 &i &j &x &array &old_array do
      array \<Midarrow> &array(nat\<^sub>u(&j+1) \<mapsto> &array(nat\<^sub>u(&j))\<^sub>a)\<^sub>u;;
      j \<Midarrow> (&j - 1)
    od;;
    array \<Midarrow> &array(nat\<^sub>u(&j+1) \<mapsto> &x)\<^sub>u;;
    i \<Midarrow> (&i + 1)
  od
  \<lbrace>sorted\<^sub>u(&array) \<and> mset\<^sub>u(&array) =\<^sub>u mset\<^sub>u(&old_array)\<rbrace>\<^sub>A\<^sub>B\<^sub>R\<close>
  apply (insert assms)
  apply exp_vcg

subsubsection \<open>Future: merge sort, quicksort\<close>

end
