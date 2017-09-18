section \<open>Examples using ML-level VCG for Total Correctness\<close>

theory examples_vcg_total_Floyd
imports
  "~~/src/HOL/Library/Multiset"
  "../../../../../Backend/VCG/VCG_total_Floyd"
begin

recall_syntax (* Fixes purge_notation issue with inclusion of HOL libraries. *)

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

subsubsection \<open>Extra stuff to work five-arg functions into UTP\<close>

lift_definition qiop ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f) \<Rightarrow>
   ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr \<Rightarrow> ('d, '\<alpha>) uexpr \<Rightarrow> ('e, '\<alpha>) uexpr \<Rightarrow>
   ('f, '\<alpha>) uexpr\<close>
  is \<open>\<lambda>f u v w x y b. f (u b) (v b) (w b) (x b) (y b)\<close> .
update_uexpr_rep_eq_thms \<comment> \<open>Necessary to get the above utilized by {pred,rel}_{auto,simp}\<close>

text \<open>The below lemmas do not seem useful in general but are included for completeness.\<close>
lemma qiop_ueval [ueval]: \<open>\<lbrakk>qiop f v x y z w\<rbrakk>\<^sub>eb = f (\<lbrakk>v\<rbrakk>\<^sub>eb) (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb) (\<lbrakk>z\<rbrakk>\<^sub>eb) (\<lbrakk>w\<rbrakk>\<^sub>eb)\<close>
  by transfer simp

lemma subst_qiop [usubst]: \<open>\<sigma> \<dagger> qiop f t u v w x = qiop f (\<sigma> \<dagger> t) (\<sigma> \<dagger> u) (\<sigma> \<dagger> v) (\<sigma> \<dagger> w) (\<sigma> \<dagger> x)\<close>
  by transfer simp

lemma unrest_qiop [unrest]: \<open>\<lbrakk>x \<sharp> t; x \<sharp> u; x \<sharp> v; x \<sharp> w; x \<sharp> y\<rbrakk> \<Longrightarrow> x \<sharp> qiop f t u v w y\<close>
  by transfer simp

lemma aext_qiop [alpha]: \<open>qiop f t u v w x \<oplus>\<^sub>p a = qiop f (t \<oplus>\<^sub>p a) (u \<oplus>\<^sub>p a) (v \<oplus>\<^sub>p a) (w \<oplus>\<^sub>p a) (x \<oplus>\<^sub>p a)\<close>
  by pred_auto

lemma lit_qiop_simp [lit_simps]:
  \<open>\<guillemotleft>i x y z u t\<guillemotright> = qiop i \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright> \<guillemotleft>z\<guillemotright> \<guillemotleft>u\<guillemotright> \<guillemotleft>t\<guillemotright>\<close>
  by transfer simp

subsubsection \<open>Actual proofs\<close>

lemma sorted_update_plus_one:
  assumes \<open>sorted xs\<close>
    shows \<open>sorted (xs[i+1 := xs!i])\<close>
proof (cases \<open>i + 1 < length xs\<close>)
  case True
  then show ?thesis using assms
    apply (subst id_take_nth_drop[where i = \<open>i + 1\<close> and xs = xs])
    apply (auto simp: list_update_append sorted_append sorted_Cons sorted_take sorted_drop)
      apply (metis (no_types, lifting) Cons_nth_drop_Suc Suc_lessD order_trans sorted_Cons sorted_drop sorted_many_eq)
    by (auto simp: in_set_conv_nth sorted_nth_mono)
next
  case False
  then show ?thesis using assms by auto
qed

lemma sorted_update_take_plus_one:
  assumes \<open>sorted (take i xs)\<close>
      and \<open>i > j\<close>
    shows \<open>sorted (take i (xs[j+1 := xs!j]))\<close>
  using assms
  by (metis sorted_update_plus_one leI nth_take take_update_cancel take_update_swap)

term \<open>&i >\<^sub>u 0 \<and> #\<^sub>u(&array) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> mset\<^sub>u(&array) =\<^sub>u mset\<^sub>u(&old_array) \<and> sorted\<^sub>u(take\<^sub>u(&i-1, &array))\<close>
definition \<open>outer_invr' i n array old_array \<equiv>
  i > 0 \<and> length array = n \<and> mset array = mset old_array \<and> sorted (take (i - 1) array)\<close>
abbreviation \<open>outer_invr \<equiv> qtop outer_invr'\<close>

lemma outer_invr_init[vcg_simps]:
  assumes \<open>length array = n\<close>
      and \<open>mset array = mset old_array\<close>
  shows \<open>outer_invr' (Suc 0) n array old_array\<close>
  unfolding outer_invr'_def
  using assms by auto

term \<open>&i <\<^sub>u #\<^sub>u(&array) \<and> &i >\<^sub>u 0 \<and> &i >\<^sub>u nat\<^sub>u(&j) \<and> #\<^sub>u(&array) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> sorted\<^sub>u(take\<^sub>u(&i-1, &array))\<close>
definition \<open>inner_invr' i j n array old_array \<equiv>
  i < length array \<and> i > 0 \<and> i > nat j \<and> length array = n \<and> sorted (take (i - 1) array)\<close>
abbreviation \<open>inner_invr \<equiv> qiop inner_invr'\<close>

lemma inner_invr_init[vcg_simps]:
  assumes \<open>outer_invr' i n array old_array\<close>
      and \<open>nat j = i - 1\<close>
      and \<open>i < length array\<close>
    shows \<open>inner_invr' i j n array old_array\<close>
  using assms unfolding inner_invr'_def outer_invr'_def
  by auto

lemma inner_invr_step[vcg_simps]:
  assumes \<open>inner_invr' i j n array old_array\<close>
    and \<open>j \<ge> 0\<close>
  shows \<open>inner_invr' i (j - 1) n (array[nat (j+1) := array!(nat j)]) old_array\<close>
  using assms unfolding inner_invr'_def
  by auto (smt Suc_eq_plus1 Suc_lessD Suc_nat_eq_nat_zadd1 not_less sorted_update_take_plus_one take_update_cancel)

lemma outer_invr_step[vcg_simps]:
  assumes \<open>inner_invr' i j n array old_array\<close>
      and \<open>0 \<le> j \<longrightarrow> \<not> x < array!(nat j)\<close>
    shows \<open>outer_invr' (Suc i) n (array[nat (j + 1) :=x]) old_array\<close>
  oops

lemma inner_loop_r_t:
  assumes \<open>lens_indep_all [i, x]\<close>
      and \<open>vwb_lens j\<close> and \<open>i \<bowtie> j\<close> and \<open>x \<bowtie> j\<close>
      and \<open>i \<bowtie> array\<close>
      and \<open>x \<bowtie> array\<close>
      and \<open>j \<bowtie> array\<close>
  shows
  \<open>\<lbrace>undefined pre\<rbrace>
    while &j \<ge>\<^sub>u 0 \<and> &x <\<^sub>u &array\<lparr>nat\<^sub>u(&j)\<rparr>\<^sub>u
    invr inner_invr &i &j \<guillemotleft>n\<guillemotright> &array old_array do
      array \<Midarrow> &array(nat\<^sub>u(&j+1) \<mapsto> &array\<lparr>nat\<^sub>u(&j)\<rparr>\<^sub>u)\<^sub>u;;
      j \<Midarrow> &j - 1
    od
  \<lbrace>undefined post\<rbrace>\<^sub>A\<^sub>B\<^sub>R\<close>
  sorry
(* 
lemmas [hoare_rules_extra] =
  inner_loop_r_t[THEN hoare_pre_str_t[rotated]] *)

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
  invr outer_invr &i \<guillemotleft>n\<guillemotright> &array &old_array do
    x \<Midarrow> &array\<lparr>&i\<rparr>\<^sub>u;;
    j \<Midarrow> int\<^sub>u(&i - 1);;
    while &j \<ge>\<^sub>u 0 \<and> &x <\<^sub>u &array\<lparr>nat\<^sub>u(&j)\<rparr>\<^sub>u
    invr inner_invr &i &j \<guillemotleft>n\<guillemotright> &array &old_array do
      array \<Midarrow> &array(nat\<^sub>u(&j+1) \<mapsto> &array\<lparr>nat\<^sub>u(&j)\<rparr>\<^sub>u)\<^sub>u;;
      j \<Midarrow> &j - 1
    od;;
    array \<Midarrow> &array(nat\<^sub>u(&j+1) \<mapsto> &x)\<^sub>u;;
    i \<Midarrow> &i + 1
  od
  \<lbrace>#\<^sub>u(&array) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> sorted\<^sub>u(&array) \<and> mset\<^sub>u(&array) =\<^sub>u mset\<^sub>u(&old_array)\<rbrace>\<^sub>A\<^sub>B\<^sub>R\<close>
  apply (insert assms)
  apply exp_vcg

end
