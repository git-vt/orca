section {* Lists: extra functions and properties *}

theory List_extra
imports
  Main
  "~~/src/HOL/Library/Sublist"
  "~~/src/HOL/Library/Monad_Syntax"
begin

subsection {* Extra list functions *}

text {*
The following variant of the standard @{text nth} function returns
@{text "\<bottom>"} if the index is out of range.
*}

primrec
  nth_el :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" ("_\<langle>_\<rangle>\<^sub>l" [90, 0] 91)
where
  "[]\<langle>i\<rangle>\<^sub>l = None"
| "(x # xs)\<langle>i\<rangle>\<^sub>l = (case i of 0 \<Rightarrow> Some x | Suc j \<Rightarrow> xs \<langle>j\<rangle>\<^sub>l)"

fun sequence :: "'a option list \<Rightarrow> 'a list option" where
"sequence [] = Some []" |
"sequence (f # fs) = do { x \<leftarrow> f; xs \<leftarrow> sequence fs; Some (x # xs) }"

abbreviation "mapM f \<equiv> sequence \<circ> map f"

subsection {* List lemmas *}

lemma map_nth_Cons_atLeastLessThan:
  "map (nth (x # xs)) [Suc m..<n] = map (nth xs) [m..<n - 1]"
proof -
  have "nth xs = nth (x # xs) \<circ> Suc"
    by auto
  hence "map (nth xs) [m..<n - 1] = map (nth (x # xs) \<circ> Suc) [m..<n - 1]"
    by simp
  also have "... = map (nth (x # xs)) (map Suc [m..<n - 1])"
    by simp
  also have "... = map (nth (x # xs)) [Suc m..<n]"
    by (metis Suc_diff_1 le_0_eq length_upt list.simps(8) list.size(3) map_Suc_upt not_less upt_0)
  finally show ?thesis ..
qed

lemma nth_el_appendl[simp]: "i < length xs \<Longrightarrow> (xs @ ys)\<langle>i\<rangle>\<^sub>l = xs\<langle>i\<rangle>\<^sub>l"
  apply (induct xs arbitrary: i)
  apply simp
  apply (case_tac i)
  apply simp_all
done

lemma nth_el_appendr[simp]: "length xs \<le> i \<Longrightarrow> (xs @ ys)\<langle>i\<rangle>\<^sub>l = ys\<langle>i - length xs\<rangle>\<^sub>l"
  apply (induct xs arbitrary: i)
  apply simp
  apply (case_tac i)
  apply simp_all
done

lemma sorted_last [simp]: "\<lbrakk> x \<in> set xs; sorted xs \<rbrakk> \<Longrightarrow> x \<le> last xs"
  apply (induct xs)
  apply (auto)
  apply (metis last_in_set sorted_Cons)+
done

lemma sorted_map: "\<lbrakk> sorted xs; mono f \<rbrakk> \<Longrightarrow> sorted (map f xs)"
  by (simp add: monoD sorted_equals_nth_mono)
 
lemma prefix_length_eq:
  "\<lbrakk> length xs = length ys; prefixeq xs ys \<rbrakk> \<Longrightarrow> xs = ys"
  using not_equal_is_parallel by auto
 
lemma prefix_Cons_elim [elim]:
  assumes "prefixeq (x # xs) ys"
  obtains ys' where "ys = x # ys'" "prefixeq xs ys'"
  using assms by (auto elim!: prefixeqE)

lemma prefix_map_inj:
  "\<lbrakk> inj_on f (set xs \<union> set ys); prefixeq (map f xs) (map f ys) \<rbrakk> \<Longrightarrow>
   prefixeq xs ys"
  apply (induct xs arbitrary:ys)
  apply (simp_all)
  apply (erule prefix_Cons_elim)
  apply (auto)
  apply (metis image_insert insertI1 insert_Diff_if singletonE)
done

lemma prefix_map_inj_eq [simp]:
  "inj_on f (set xs \<union> set ys) \<Longrightarrow>
   prefixeq (map f xs) (map f ys) \<longleftrightarrow> prefixeq xs ys"
  by (metis map_prefixeqI prefix_map_inj)

lemma strict_prefix_Cons_elim:
  assumes "prefixeq (x # xs) ys"
  obtains ys' where "ys = x # ys'" "prefixeq xs ys'"
  using assms by auto

lemma strict_prefix_map_inj:
  "\<lbrakk> inj_on f (set xs \<union> set ys); prefixeq (map f xs) (map f ys) \<rbrakk> \<Longrightarrow>
   prefixeq xs ys" by auto

lemma strict_prefix_map_inj_eq:
  "inj_on f (set xs \<union> set ys) \<Longrightarrow>
   prefixeq (map f xs) (map f ys) \<longleftrightarrow> prefixeq xs ys"
   by auto

lemma prefix_drop:
  "\<lbrakk> drop (length xs) ys = zs; prefixeq xs ys \<rbrakk>
   \<Longrightarrow> ys = xs @ zs"
  by (metis append_eq_conv_conj prefixeq_def)

subsection {* Minus on lists *}

instantiation list :: (type) minus
begin

text {* We define list minus so that if the second list is not a prefix of the first, then an arbitrary
        list longer than the combined length is produced. Thus we can always determined from the output
        whether the minus is defined or not. *}

definition "xs - ys = (if (prefixeq ys xs) then drop (length ys) xs else [])"

instance ..
end

lemma minus_cancel [simp]: "xs - xs = []"
  by (simp add: minus_list_def)

lemma append_minus [simp]: "(xs @ ys) - xs = ys"
  by (simp add: minus_list_def)

lemma minus_right_nil [simp]: "xs - [] = xs"
  by (simp add: minus_list_def)

lemma list_concat_minus_list_concat: "(s @ t) - (s @ z) = t - z"
  by (simp add: minus_list_def)

lemma length_gt_zero_butlast_concat:
  assumes "length ys > 0"
  shows "butlast (xs @ ys) = xs @ (butlast ys)"
  using assms by (metis butlast_append length_greater_0_conv)

lemma length_eq_zero_butlast_concat:
  assumes "length ys = 0"
  shows "butlast (xs @ ys) = butlast xs"
  using assms by (metis append_Nil2 length_0_conv)

lemma butlast_single_element:
  shows "butlast [e] = []"
  by (metis butlast.simps(2))

lemma last_single_element:
  shows "last [e] = e"
  by (metis last.simps)

lemma length_zero_last_concat:
  assumes "length t = 0"
  shows "last (s @ t) = last s"
  by (metis append_Nil2 assms length_0_conv)

lemma length_gt_zero_last_concat:
  assumes "length t > 0"
  shows "last (s @ t) = last t"
  by (metis assms last_append length_greater_0_conv)

subsection {* Interleaving operations *}

fun interleave :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set" where
"interleave [] ys = {ys}" |
"interleave (x # xs) (y # ys) = (Cons x) ` (interleave xs (y # ys))
                              \<union> (Cons y) ` (interleave (x # xs) ys)" |
"interleave xs [] = {xs}"

lemma interleave_finite [simp]:
  "finite (interleave xs ys)"
  apply (induct xs arbitrary: ys)
  apply (simp)
  apply (induct_tac ys)
  apply (auto)
done

lemma interleave_right_nil [simp]:
  "interleave xs [] = {xs}"
  by (induct xs, auto)

lemma interleave_headE [elim!]:
  "\<lbrakk> z # zs \<in> interleave xs ys
   ; \<And> xs'. xs = z # xs' \<Longrightarrow> P
   ; \<And> ys'. ys = z # ys' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (induct xs)
  apply (auto)
  apply (induct ys)
  apply (auto)
done

lemma interleave_member:
  "\<lbrakk> zs \<in> interleave xs ys; z \<in> set zs \<rbrakk> \<Longrightarrow> z \<in> set xs \<or> z \<in> set ys"
  apply (induct xs arbitrary: zs)
  apply (auto)
  apply (induct ys)
  apply (auto)
oops

(* FIXME: What happens if no progress can be made? *)
fun intersync :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set" where
"intersync s (x # xs) (y # ys)
  = (case (x = y , x \<in> s , y \<in> s) of
          (True  , True   , _      ) \<Rightarrow> Cons x ` intersync s xs ys |
          (True  , False  , _      ) \<Rightarrow> ((Cons x ` intersync s xs (y # ys))
                                         \<union> (Cons y ` intersync s (x # xs) ys)) |
          (False , True   , True   ) \<Rightarrow> {[]} |
          (False , True   , False  ) \<Rightarrow> Cons y ` intersync s (x # xs) ys |
          (False , False  , True   ) \<Rightarrow> Cons x ` intersync s xs (y # ys) |
          (False , False  , False  ) \<Rightarrow> ((Cons x ` intersync s xs (y # ys))
                                         \<union> (Cons y ` intersync s (x # xs) ys)))" |
"intersync s [] (y # ys) =
   (if (y \<in> s) then {[]} else Cons y ` intersync s [] ys)" |
"intersync s (x # xs) [] =
   (if (x \<in> s) then {[]} else Cons x ` intersync s xs [])" |
"intersync s [] [] = {[]}"

(* FIXME: We should be able to prove this property... *)
lemma intersync_empty_interleave:
  "intersync {} xs ys = interleave xs ys"
oops

subsection {* Sorting of lists *}

definition is_sorted_list_of_set :: "('a::ord) set \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_sorted_list_of_set A xs = ((\<forall> i<length(xs) - 1. xs!i < xs!(i + 1)) \<and> set(xs) = A)"

lemma sorted_distinct [intro]: "\<lbrakk> sorted (xs); distinct(xs) \<rbrakk> \<Longrightarrow> (\<forall> i<length xs - 1. xs!i < xs!(i + 1))"
  apply (induct xs)
  apply (auto)
  apply (metis Suc_mono distinct.simps(2) length_Cons lessI less_SucI less_le nth_Cons_Suc nth_eq_iff_index_eq sorted_equals_nth_mono)
done

lemma sorted_is_sorted_list_of_set:
  assumes "is_sorted_list_of_set A xs"
  shows "sorted(xs)" and "distinct(xs)"
using assms proof (induct xs arbitrary: A)
  show "sorted []"
    by auto
next
  show "distinct []"
    by auto
next
  fix A :: "'a set"
  case (Cons x xs) note hyps = this
  assume isl: "is_sorted_list_of_set A (x # xs)"
  hence srt: "(\<forall>i<length xs - Suc 0. xs ! i < xs ! Suc i)"
    using less_diff_conv by (auto simp add: is_sorted_list_of_set_def)
  with hyps(1) have srtd: "sorted xs"
    by (simp add: is_sorted_list_of_set_def)
  with isl show "sorted (x # xs)"
    apply (auto simp add: is_sorted_list_of_set_def)
    apply (metis length_pos_if_in_set less_imp_le nth_Cons_0 sorted.simps sorted_many sorted_single)
  done
  from srt hyps(2) have "distinct xs"
    by (simp add: is_sorted_list_of_set_def)
  with isl show "distinct (x # xs)"
  proof -
    have "(\<forall>n. \<not> n < length (x # xs) - 1 \<or> (x # xs) ! n < (x # xs) ! (n + 1)) \<and> set (x # xs) = A"
      by (meson \<open>is_sorted_list_of_set A (x # xs)\<close> is_sorted_list_of_set_def)
  then show ?thesis
      by (metis Nat.add_0_right One_nat_def \<open>distinct xs\<close> \<open>sorted (x # xs)\<close> add_Suc_right diff_Suc_Suc diff_zero distinct.simps(2) insert_iff length_pos_if_in_set linorder_not_less list.set(2) list.simps(1) list.simps(3) list.size(3) list.size(4) not_less_iff_gr_or_eq nth_Cons_0 nth_Cons_Suc sorted.cases)
  qed
qed

lemma is_sorted_list_of_set_alt_def:
  "is_sorted_list_of_set A xs \<longleftrightarrow> sorted (xs) \<and> distinct (xs) \<and> set(xs) = A"
  apply (auto intro: sorted_is_sorted_list_of_set)
  apply (auto simp add: is_sorted_list_of_set_def)
  apply (metis Nat.add_0_right One_nat_def add_Suc_right sorted_distinct)
done

(*
lemma sorted_alt_def:
  "(\<forall> i<(length xs) - 1. xs!i < xs!(i + 1)) \<longleftrightarrow> sorted (xs) \<and> distinct (xs)"
  apply (auto)
  sledgehammer
oops
*)

definition sorted_list_of_set_alt :: "('a::ord) set \<Rightarrow> 'a list" where
"sorted_list_of_set_alt A =
  (if (A = {}) then [] else (THE xs. is_sorted_list_of_set A xs))"

lemma is_sorted_list_of_set:
  "finite A \<Longrightarrow> is_sorted_list_of_set A (sorted_list_of_set A)"
  apply (simp add: is_sorted_list_of_set_def)
  apply (metis One_nat_def add.right_neutral add_Suc_right sorted_distinct sorted_list_of_set)
done

lemma sorted_list_of_set_other_def:
  "finite A \<Longrightarrow> sorted_list_of_set(A) = (THE xs. sorted(xs) \<and> distinct(xs) \<and> set xs = A)"
  apply (rule sym)
  apply (rule the_equality)
  apply (auto)
  apply (simp add: sorted_distinct_set_unique)
done

lemma sorted_list_of_set_alt [simp]:
  "finite A \<Longrightarrow> sorted_list_of_set_alt(A) = sorted_list_of_set(A)"
  apply (rule sym)
  apply (auto simp add: sorted_list_of_set_alt_def is_sorted_list_of_set_alt_def sorted_list_of_set_other_def)
done


text {* Greatest common prefix *}

fun gcp :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"gcp [] ys = []" |
"gcp (x # xs) (y # ys) = (if (x = y) then x # gcp xs ys else [])" |
"gcp _ _ = []"

lemma gcp_right [simp]: "gcp xs [] = []"
  by (induct xs, auto)

lemma gcp_append [simp]: "gcp (xs @ ys) (xs @ zs) = xs @ gcp ys zs"
  by (induct xs, auto)

lemma gcp_lb1: "prefixeq (gcp xs ys) xs"
  apply (induct xs arbitrary: ys, auto)
  apply (case_tac ys, auto)
done

lemma gcp_lb2: "prefixeq (gcp xs ys) ys"
  apply (induct ys arbitrary: xs, auto)
  apply (case_tac xs, auto)
done

interpretation prefix_semilattice: semilattice_inf gcp prefixeq prefix
proof (unfold_locales)
  fix xs ys :: "'a list"
  show "prefixeq (gcp xs ys) xs"
    by (induct xs arbitrary: ys, auto, case_tac ys, auto)
  show "prefixeq (gcp xs ys) ys"
    by (induct ys arbitrary: xs, auto, case_tac xs, auto)
next
  fix xs ys zs :: "'a list"
  assume "prefixeq xs ys" "prefixeq xs zs"
  thus "prefixeq xs (gcp ys zs)"
    by (simp add: prefixeq_def, auto)
qed

text {* Extra laws to do with prefix and order *}

lemma lexord_append:
  assumes "(xs\<^sub>1 @ ys\<^sub>1, xs\<^sub>2 @ ys\<^sub>2) \<in> lexord R" "length(xs\<^sub>1) = length(xs\<^sub>2)"
  shows "(xs\<^sub>1, xs\<^sub>2) \<in> lexord R \<or> (xs\<^sub>1 = xs\<^sub>2 \<and> (ys\<^sub>1, ys\<^sub>2) \<in> lexord R)"
using assms
proof (induct xs\<^sub>2 arbitrary: xs\<^sub>1)
  case (Cons x\<^sub>2 xs\<^sub>2') note hyps = this
  from hyps(3) obtain x\<^sub>1 xs\<^sub>1' where xs\<^sub>1: "xs\<^sub>1 = x\<^sub>1 # xs\<^sub>1'" "length(xs\<^sub>1') = length(xs\<^sub>2')"
    by (auto, metis Suc_length_conv)
  with hyps(2) have xcases: "(x\<^sub>1, x\<^sub>2) \<in> R \<or> (xs\<^sub>1' @ ys\<^sub>1, xs\<^sub>2' @ ys\<^sub>2) \<in> lexord R"
    by (auto)
  show ?case
  proof (cases "(x\<^sub>1, x\<^sub>2) \<in> R")
    case True with xs\<^sub>1 show ?thesis
      by (auto)
  next
    case False
    with xcases have "(xs\<^sub>1' @ ys\<^sub>1, xs\<^sub>2' @ ys\<^sub>2) \<in> lexord R"
      by (auto)
    with hyps(1) xs\<^sub>1 have dichot: "(xs\<^sub>1', xs\<^sub>2') \<in> lexord R \<or> (xs\<^sub>1' = xs\<^sub>2' \<and> (ys\<^sub>1, ys\<^sub>2) \<in> lexord R)"
      by (auto)
    have "x\<^sub>1 = x\<^sub>2"
      using False hyps(2) xs\<^sub>1(1) by auto
    with dichot xs\<^sub>1 show ?thesis
      by (simp)
  qed
next
  case Nil thus ?case
    by auto
qed

lemma strict_prefix_lexord_rel:
  "prefix xs ys \<Longrightarrow> (xs, ys) \<in> lexord R"
  by (metis lexord_append_rightI prefixE')

lemma strict_prefix_lexord_left:
  assumes "trans R" "(xs, ys) \<in> lexord R" "prefix xs' xs"
  shows "(xs', ys) \<in> lexord R"
  using assms lexord_trans strict_prefix_lexord_rel by blast


lemma prefix_lexord_right:
  assumes "trans R" "(xs, ys) \<in> lexord R" "prefix ys ys'"
  shows "(xs, ys') \<in> lexord R"
  by (metis assms lexord_trans strict_prefix_lexord_rel)

lemma lexord_eq_length:
  assumes "(xs, ys) \<in> lexord R" "length xs = length ys"
  shows "\<exists> i. (xs!i, ys!i) \<in> R \<and> i < length xs \<and> (\<forall> j<i. xs!j = ys!j)"
using assms proof (induct xs arbitrary: ys)
  case (Cons x xs) note hyps = this
  then obtain y ys' where ys: "ys = y # ys'" "length ys' = length xs"
    by (metis Suc_length_conv)
  show ?case
  proof (cases "(x, y) \<in> R")
    case True with ys show ?thesis
      by (rule_tac x="0" in exI, simp)
  next
    case False
    with ys hyps(2) have xy: "x = y" "(xs, ys') \<in> lexord R"
      by auto
    with hyps(1,3) ys obtain i where "(xs!i, ys'!i) \<in> R" "i < length xs" "(\<forall> j<i. xs!j = ys'!j)"
      by force
    with xy ys show ?thesis
      apply (rule_tac x="Suc i" in exI)
      apply (auto simp add: less_Suc_eq_0_disj)
    done
  qed
next
  case Nil thus ?case by (auto)
qed

lemma lexord_intro_elems:
  assumes "length xs > i" "length ys > i" "(xs!i, ys!i) \<in> R" "\<forall> j<i. xs!j = ys!j"
  shows "(xs, ys) \<in> lexord R"
using assms proof (induct i arbitrary: xs ys)
  case 0 thus ?case
    by (auto, metis lexord_cons_cons list.exhaust nth_Cons_0)
next
  case (Suc i) note hyps = this
  then obtain x' y' xs' ys' where "xs = x' # xs'" "ys = y' # ys'"
    by (metis Suc_length_conv Suc_lessE)
  moreover with hyps(5) have "\<forall>j<i. xs' ! j = ys' ! j"
    by (auto)
  ultimately show ?case using hyps
    by (auto)
qed

text {* Extra lemmas about @{term prefix} and @{term strict_prefix} *}

lemma prefix_concat_minus:
  assumes "prefixeq xs ys"
  shows "xs @ (ys - xs) = ys"
  using assms by (metis minus_list_def prefix_drop)

lemma prefix_minus_concat:
  assumes "prefixeq s t"
  shows "(t - s) @ z = (t @ z) - s"
  using assms by (simp add: minus_list_def prefixeq_length_le)

lemma strict_prefix_minus_not_empty:
  assumes "prefix xs ys"
  shows "ys - xs \<noteq> []"
  using assms  by (metis append_Nil2 prefixE prefix_concat_minus)

lemma strict_prefix_diff_minus:
  assumes "prefix xs ys" and "xs \<noteq> ys"
  shows "(ys - xs) \<noteq> []"
  using assms by (simp add: strict_prefix_minus_not_empty)

lemma prefix_not_empty:
  assumes "prefix xs ys" and "xs \<noteq> []"
  shows "ys \<noteq> []"
  using assms prefix_simps(1) by blast

lemma prefix_not_empty_length_gt_zero:
  assumes "prefix xs ys" and "xs \<noteq> []"
  shows "length ys > 0"
  using assms prefix_not_empty by auto

lemma butlast_prefix_suffix_not_empty:
  assumes "prefix (butlast xs) ys"
  shows "ys \<noteq> []"
  using assms prefix_not_empty_length_gt_zero by fastforce

lemma length_tl_list_minus_butlast_gt_zero:
  assumes "length s < length t" and "prefix (butlast s) t" and "length s > 0"
  shows "length (tl (t - (butlast s))) > 0"
  using assms
  by (metis Nitpick.size_list_simp(2) butlast_snoc hd_Cons_tl length_butlast length_greater_0_conv length_tl less_trans nat_neq_iff strict_prefix_minus_not_empty prefix_order.dual_order.strict_implies_order prefix_concat_minus)

lemma prefix_and_concat_prefix_is_concat_prefix:
  assumes "prefixeq s t" "prefixeq (e @ t) u"
  shows "prefixeq (e @ s) u"
  using assms prefix_order.dual_order.trans same_prefixeq_prefixeq by blast

lemma list_minus_butlast_eq_butlast_list:
  assumes "length t = length s" and "prefix (butlast s) t"
  shows "t - (butlast s) = [last t]"
  using assms
  by (metis append_butlast_last_id append_eq_append_conv butlast.simps(1) length_butlast less_numeral_extra(3) list.size(3) prefix_order.dual_order.strict_implies_order prefix_concat_minus prefixeq_length_less)

lemma strict_prefix_eq_exists:
  "prefix s t \<longleftrightarrow> (\<exists>xs . s @ xs = t \<and> (length xs) > 0)"
  by (metis append_minus length_greater_0_conv minus_list_def prefixE' prefix_def self_append_conv)

lemma prefix_eq_exists:
  "prefixeq s t \<longleftrightarrow> (\<exists>xs . s @ xs = t)"
  using prefix_concat_minus by auto

lemma butlast_strict_prefix_eq_butlast:
  assumes "length s = length t" and "prefix (butlast s) t"
  shows "prefix (butlast s) t \<longleftrightarrow> (butlast s) = (butlast t)"
  by (metis append_butlast_last_id append_eq_append_conv assms(1) assms(2) length_0_conv length_butlast strict_prefix_eq_exists)

lemma butlast_eq_if_eq_length_and_prefix:
  assumes "length s > 0" "length z > 0"
          "length s = length z" "prefix (butlast s) t" "prefix (butlast z) t"
  shows   "(butlast s) = (butlast z)"
  using assms by (auto simp add:strict_prefix_eq_exists)

lemma prefix_imp_length_lteq:
  assumes "prefixeq s t"
  shows "length s \<le> length t"
  using assms by (simp add:prefixeq_length_le)

lemma prefix_imp_length_not_gt:
  assumes "prefixeq s t"
  shows "\<not> length t < length s"
  using assms by (simp add: leD prefixeq_length_le)

lemma prefix_and_eq_length_imp_eq_list:
  assumes "prefixeq s t" and "length t = length s"
  shows "s=t"
  using assms by (simp add: prefix_length_eq)

lemma butlast_strict_prefix_length_lt_imp_last_tl_minus_butlast_eq_last:
  assumes "length s > 0" "prefix (butlast s) t" "length s < length t"
  shows "last (tl (t - (butlast s))) = (last t)"
  using assms by (metis last_append last_tl length_tl_list_minus_butlast_gt_zero less_numeral_extra(3) list.size(3) append_minus strict_prefix_eq_exists)

lemma tl_list_minus_butlast_not_empty:
  assumes "prefixeq (butlast s) t" and "length s > 0" and "length t > length s"
  shows "tl (t - (butlast s)) \<noteq> []"
  using assms length_tl_list_minus_butlast_gt_zero
proof -
  have "butlast s \<noteq> t"
    by (metis (full_types) assms(3) diff_le_self leD length_butlast)
  then have "prefix (butlast s) t"
    by (metis assms(1) prefix_order.le_imp_less_or_eq)
  then show ?thesis
    by (metis (full_types) assms(2) assms(3) length_tl_list_minus_butlast_gt_zero less_numeral_extra(3) list.size(3))
qed 

lemma tl_list_minus_butlast_empty:
  assumes "prefix (butlast s) t" and "length s > 0" and "length t = length s"
  shows "tl (t - (butlast s)) = []"
  using assms by (simp add: list_minus_butlast_eq_butlast_list)

lemma concat_minus_list_concat_butlast_eq_list_minus_butlast:
  assumes "prefixeq (butlast u) s"
  shows "(t @ s) - (t @ (butlast u)) = s - (butlast u)" 
  using List_extra.list_concat_minus_list_concat by auto

lemma tl_list_minus_butlast_eq_empty:
  assumes "prefix (butlast s) t" and "length s = length t"
  shows "tl (t - (butlast s)) = []"
  using assms by (metis list.sel(3) list_minus_butlast_eq_butlast_list)

(* this can be shown using length_tl, but care is needed when list is empty? *)
lemma prefix_length_tl_minus:
  assumes "prefix s t"
  shows "length (tl (t-s)) = (length (t-s)) - 1"
  by auto

lemma length_list_minus:
  assumes "prefix s t"
  shows "length(t - s) = length(t) - length(s)"
  using assms by (simp add: minus_list_def prefix_order.dual_order.strict_implies_order)

lemma butlast_prefix_imp_length_not_gt:
  assumes "length s > 0" "prefix (butlast s) t"
  shows "\<not> (length t < length s)"
  using assms prefixeq_length_less by fastforce

lemma length_not_gt_iff_eq_length:
  assumes "length s > 0" and "prefix (butlast s) t"
  shows "(\<not> (length s < length t)) = (length s = length t)"
proof -
  have "(\<not> (length s < length t)) = ((length t < length s) \<or> (length s = length t))"
      by (metis not_less_iff_gr_or_eq)
  also have "... = (length s = length t)"
      using assms
      by (simp add:butlast_prefix_imp_length_not_gt)
  finally show ?thesis .
qed

lemma dropWhile_sorted_le_above:
  "\<lbrakk> sorted xs; x \<in> set (dropWhile (\<lambda> x. x \<le> n) xs) \<rbrakk> \<Longrightarrow> x > n"
  apply (induct xs)
  apply (auto)
  apply (rename_tac a xs)
  apply (case_tac "a \<le> n")
  apply (simp_all)
  using sorted_Cons apply blast
  apply (meson dual_order.trans not_less sorted_Cons)
done

lemma set_dropWhile_le:
  "sorted xs \<Longrightarrow> set (dropWhile (\<lambda> x. x \<le> n) xs) = {x\<in>set xs. x > n}"
  apply (induct xs)
  apply (simp)
  apply (rename_tac x xs)
  apply (subgoal_tac "sorted xs")
  apply (simp)
  apply (safe)
  apply (simp_all)
  apply (meson not_less order_trans sorted_Cons)
  using sorted_Cons apply auto
done

lemma set_takeWhile_less_sorted: 
  "\<lbrakk> sorted I; x \<in> set I; x < n \<rbrakk> \<Longrightarrow> x \<in> set (takeWhile (\<lambda>x. x < n) I)"
proof (induct I arbitrary: x)
  case Nil thus ?case
    by (simp)
next
  case (Cons a I) thus ?case
    by (auto, (meson le_less_trans sorted_Cons)+)
qed

lemma nth_le_takeWhile_ord: "\<lbrakk> sorted xs; i \<ge> length (takeWhile (\<lambda> x. x \<le> n) xs); i < length xs \<rbrakk> \<Longrightarrow> n \<le> xs ! i"
  apply (induct xs arbitrary: i, auto)
  apply (rename_tac x xs i)
  apply (case_tac "x \<le> n")
  apply (auto simp add: sorted_Cons)
  apply (metis One_nat_def Suc_eq_plus1 le_less_linear le_less_trans less_imp_le list.size(4) nth_mem set_ConsD)
done

lemma length_takeWhile_less:
  "\<lbrakk> a \<in> set xs; \<not> P a \<rbrakk> \<Longrightarrow> length (takeWhile P xs) < length xs"
  by (metis in_set_conv_nth length_takeWhile_le nat_neq_iff not_less set_takeWhileD takeWhile_nth)

lemma nth_length_takeWhile_less:
  "\<lbrakk> sorted xs; distinct xs; (\<exists> a \<in> set xs. a \<ge> n) \<rbrakk> \<Longrightarrow> xs ! length (takeWhile (\<lambda>x. x < n) xs) \<ge> n"
  apply (induct xs, auto)
  using sorted_Cons by blast

text {* Sorting lists according to a relation *}

definition is_sorted_list_of_set_by :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_sorted_list_of_set_by R A xs = ((\<forall> i<length(xs) - 1. (xs!i, xs!(i + 1)) \<in> R) \<and> set(xs) = A)"

definition sorted_list_of_set_by :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a list" where
"sorted_list_of_set_by R A = (THE xs. is_sorted_list_of_set_by R A xs)"

definition fin_set_lexord :: "'a rel \<Rightarrow> 'a set rel" where
"fin_set_lexord R = {(A, B). finite A \<and> finite B \<and>
                             (\<exists> xs ys. is_sorted_list_of_set_by R A xs \<and> is_sorted_list_of_set_by R B ys
                              \<and> (xs, ys) \<in> lexord R)}"

lemma is_sorted_list_of_set_by_mono:
  "\<lbrakk> R \<subseteq> S; is_sorted_list_of_set_by R A xs \<rbrakk> \<Longrightarrow> is_sorted_list_of_set_by S A xs"
  by (auto simp add: is_sorted_list_of_set_by_def)

lemma lexord_mono':
  "\<lbrakk> (\<And> x y. f x y \<longrightarrow> g x y); (xs, ys) \<in> lexord {(x, y). f x y} \<rbrakk> \<Longrightarrow> (xs, ys) \<in> lexord {(x, y). g x y}"
  by (metis case_prodD case_prodI lexord_take_index_conv mem_Collect_eq)

lemma fin_set_lexord_mono [mono]:
  "(\<And> x y. f x y \<longrightarrow> g x y) \<Longrightarrow> (xs, ys) \<in> fin_set_lexord {(x, y). f x y} \<longrightarrow> (xs, ys) \<in> fin_set_lexord {(x, y). g x y}"
proof
  assume
    fin: "(xs, ys) \<in> fin_set_lexord {(x, y). f x y}" and
    hyp: "(\<And> x y. f x y \<longrightarrow> g x y)"

  from fin have "finite xs" "finite ys"
    using fin_set_lexord_def by fastforce+

  with fin hyp show "(xs, ys) \<in> fin_set_lexord {(x, y). g x y}"
    apply (auto simp add: fin_set_lexord_def)
    apply (rule_tac x="xsa" in exI)
    apply (auto)
    apply (metis case_prodD case_prodI is_sorted_list_of_set_by_def mem_Collect_eq)
    apply (metis case_prodD case_prodI is_sorted_list_of_set_by_def lexord_mono' mem_Collect_eq)
  done
qed

definition distincts :: "'a set \<Rightarrow> 'a list set" where
"distincts A = {xs \<in> lists A. distinct(xs)}"

lemma tl_element:
  "\<lbrakk> x \<in> set xs; x \<noteq> hd(xs) \<rbrakk> \<Longrightarrow> x \<in> set(tl(xs))"
  by (metis in_set_insert insert_Nil list.collapse list.distinct(2) set_ConsD)

subsection {* Z mathematical tool kit for sequences *}

abbreviation seq_dom :: "'a list \<Rightarrow> nat set" ("dom\<^sub>l") where
"seq_dom xs \<equiv> {0..<length xs}"

abbreviation seq_ran :: "'a list \<Rightarrow> 'a set" ("ran\<^sub>l") where
"seq_ran xs \<equiv> set xs"

definition seq_extract :: "nat set \<Rightarrow> 'a list \<Rightarrow> 'a list" (infix "\<upharpoonleft>\<^sub>l" 80) where
"seq_extract A xs = sublist xs A"

lemma seq_extract_Nil [simp]: "A \<upharpoonleft>\<^sub>l [] = []"
  by (simp add: seq_extract_def)

lemma seq_extract_Cons:
  "A \<upharpoonleft>\<^sub>l (x # xs) = (if 0 \<in> A then [x] else []) @ {j. Suc j \<in> A} \<upharpoonleft>\<^sub>l xs"
  by (simp add: seq_extract_def sublist_Cons)

lemma seq_extract_empty [simp]: "{} \<upharpoonleft>\<^sub>l xs = []"
  by (simp add: seq_extract_def)

lemma seq_extract_ident [simp]: "{0..<length xs} \<upharpoonleft>\<^sub>l xs = xs"
  unfolding list_eq_iff_nth_eq
  by (auto simp add: seq_extract_def length_sublist atLeast0LessThan)

lemma seq_extract_split:
  assumes "i \<le> length xs"
  shows "{0..<i} \<upharpoonleft>\<^sub>l xs @ {i..<length xs} \<upharpoonleft>\<^sub>l xs = xs"
using assms
proof (induct xs arbitrary: i)
  case Nil thus ?case by (simp add: seq_extract_def)
next
  case (Cons x xs) note hyp = this
  have "{j. Suc j < i} = {0..<i - 1}"
    by (auto)
  moreover have "{j. i \<le> Suc j \<and> j < length xs} = {i - 1..<length xs}"
    by (auto)
  ultimately show ?case
    using hyp by (force simp add: seq_extract_def sublist_Cons)
qed

lemma seq_extract_append:
  "A \<upharpoonleft>\<^sub>l (xs @ ys) = (A \<upharpoonleft>\<^sub>l xs) @ ({j. j + length xs \<in> A} \<upharpoonleft>\<^sub>l ys)"
  by (simp add: seq_extract_def sublist_append)

lemma seq_extract_range: "A \<upharpoonleft>\<^sub>l xs = (A \<inter> dom\<^sub>l(xs)) \<upharpoonleft>\<^sub>l xs"
  apply (auto simp add: seq_extract_def sublist_def)
  apply (metis (no_types, lifting) atLeastLessThan_iff filter_cong in_set_zip nth_mem set_upt)
done

lemma seq_extract_out_of_range:
  "A \<inter> dom\<^sub>l(xs) = {} \<Longrightarrow> A \<upharpoonleft>\<^sub>l xs = []"
  by (metis seq_extract_def seq_extract_range sublist_empty)

lemma seq_extract_length [simp]:
  "length (A \<upharpoonleft>\<^sub>l xs) = card (A \<inter> dom\<^sub>l(xs))"
proof -
  have "{i. i < length(xs) \<and> i \<in> A} = (A \<inter> {0..<length(xs)})"
    by (auto)
  thus ?thesis
    by (simp add: seq_extract_def length_sublist)
qed

lemma seq_extract_Cons_atLeastLessThan:
  assumes "m < n"
  shows "{m..<n} \<upharpoonleft>\<^sub>l (x # xs) = (if (m = 0) then x # ({0..<n-1} \<upharpoonleft>\<^sub>l xs) else {m-1..<n-1} \<upharpoonleft>\<^sub>l xs)"
proof -
  have "{j. Suc j < n} = {0..<n - Suc 0}"
    by (auto)
  moreover have "{j. m \<le> Suc j \<and> Suc j < n} = {m - Suc 0..<n - Suc 0}"
    by (auto)

  ultimately show ?thesis using assms
    by (auto simp add: seq_extract_Cons)
qed

lemma seq_extract_singleton:
  assumes "i < length xs"
  shows "{i} \<upharpoonleft>\<^sub>l xs = [xs ! i]"
  using assms
  apply (induct xs arbitrary: i)
  apply (auto simp add: seq_extract_Cons)
  apply (rename_tac xs i)
  apply (subgoal_tac "{j. Suc j = i} = {i - 1}")
  apply (auto)
done

lemma seq_extract_as_map:
  assumes "m < n" "n \<le> length xs"
  shows "{m..<n} \<upharpoonleft>\<^sub>l xs = map (nth xs) [m..<n]"
using assms proof (induct xs arbitrary: m n)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have "[m..<n] = m # [m+1..<n]"
    using Cons.prems(1) upt_eq_Cons_conv by blast
  moreover have "map (nth (x # xs)) [Suc m..<n] = map (nth xs) [m..<n-1]"
    by (simp add: map_nth_Cons_atLeastLessThan)
  ultimately show ?case
    using Cons upt_rec
    by (auto simp add: seq_extract_Cons_atLeastLessThan)
qed

lemma seq_append_as_extract:
  "xs = ys @ zs \<longleftrightarrow> (\<exists> i\<le>length(xs). ys = {0..<i} \<upharpoonleft>\<^sub>l xs \<and> zs = {i..<length(xs)} \<upharpoonleft>\<^sub>l xs)"
proof
  assume xs: "xs = ys @ zs"
  moreover have "ys = {0..<length ys} \<upharpoonleft>\<^sub>l (ys @ zs)"
    by (simp add: seq_extract_append)
  moreover have "zs = {length ys..<length ys + length zs} \<upharpoonleft>\<^sub>l (ys @ zs)"
  proof -
    have "{length ys..<length ys + length zs} \<inter> {0..<length ys} = {}"
      by auto
    moreover have s1: "{j. j < length zs} = {0..<length zs}"
      by auto
    ultimately show ?thesis
      by (simp add: seq_extract_append seq_extract_out_of_range)
  qed
  ultimately show "(\<exists> i\<le>length(xs). ys = {0..<i} \<upharpoonleft>\<^sub>l xs \<and> zs = {i..<length(xs)} \<upharpoonleft>\<^sub>l xs)"
    by (rule_tac x="length ys" in exI, auto)
next
  assume "\<exists>i\<le>length xs. ys = {0..<i} \<upharpoonleft>\<^sub>l xs \<and> zs = {i..<length xs} \<upharpoonleft>\<^sub>l xs"
  thus "xs = ys @ zs"
    by (auto simp add: seq_extract_split)
qed

definition seq_filter :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a list" (infix "\<restriction>\<^sub>l" 80) where
"seq_filter xs A = filter (\<lambda> x. x \<in> A) xs"

lemma seq_filter_Nil [simp]: "[] \<restriction>\<^sub>l A = []"
  by (simp add: seq_filter_def)

lemma seq_filter_empty [simp]: "xs \<restriction>\<^sub>l {} = []"
  by (simp add: seq_filter_def)

lemma seq_filter_append: "(xs @ ys) \<restriction>\<^sub>l A = (xs \<restriction>\<^sub>l A) @ (ys \<restriction>\<^sub>l A)"
  by (simp add: seq_filter_def)

subsection {* Distributed Concatenation *}

definition uncurry :: "('a \<Rightarrow> 'b \<Rightarrow>  'c) \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'c)" where
[simp]: "uncurry f = (\<lambda>(x, y). f x y)"

definition dist_concat ::
  "'a list set \<Rightarrow> 'a list set \<Rightarrow> 'a list set" (infixr "\<^sup>\<frown>" 100) where
"dist_concat ls1 ls2 = (uncurry (op @) ` (ls1 \<times> ls2))"

lemma dist_concat_left_empty [simp]:
  "{} \<^sup>\<frown> ys = {}"
  by (simp add: dist_concat_def)

lemma dist_concat_right_empty [simp]:
  "xs \<^sup>\<frown> {} = {}"
  by (simp add: dist_concat_def)

lemma dist_concat_insert [simp]:
"insert l ls1 \<^sup>\<frown> ls2 = ((op @ l) ` ( ls2)) \<union> (ls1 \<^sup>\<frown> ls2)"
  by (auto simp add: dist_concat_def)
end