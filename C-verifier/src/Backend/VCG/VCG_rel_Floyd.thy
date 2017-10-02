section \<open>VCG for total correctness using Floyd assignment\<close>

theory VCG_rel_Floyd                                           
  imports "../../Midend-IVL/Isabelle-UTP-Extended/hoare/HoareLogic/PartialCorrectness/utp_hoare"
begin

text \<open>The below definition helps in asserting independence for a group of lenses, as otherwise the
number of assumptions required increases greatly. Unfortunately, it is not usable with lenses of
different types as Isabelle does not allow heterogenous lists; element types must be unifiable.\<close>
definition \<open>lens_indep_all lenses \<longleftrightarrow> (\<forall>l \<in> set lenses. vwb_lens l \<and> eff_lens l) \<and>
                                      (\<forall>i j. i < length lenses \<and> j < length lenses \<and>
                                             i \<noteq> j \<longrightarrow> lenses!i \<bowtie> lenses!j)\<close>
lemma lens_indep_all_alt:
  \<open>lens_indep_all lenses \<longleftrightarrow> (\<forall>l \<in> set lenses. vwb_lens l \<and> eff_lens l) \<and>
                              distinct lenses \<and>
                             (\<forall>a \<in> set lenses. \<forall>b \<in> set lenses. a \<noteq> b \<longrightarrow> a \<bowtie> b)\<close>
  unfolding lens_indep_all_def distinct_conv_nth
  apply (safe; simp?)
   apply (metis lens_indep_quasi_irrefl nth_mem vwb_lens_wb)
  apply (metis in_set_conv_nth)
  done

named_theorems hoare_rules

lemma assert_hoare_r'[hoare_rules]:
  assumes \<open>`p \<Rightarrow> c`\<close>
  shows \<open>\<lbrace>p\<rbrace>c\<^sub>\<bottom>\<lbrace>p \<and> c\<rbrace>\<^sub>u\<close>
  using assms
  by (metis assert_hoare_r conj_comm hoare_false refBy_order skip_hoare_r
      utp_pred_laws.inf.orderE utp_pred_laws.inf_compl_bot_left1)

lemma assume_hoare_r'[hoare_rules]:
  shows \<open>\<lbrace>p\<rbrace>c\<^sup>\<top>\<lbrace>p \<and> c\<rbrace>\<^sub>u\<close>
  by rel_simp

lemma cond_hoare_r'[hoare_rules]:
  assumes \<open>\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>u\<close> and \<open>\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>s\<rbrace>\<^sub>u\<close>
  shows \<open>\<lbrace>p\<rbrace>if\<^sub>u b then C\<^sub>1 else C\<^sub>2 \<lbrace>q \<or> s\<rbrace>\<^sub>u\<close>
  by (insert assms, rel_auto)

(*lemma cond_assert_hoare_r[hoare_rules]: (* Needs some heuristics *)
  assumes \<open>\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>u\<close>
      and \<open>\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>s\<rbrace>\<^sub>u\<close>
      and \<open>`q \<Rightarrow> A`\<close>
      and \<open>`s \<Rightarrow> A`\<close>
      and \<open>\<lbrace>A\<rbrace>P\<lbrace>A'\<rbrace>\<^sub>u\<close>
    shows \<open>\<lbrace>p\<rbrace>if\<^sub>u b then C\<^sub>1 else C\<^sub>2;; A\<^sub>\<bottom>;; P\<lbrace>A'\<rbrace>\<^sub>u\<close>
  apply (insert assms)
  apply (rule hoare_post_weak)
   apply (rule cond_hoare_r' seq_hoare_r|assumption)+
    apply (rule assert_hoare_r')
  using impl_disjI apply blast
   apply (rule hoare_pre_str[where p\<^sub>2 = A])
    apply (simp add: disj_comm impl_alt_def)
    apply assumption
  apply pred_auto
  done
*)

lemma cond_assert_last_hoare_r[hoare_rules]:
  assumes \<open>\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>u\<close>
      and \<open>\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>s\<rbrace>\<^sub>u\<close>
      and \<open>`q \<Rightarrow> A`\<close>
      and \<open>`s \<Rightarrow> A`\<close>
      and \<open>`A \<Rightarrow> A'`\<close>
    shows \<open>\<lbrace>p\<rbrace>if\<^sub>u b then C\<^sub>1 else C\<^sub>2;; A\<^sub>\<bottom>\<lbrace>A'\<rbrace>\<^sub>u\<close>
  apply (insert assms)
  apply (rule hoare_post_weak)
   apply (rule cond_hoare_r' seq_hoare_r|assumption)+
   apply (rule assert_hoare_r')
  using impl_disjI apply blast
  by (metis impl_alt_def subsumption1 utp_pred_laws.compl_inf utp_pred_laws.inf_commute utp_pred_laws.sup_cancel_left2 utp_pred_laws.sup_commute utp_pred_laws.sup_inf_distrib1 utp_pred_laws.sup_left_idem)

lemma while_invr_hoare_r'[hoare_rules]:
  assumes \<open>`pre \<Rightarrow> p`\<close> and \<open>\<lbrace>p \<and> b\<rbrace>C\<lbrace>p'\<rbrace>\<^sub>u\<close> and \<open>`p' \<Rightarrow> p`\<close>
  shows \<open>\<lbrace>pre\<rbrace>while b invr p do C od\<lbrace>\<not>b \<and> p\<rbrace>\<^sub>u\<close>
  by (metis while_inv_def assms hoare_post_weak hoare_pre_str while_hoare_r)

lemma nu_refine_intro[hoare_rules]:
  assumes \<open>(C \<Rightarrow> S) \<sqsubseteq> F(C \<Rightarrow> S)\<close>
  shows \<open>(C \<Rightarrow> S) \<sqsubseteq> \<nu> F\<close>
  using assms
  by (simp add: lfp_lowerbound)

lemma nu_hoare_basic_r[hoare_rules]:
  assumes \<open>\<And>p. \<lbrace>P\<rbrace>p\<lbrace>Q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>P\<rbrace>F p\<lbrace>Q\<rbrace>\<^sub>u\<close>
  shows \<open>\<lbrace>P\<rbrace>\<nu> F\<lbrace>Q\<rbrace>\<^sub>u\<close>
  using assms unfolding hoare_r_def
  by (rule nu_refine_intro) auto

definition annot_rec ::
  \<open>'a upred \<Rightarrow> 'a upred \<Rightarrow> ((bool, 'a) hexpr \<Rightarrow> (bool, 'a) hexpr) \<Rightarrow> (bool, 'a) hexpr\<close> where
  \<open>annot_rec P Q F \<equiv> \<nu> F\<close>

syntax
  "_nu_annot" :: \<open>pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic\<close> ("\<nu> _ [_\<Rightarrow>_] \<bullet> _" [0, 10] 10)

translations
  "\<nu> X [P\<Rightarrow>Q] \<bullet> p" == "CONST annot_rec P Q (\<lambda> X. p)"

lemma nu_hoare_r(* [hoare_rules] *):
  assumes PRE: \<open>`P' \<Rightarrow> P`\<close>
  assumes IH: \<open>\<And>p. \<lbrace>P\<rbrace>p\<lbrace>Q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>P\<rbrace>F p\<lbrace>Q\<rbrace>\<^sub>u\<close>
  shows \<open>\<lbrace>P'\<rbrace>\<nu> F\<lbrace>Q\<rbrace>\<^sub>u\<close>
  apply (rule hoare_pre_str[OF PRE])
  using IH
  unfolding hoare_r_def
  by (rule nu_refine_intro) (rule order_refl)

lemma nu_hoare_annot_r[hoare_rules]:
  assumes PRE: \<open>`P' \<Rightarrow> P`\<close>
  assumes IH: \<open>\<And>p. \<lbrace>P\<rbrace>p\<lbrace>Q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>P\<rbrace>F p\<lbrace>Q\<rbrace>\<^sub>u\<close>
  shows \<open>\<lbrace>P'\<rbrace>annot_rec P Q F\<lbrace>Q\<rbrace>\<^sub>u\<close>
  using nu_hoare_r assms unfolding annot_rec_def .

lemmas [hoare_rules] =
  assigns_floyd_r
  skip_hoare_r
  seq_hoare_r

named_theorems vcg_simps
lemmas [vcg_simps] =
  lens_indep.lens_put_irr1
  lens_indep.lens_put_irr2
  lens_indep_all_alt

named_theorems hoare_rules_extra and vcg_dests

method exp_vcg_pre = (simp only: seqr_assoc[symmetric])?, rule hoare_post_weak
method solve_dests = safe?; simp?; drule vcg_dests; assumption?; (simp add: vcg_simps)?
method solve_vcg = assumption|pred_simp?, (simp add: vcg_simps)?;(solve_dests; fail)?
method exp_vcg_step = rule hoare_rules_extra|rule hoare_rules|solve_vcg; fail
method exp_vcg = exp_vcg_pre, exp_vcg_step+

end
