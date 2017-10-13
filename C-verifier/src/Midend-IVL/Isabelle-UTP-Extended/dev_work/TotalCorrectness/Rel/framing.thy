section \<open>Work on framing and function calls\<close>

theory framing
imports
  "../../../../../Backend/VCG/VCG_rel_Floyd"
  "../../../utils/vcg_helpers"
begin

text \<open>Using locales for modularity\<close>

locale peter =
  fixes lvars :: \<open>'l \<Longrightarrow> 's\<close>
    and gvars :: \<open>'g \<Longrightarrow> 's\<close>
    and   ret :: \<open>nat \<Longrightarrow> 'g\<close>
    and     x :: \<open>nat \<Longrightarrow> 'l\<close>
    and     y :: \<open>nat \<Longrightarrow> 'l\<close>
  assumes INDEP: \<open>lvars \<bowtie> gvars\<close> \<open>x \<bowtie> y\<close>
          \<open>vwb_lens lvars\<close> \<open>vwb_lens gvars\<close> \<open>vwb_lens ret\<close> \<open>vwb_lens x\<close> \<open>vwb_lens y\<close>
begin
abbreviation \<open>Lx \<equiv> x ;\<^sub>L lvars\<close>
abbreviation \<open>Ly \<equiv> y ;\<^sub>L lvars\<close>
abbreviation \<open>Gret \<equiv> ret ;\<^sub>L gvars\<close>

term \<open>subst_upd id (x ;\<^sub>L lvars)\<close>
term \<open>antiframe gvars (Lx :== (&Lx + \<guillemotleft>1\<guillemotright>))\<close>

definition \<open>f r a = gvars:[Lx :== a ;; Lx :== (&Lx + \<guillemotleft>1\<guillemotright>);; Gret:==&Lx];; r :== &Gret\<close>

lemma f_rule:
  assumes \<open>vwb_lens r\<close>
  shows \<open>\<lbrace> e=\<^sub>u\<guillemotleft>val\<guillemotright> \<rbrace> f r e \<lbrace> &r=\<^sub>u\<guillemotleft>val+1\<guillemotright> \<rbrace>\<^sub>u\<close>
  unfolding f_def using assms INDEP
  by rel_simp

definition (in -) \<open>EXINV l P \<equiv> \<^bold>\<exists>st \<bullet> P\<lbrakk>(\<guillemotleft>st\<guillemotright> \<oplus> &\<Sigma> on &l)/&\<Sigma>\<rbrakk>\<close>

subsection \<open>Modification is existential\<close>

definition (in -) \<open>modifies x \<equiv> \<^bold>\<exists>v' \<bullet> $\<Sigma>\<acute> \<oplus> \<guillemotleft>v'\<guillemotright> on &x =\<^sub>u $\<Sigma>\<close>
abbreviation (in -) ref_modifies (infix "\<flat>" 95) where
  \<open>x \<flat> c \<equiv> modifies x \<sqsubseteq> c\<close>

lemma (in -) modifies_to_ext:
  assumes \<open>vwb_lens x\<close>
      and \<open>modifies x \<sqsubseteq> c\<close> (* TODO: use notation? *)
  shows \<open>\<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u\<close>
  using assms unfolding modifies_def
  by rel_simp metis

lemma (in -) ext_to_modifies:
  assumes \<open>vwb_lens x\<close>
      and \<open>\<forall>P. \<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u\<close>
  shows \<open>modifies x \<sqsubseteq> c\<close>
  using assms unfolding modifies_def
  apply - \<comment> \<open>Why do we need to inline the assumptions? Weird.\<close>
  apply rel_simp
  by (metis skip_r_eq subst.rep_eq vwb_lens.put_eq)

lemma (in -) modifies_ext:
  assumes \<open>vwb_lens x\<close>
  shows \<open>modifies x \<sqsubseteq> c = (\<forall>P. \<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u)\<close>
  by (metis assms modifies_to_ext ext_to_modifies)

subsection \<open>Region-based modifies\<close>

definition (in -) region :: \<open>('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha> set\<close> where
  \<open>region x s = {s'. \<exists>v. s' = put\<^bsub>x\<^esub> s v}\<close>

definition (in -) region_modifies :: \<open>('\<alpha> \<Rightarrow> '\<alpha> set) \<Rightarrow> _\<close> where
  \<open>region_modifies reg \<equiv> $\<Sigma> \<in>\<^sub>u uop reg $\<Sigma>\<acute>\<close>

lemma (in -) region_modifies_to_ext:
  assumes \<open>region_modifies (region x) \<sqsubseteq> c\<close>
  shows \<open>\<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u\<close>
  using assms unfolding region_modifies_def region_def
  by rel_simp blast

lemma (in -) ext_to_region_modifies:
  assumes \<open>\<forall>P. \<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u\<close>
  shows \<open>region_modifies (region x) \<sqsubseteq> c\<close>
  using assms unfolding region_modifies_def region_def
  by rel_simp (metis skip_r_eq subst.rep_eq)

lemma (in -) region_modifies_ext:
  \<open>region_modifies (region x) \<sqsubseteq> c = (\<forall>P. \<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u)\<close>
  using ext_to_region_modifies region_modifies_to_ext
  by blast

subsection \<open>Antiframe rule work\<close>

lemma antiframe_rule[hoare_rules]:
  assumes \<open>vwb_lens a\<close> \<open>\<lbrace>P\<rbrace>c\<lbrace>Q\<rbrace>\<^sub>u\<close>
  shows \<open>\<lbrace>P\<rbrace> a:[c] \<lbrace>(\<exists>a \<bullet> P) \<and> (EXINV a Q)\<rbrace>\<^sub>u\<close>
  using assms unfolding EXINV_def
  apply rel_simp
  apply pred_simp
  by (metis assms(1) vwb_lens_wb wb_lens.get_put)

declare assigns_floyd_r[hoare_rules del]
lemma (in -) assigns_floyd_rX [hoare_rules]:
  assumes \<open>vwb_lens x\<close>
  shows   \<open>\<lbrace>p\<rbrace>x :== e\<lbrace>(\<exists>x \<bullet> p) \<and> (\<^bold>\<exists>v \<bullet> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>)\<rbrace>\<^sub>u\<close>
  apply (insert assms)
  apply pred_simp
  apply transfer
  apply rule
   apply (rule_tac x = \<open>get\<^bsub>x\<^esub> a\<close> in exI)
    (*subgoal for a x p e
   apply (rule exI[where x="get\<^bsub>x\<^esub> a"])*)
   apply auto
  apply (rule_tac x = \<open>get\<^bsub>x\<^esub> a\<close> in exI)
  apply auto
  done

lemma (in -) modified_assign_rule:
  assumes \<open>vwb_lens x\<close>
  shows   \<open>\<lbrace>p\<rbrace>x :== e\<lbrace>(\<exists>x \<bullet> p)\<rbrace>\<^sub>u\<close>
  apply (rule hoare_post_weak)
   apply (rule assigns_floyd_rX)
   apply fact
  apply pred_simp
  done

lemma (in -) EXINV_pull_out_sublens:
  assumes A: \<open>vwb_lens x\<close> \<open>vwb_lens l\<close>
  defines \<open>XX \<equiv> x;\<^sub>Ll\<close>
  shows \<open>EXINV l (\<exists>XX \<bullet> P ) = (\<exists>XX \<bullet> EXINV l P)\<close>
  unfolding EXINV_def XX_def using A
  by pred_blast

lemma (in -) EXINV_drop_indep:
  assumes A: \<open>vwb_lens l\<^sub>1\<close> \<open>vwb_lens l\<^sub>2\<close> \<open>l\<^sub>1 \<bowtie> l\<^sub>2\<close>
  shows "EXINV l\<^sub>1 (\<exists>l\<^sub>2 \<bullet> P) = (EXINV l\<^sub>1 P)"
  unfolding EXINV_def using A
  by pred_simp (metis lens_indep_def vwb_lens_wb wb_lens.get_put)

lemma (in -) lens_indep_right_ext' [intro, simp]:
  \<open>z \<bowtie> x \<Longrightarrow> x \<bowtie> (y ;\<^sub>L z)\<close>
  using lens_indep_sym by blast

lemma (in -) lens_indep_left_ext' [intro, simp]:
  \<open>x \<bowtie> z \<Longrightarrow> (y ;\<^sub>L z) \<bowtie> x\<close>
  using lens_indep_sym by blast

(*lemmas [simp] = lens_indep_right_ext lens_indep_left_ext*)

lemma conj_ex2_move_front: \<open>l \<sharp> P \<Longrightarrow> (P \<and> (\<exists>l \<bullet> Q)) = (\<exists>l \<bullet> P \<and> Q)\<close>
  by pred_simp

lemma (in -) dep_unrest_ex:
  assumes A: \<open>vwb_lens x\<close> \<open>vwb_lens l\<close>
  defines \<open>XX \<equiv> x;\<^sub>Ll\<close>
  shows \<open>XX \<sharp> (\<exists> l \<bullet> F)\<close>
  unfolding XX_def using A
  by pred_simp

lemma (in -)
  assumes \<open>vwb_lens l\<close>
  shows \<open>((\<exists> l \<bullet> F) \<and> EXINV l F) = F\<close>
  using assms
  unfolding EXINV_def
  apply pred_simp
  apply transfer
  oops

lemma (in -) \<open>(\<exists>x. P x y) \<and> (\<exists>y. P x y) \<Longrightarrow> P x y\<close>
  oops

lemma
  assumes \<open>vwb_lens r\<close>
  shows \<open>\<lbrace> F \<rbrace> f r a \<lbrace> \<exists> r \<bullet> \<exists> Gret \<bullet> F \<rbrace>\<^sub>u\<close>
  unfolding f_def using INDEP assms
    supply assigns_floyd_rX [hoare_rules del]
  supply modified_assign_rule[hoare_rules]
  apply -
  apply exp_vcg
  apply (simp add: EXINV_pull_out_sublens EXINV_drop_indep conj_ex2_move_front dep_unrest_ex)
  unfolding EXINV_def
  apply pred_simp
  apply (subst conj_ex2_move_front)
  oops
  apply (subst EXINV_drop_indep)
  apply simp
  apply simp
  apply (rule lens_indep_sym)
  solve_direct
  using lens_indep_sym apply blast
  apply simp
  oops
  apply solve_vcg
  apply pred_simp
  apply (simp add: vwb_lens_wb[THEN wb_lens.get_put])



end

end
