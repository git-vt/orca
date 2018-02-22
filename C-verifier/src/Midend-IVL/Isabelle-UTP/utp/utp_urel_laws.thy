section {* UTP variables *}

theory utp_urel_laws
  imports "../../Isabelle-UTP-Extended/theories/Rel/utp_rel_more"
begin

subsection {* Unrestriction Laws *}
lemma unrest_iuvar [unrest]: 
  "out\<alpha> \<sharp> $x" 
  by ( rel_auto)
 
lemma unrest_ouvar [unrest]: 
  "in\<alpha> \<sharp> $x\<acute>" 
  by (rel_auto)

lemma unrest_semir_undash [unrest]:
  fixes x :: "('a\<Longrightarrow> '\<alpha>)"
  assumes "$x \<sharp> P"
  shows "$x \<sharp> P ;; Q"
  using assms by (rel_auto) 

lemma unrest_semir_dash [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "$x\<acute> \<sharp> Q"
  shows "$x\<acute> \<sharp> P ;; Q"
  using assms by (rel_auto)


lemma unrest_in\<alpha>_var [unrest]:
  "\<lbrakk> mwb_lens x; in\<alpha> \<sharp> (P :: ('\<alpha>, '\<beta>) rel) \<rbrakk> \<Longrightarrow> $x \<sharp> P"
  by (pred_auto)

lemma unrest_out\<alpha>_var [unrest]:
  "\<lbrakk> mwb_lens x; out\<alpha> \<sharp> (P :: ('\<alpha>, '\<beta>) rel) \<rbrakk> \<Longrightarrow> $x\<acute> \<sharp> P"
  by (pred_auto)

lemma in\<alpha>_uvar [simp]: "vwb_lens in\<alpha>"
  by (unfold_locales, auto simp add: in\<alpha>_def)

lemma out\<alpha>_uvar [simp]: "vwb_lens out\<alpha>"
  by (unfold_locales, auto simp add: out\<alpha>_def)

lemma unrest_pre_out\<alpha> [unrest]: "out\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub><"
  by (transfer, auto simp add: out\<alpha>_def)

lemma unrest_post_in\<alpha> [unrest]: "in\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>>"
  by (transfer, auto simp add: in\<alpha>_def)

lemma unrest_pre_in_var [unrest]:
  "x \<sharp> p1 \<Longrightarrow> $x \<sharp> \<lceil>p1\<rceil>\<^sub><"
  by (transfer, simp)

lemma unrest_post_out_var [unrest]:
  "x \<sharp> p1 \<Longrightarrow> $x\<acute> \<sharp> \<lceil>p1\<rceil>\<^sub>>"
  by (transfer, simp)

lemma unrest_convr_out\<alpha> [unrest]:
  "in\<alpha> \<sharp> p \<Longrightarrow> out\<alpha> \<sharp> p\<^sup>-"
  by (pred_auto)

lemma unrest_convr_in\<alpha> [unrest]:
  "out\<alpha> \<sharp> p \<Longrightarrow> in\<alpha> \<sharp> p\<^sup>-"
  by (pred_auto)

lemma unrest_in_rel_var_res [unrest]:
  "vwb_lens x \<Longrightarrow> $x \<sharp> (P \<restriction>\<^sub>\<alpha> x)"
  by (simp add: rel_var_res_def unrest)
 
lemma unrest_out_rel_var_res [unrest]:
  "vwb_lens x \<Longrightarrow> $x\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> x)"
  by (simp add: rel_var_res_def unrest)

lemma unrest_in_rel_var_res_mwb [unrest]:
  "mwb_lens x \<Longrightarrow> $x \<sharp> (P \<restriction>\<^sub>\<alpha> x)"
  by (simp add: rel_var_res_def unrest)
 
lemma unrest_out_rel_var_res_mwb [unrest]:
  "mwb_lens x \<Longrightarrow> $x\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> x)"
  by (simp add: rel_var_res_def unrest)

subsection {* Substitution laws *}

lemma subst_seq_left [usubst]:
  "out\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P ;; Q) = (\<sigma> \<dagger> P) ;; Q"
  by transfer (rel_auto, (metis (no_types, lifting) Pair_inject surjective_pairing)+)

lemma subst_seq_right [usubst]:
  "in\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P ;; Q) = P ;; (\<sigma> \<dagger> Q)"
  by transfer (rel_auto, (metis (no_types, lifting) Pair_inject surjective_pairing)+)

text {* The following laws support substitution in heterogeneous relations for polymorphically
  types literal expressions. These cannot be supported more generically due to limitations
  in HOL's type system. The laws are presented in a slightly strange way so as to be as 
  general as possible. *}

lemma bool_seqr_laws [usubst]:
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s true) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>true/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s false) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>false/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s true) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>true/$x\<acute>\<rbrakk>)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s false) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>false/$x\<acute>\<rbrakk>)"
    by (transfer, rel_auto)+

lemma zero_one_seqr_laws [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows 
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s 0) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>0/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s 1) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>1/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s 0) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>0/$x\<acute>\<rbrakk>)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s 1) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>1/$x\<acute>\<rbrakk>)"
    by (transfer, rel_auto)+

lemma numeral_seqr_laws [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows 
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s numeral n) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>numeral n/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s numeral n) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>numeral n/$x\<acute>\<rbrakk>)"
  by (transfer, rel_auto)+    

lemma usubst_condr [usubst]:
  "\<sigma> \<dagger> ( P \<triangleleft> b \<triangleright> Q) = (\<sigma> \<dagger> P \<triangleleft> \<sigma> \<dagger> b \<triangleright> \<sigma> \<dagger> Q)"
  unfolding cond_def
  by rel_auto
 
lemma subst_skip_r [usubst]:
  "out\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> II = \<langle>\<lfloor>\<sigma>\<rfloor>\<^sub>s\<rangle>\<^sub>a"
  by (rel_simp, (metis (mono_tags, lifting) prod.sel(1) sndI surjective_pairing)+)

lemma usubst_upd_in_comp [usubst]:
  "\<sigma>(&in\<alpha>:x \<mapsto>\<^sub>s v) = \<sigma>($x \<mapsto>\<^sub>s v)"
  by (pred_auto)

lemma usubst_upd_out_comp [usubst]:
  "\<sigma>(&out\<alpha>:x \<mapsto>\<^sub>s v) = \<sigma>($x\<acute> \<mapsto>\<^sub>s v)"
  by (pred_auto)

lemma subst_lift_upd [usubst]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "\<lceil>\<sigma>(x \<mapsto>\<^sub>s v)\<rceil>\<^sub>s = \<lceil>\<sigma>\<rceil>\<^sub>s($x \<mapsto>\<^sub>s \<lceil>v\<rceil>\<^sub><)"
  by pred_auto

lemma subst_drop_upd [usubst]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "\<lfloor>\<sigma>($x \<mapsto>\<^sub>s v)\<rfloor>\<^sub>s = \<lfloor>\<sigma>\<rfloor>\<^sub>s(x \<mapsto>\<^sub>s \<lfloor>v\<rfloor>\<^sub><)"
  by  (pred_simp)

lemma subst_lift_pre [usubst]: "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> \<lceil>b\<rceil>\<^sub>< = \<lceil>\<sigma> \<dagger> b\<rceil>\<^sub><"
  by (metis apply_subst_ext fst_vwb_lens in\<alpha>_def)

lemma unrest_usubst_lift_in [unrest]:
  "x \<sharp> P \<Longrightarrow> $x \<sharp> \<lceil>P\<rceil>\<^sub>s"
  by (pred_simp)

lemma unrest_usubst_lift_out [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "$x\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>s"
  by (pred_simp)

subsection {* Relation laws *}

lemma drop_pre_inv [simp]: "\<lbrakk> out\<alpha> \<sharp> p \<rbrakk> \<Longrightarrow> \<lceil>\<lfloor>p\<rfloor>\<^sub><\<rceil>\<^sub>< = p"
  by (pred_simp)

lemma seqr_true_lemma:
  "(P = (\<not> ((\<not> P) ;; true))) = (P = (P ;; true))"
  by (rel_auto)
 theorem precond_equiv:
  "P = (P ;; true) \<longleftrightarrow> (out\<alpha> \<sharp> P)"
  by (rel_auto)

theorem postcond_equiv:
  "P = (true ;; P) \<longleftrightarrow> (in\<alpha> \<sharp> P)"
  by (rel_auto)   
lemma precond_right_unit: "out\<alpha> \<sharp> p \<Longrightarrow> (p ;; true) = p"
  by (metis precond_equiv)
    
theorem seqr_post_transfer: "out\<alpha> \<sharp> q \<Longrightarrow> (P ;; (q \<and> R)) = ((P \<and> q\<^sup>-) ;; R)"
  by (rel_auto)

lemma seqr_pre_out: "out\<alpha> \<sharp> p \<Longrightarrow> ((p \<and> Q) ;; R) = (p \<and> (Q ;; R))"
  by (rel_blast)

lemma postcond_left_unit: "in\<alpha> \<sharp> p \<Longrightarrow> (true ;; p) = p"
  by (metis postcond_equiv)
    
lemma seqr_to_conj: "\<lbrakk> out\<alpha> \<sharp> P; in\<alpha> \<sharp> Q \<rbrakk> \<Longrightarrow> (P ;; Q) = (P \<and> Q)"
  by (metis postcond_left_unit seqr_pre_out utp_pred_laws.inf_top.right_neutral)

lemma shEx_lift_seq_1 [uquant_lift]:
  "((\<^bold>\<exists> x \<bullet> P x) ;; Q) = (\<^bold>\<exists> x \<bullet> (P x ;; Q))"
  by pred_auto

lemma shEx_lift_seq_2 [uquant_lift]:
  "(P ;; (\<^bold>\<exists> x \<bullet> Q x)) = (\<^bold>\<exists> x \<bullet> (P ;; Q x))"
  by pred_auto    
 
subsection {* Iterated Sequential Composition Laws *}
  
lemma iter_seqr_nil [simp]: "(;; i : [] \<bullet> P(i)) = II"
  by (simp add: seqr_iter_def)
    
lemma iter_seqr_cons [simp]: "(;; i : (x # xs) \<bullet> P(i)) = P(x) ;; (;; i : xs \<bullet> P(i))"
  by (simp add: seqr_iter_def)
    
text {* Quantale laws for relations *}

lemma seq_Sup_distl: "P ;; (\<Sqinter> A) = (\<Sqinter> Q\<in>A. P ;; Q)"
  by (transfer, rel_auto)
    
lemma seq_Sup_distr: "(\<Sqinter> A) ;; Q = (\<Sqinter> P\<in>A. P ;; Q)"
  by (transfer, auto)
    
lemma seq_UINF_distl: "P ;; (\<Sqinter> Q\<in>A \<bullet> F(Q)) = (\<Sqinter> Q\<in>A \<bullet> P ;; F(Q))"
  by (simp add: UINF_as_Sup_collect seq_Sup_distl)

lemma seq_UINF_distl': "P ;; (\<Sqinter> Q \<bullet> F(Q)) = (\<Sqinter> Q \<bullet> P ;; F(Q))"
  by (metis UINF_mem_UNIV seq_UINF_distl)
    
lemma seq_UINF_distr: "(\<Sqinter> P\<in>A \<bullet> F(P)) ;; Q = (\<Sqinter> P\<in>A \<bullet> F(P) ;; Q)"
  by (simp add: UINF_as_Sup_collect seq_Sup_distr)

lemma seq_UINF_distr': "(\<Sqinter> P \<bullet> F(P)) ;; Q = (\<Sqinter> P \<bullet> F(P) ;; Q)"
  by (metis UINF_mem_UNIV seq_UINF_distr)

lemma seq_SUP_distl: "P ;; (\<Sqinter>i\<in>A. Q(i)) = (\<Sqinter>i\<in>A. P ;; Q(i))"
  by (metis image_image seq_Sup_distl)

lemma seq_SUP_distr: "(\<Sqinter>i\<in>A. P(i)) ;; Q = (\<Sqinter>i\<in>A. P(i) ;; Q)"
  by (simp add: seq_Sup_distr)
    
lemma impl_seqr_mono: "\<lbrakk> `P \<Rightarrow> Q`; `R \<Rightarrow> S` \<rbrakk> \<Longrightarrow> `(P ;; R) \<Rightarrow> (Q ;; S)`"
  by transfer (pred_blast)

lemma seqr_mono:
  "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 ;; Q\<^sub>1) \<sqsubseteq> (P\<^sub>2 ;; Q\<^sub>2)"
  by transfer (rel_blast)

lemma seqr_monotonic: 
  "\<lbrakk> mono P; mono Q \<rbrakk> \<Longrightarrow> mono (\<lambda> X. P X ;; Q X)"
  by (simp add: mono_def, transfer ,rel_blast)

lemma cond_mono:
  "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 \<triangleleft> b \<triangleright> Q\<^sub>1) \<sqsubseteq> (P\<^sub>2 \<triangleleft> b \<triangleright> Q\<^sub>2)"
  unfolding cond_def
  by transfer (rel_auto)

lemma cond_monotonic:
  "\<lbrakk> mono P; mono Q \<rbrakk> \<Longrightarrow> mono (\<lambda> X. P X \<triangleleft> b \<triangleright> Q X)"
  unfolding cond_def
  by (simp add: mono_def, rel_blast)

lemma spec_refine:
  "Q \<sqsubseteq> (P \<and> R) \<Longrightarrow> (P \<Rightarrow> Q) \<sqsubseteq> R"
  by (rel_auto)

lemma cond_skip: "out\<alpha> \<sharp> b \<Longrightarrow> (b \<and> II) = (II \<and> b\<^sup>-)"
  by (rel_auto)


lemma assigns_subst [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>a"
  by transfer (rel_auto)

lemma assigns_r_comp: "(\<langle>\<sigma>\<rangle>\<^sub>a ;; P) = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P)"
  by transfer rel_auto

lemma assigns_r_feasible:
  "(\<langle>\<sigma>\<rangle>\<^sub>a ;; true) = true"
  by (simp add: assigns_r_comp subst_true)

lemma assign_subst [usubst]:
  "\<lbrakk> mwb_lens x; mwb_lens y \<rbrakk> \<Longrightarrow> [$x \<mapsto>\<^sub>s \<lceil>u\<rceil>\<^sub><] \<dagger> (y :== v) = (x, y :== u, [x \<mapsto>\<^sub>s u] \<dagger> v)"
  by rel_auto

lemma assigns_idem: "mwb_lens x \<Longrightarrow> (x,x :== u,v) = (x :== v)"
  by (simp add: usubst)

lemma assigns_comp: "(\<langle>f\<rangle>\<^sub>a ;; \<langle>g\<rangle>\<^sub>a) = \<langle>g \<circ> f\<rangle>\<^sub>a"
  by (simp add: assigns_r_comp usubst)

lemma assigns_r_conv:
  "bij f \<Longrightarrow> \<langle>f\<rangle>\<^sub>a\<^sup>- = \<langle>inv f\<rangle>\<^sub>a"
  by transfer (rel_auto, simp_all add: bij_is_inj bij_is_surj surj_f_inv_f)

lemma assign_pred_transfer:
  fixes x :: "('a\<Longrightarrow> '\<alpha>)"
  assumes "$x \<sharp> b" "out\<alpha> \<sharp> b"
  shows "(b \<and> x :== v) = (x :== v \<and> b\<^sup>-)"
  using assms by rel_blast

lemma assigns_r_ufunc: "ufunctional \<langle>f\<rangle>\<^sub>a"
  by (rel_auto)

lemma assigns_r_uinj: "inj f \<Longrightarrow> uinj \<langle>f\<rangle>\<^sub>a"
  by (rel_simp, simp add: inj_eq)

lemma assigns_r_swap_uinj:
  "\<lbrakk> vwb_lens x; vwb_lens y; x \<bowtie> y \<rbrakk> \<Longrightarrow> uinj (x,y :== &y,&x)"
  using assigns_r_uinj swap_usubst_inj by rel_auto

lemma skip_r_unfold:
  "vwb_lens x \<Longrightarrow> II = ($x\<acute> =\<^sub>u $x \<and> II\<restriction>\<^sub>\<alpha>x)"
  by (rel_auto, metis mwb_lens.put_put vwb_lens_mwb vwb_lens_wb wb_lens.get_put)

lemma skip_ra_unfold:
  "II\<^bsub>x;y\<^esub> = ($x\<acute> =\<^sub>u $x \<and> II\<^bsub>y\<^esub>)"
  by (rel_auto)

lemma skip_res_as_ra:
  "\<lbrakk> vwb_lens y; x +\<^sub>L y \<approx>\<^sub>L 1\<^sub>L; x \<bowtie> y \<rbrakk> \<Longrightarrow> II\<restriction>\<^sub>\<alpha>x = II\<^bsub>y\<^esub>"
  apply (rel_auto)
  apply (metis (no_types, lifting) lens_indep_def)
  apply (metis vwb_lens.put_eq)
done

lemma assign_unfold:
  "vwb_lens x \<Longrightarrow> (x :== v) = ($x\<acute> =\<^sub>u \<lceil>v\<rceil>\<^sub>< \<and> II\<restriction>\<^sub>\<alpha>x)"
  apply (rel_auto, auto simp add: comp_def)
  using vwb_lens.put_eq by fastforce

lemma seqr_and_distr_ufunc:
  "ufunctional P \<Longrightarrow> (P ;; (Q \<and> R)) = ((P ;; Q) \<and> (P ;; R))"
  by rel_auto

lemma seqr_and_distl_uinj:
  "uinj R \<Longrightarrow> ((P \<and> Q) ;; R) = ((P ;; R) \<and> (Q ;; R))"
  by (rel_auto)

theorem precond_left_zero:
  assumes "out\<alpha> \<sharp> p" "p \<noteq> false"
  shows "(true ;; p) = true"
  using assms by pred_auto

subsection {* Converse laws *}

lemma convr_invol [simp]: "p\<^sup>-\<^sup>- = p"
  by pred_auto

lemma lit_convr [simp]: "\<guillemotleft>v\<guillemotright>\<^sup>- = \<guillemotleft>v\<guillemotright>"
  by pred_auto

lemma uivar_convr [simp]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "($x)\<^sup>- = $x\<acute>"
  by pred_auto

lemma uovar_convr [simp]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "($x\<acute>)\<^sup>- = $x"
  by pred_auto

lemma uop_convr [simp]: "(uop f u)\<^sup>- = uop f (u\<^sup>-)"
  by (pred_auto)

lemma bop_convr [simp]: "(bop f u v)\<^sup>- = bop f (u\<^sup>-) (v\<^sup>-)"
  by (pred_auto)

lemma eq_convr [simp]: "(p =\<^sub>u q)\<^sup>- = (p\<^sup>- =\<^sub>u q\<^sup>-)"
  by (pred_auto)

lemma not_convr [simp]: "(\<not> p)\<^sup>- = (\<not> p\<^sup>-)"
  by (pred_auto)

lemma disj_convr [simp]: "(p \<or> q)\<^sup>- = (q\<^sup>- \<or> p\<^sup>-)"
  by (pred_auto)

lemma conj_convr [simp]: "(p \<and> q)\<^sup>- = (q\<^sup>- \<and> p\<^sup>-)"
  by (pred_auto)

lemma seqr_convr [simp]: "(p ;; q)\<^sup>- = (q\<^sup>- ;; p\<^sup>-)"
  by rel_auto

lemma pre_convr [simp]: "\<lceil>p\<rceil>\<^sub><\<^sup>- = \<lceil>p\<rceil>\<^sub>>"
  by (rel_auto)

lemma post_convr [simp]: "\<lceil>p\<rceil>\<^sub>>\<^sup>- = \<lceil>p\<rceil>\<^sub><"
  by (rel_auto)

theorem seqr_pre_transfer: "in\<alpha> \<sharp> q \<Longrightarrow> ((P \<and> q) ;; R) = (P ;; (q\<^sup>- \<and> R))"
  by (rel_auto)

theorem seqr_pre_transfer':
  "((P \<and> \<lceil>q\<rceil>\<^sub>>) ;; R) = (P ;; (\<lceil>q\<rceil>\<^sub>< \<and> R))"
  by (rel_auto)

theorem seqr_post_out: "in\<alpha> \<sharp> r \<Longrightarrow> (P ;; (Q \<and> r)) = ((P ;; Q) \<and> r)"
  by (rel_blast)

lemma seqr_post_var_out:
  fixes x :: "(bool \<Longrightarrow> '\<alpha>)"
  shows "(P ;; (Q \<and> $x\<acute>)) = ((P ;; Q) \<and> $x\<acute>)"
  by (rel_auto)

lemma seqr_pre_var_out:
  fixes x :: "(bool \<Longrightarrow> '\<alpha>)"
  shows "(($x \<and> P) ;; Q) = ($x \<and> (P ;; Q))"
  by (rel_auto)


subsection {* Relational unrestriction *}

text {* Relational unrestriction states that a variable is unchanged by a relation. Eventually
  I'd also like to have it state that the relation also does not depend on the variable's
  initial value, but I'm not sure how to state that yet. For now we represent this by
  the parametric healthiness condition RID. *}

definition RID :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel"
where "RID x P = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x)"

declare RID_def [urel_defs]

lemma RID_idem:
  "mwb_lens x \<Longrightarrow> RID(x)(RID(x)(P)) = RID(x)(P)"
  by (rel_auto)

lemma RID_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RID(x)(P) \<sqsubseteq> RID(x)(Q)"
  by (rel_auto)

lemma RID_skip_r:
  "vwb_lens x \<Longrightarrow> RID(x)(II) = II"
  apply (rel_auto) using vwb_lens.put_eq by fastforce

lemma RID_disj:
  "RID(x)(P \<or> Q) = (RID(x)(P) \<or> RID(x)(Q))"
  by (rel_auto)

lemma RID_conj:
  "vwb_lens x \<Longrightarrow> RID(x)(RID(x)(P) \<and> RID(x)(Q)) = (RID(x)(P) \<and> RID(x)(Q))"
  by (rel_auto)

lemma RID_assigns_r_diff:
  "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> RID(x)(\<langle>\<sigma>\<rangle>\<^sub>a) = \<langle>\<sigma>\<rangle>\<^sub>a"
  apply (rel_auto)
  apply (metis vwb_lens.put_eq)
  apply (metis vwb_lens_wb wb_lens.get_put wb_lens_weak weak_lens.put_get)
done

lemma RID_assign_r_same:
  "vwb_lens x \<Longrightarrow> RID(x)(x :== v) = II"
  apply (rel_auto)
  using vwb_lens.put_eq apply fastforce
done

lemma RID_seq_left:
  assumes "vwb_lens x"
  shows "RID(x)(RID(x)(P) ;; Q) = (RID(x)(P) ;; RID(x)(Q))"
proof -
  have "RID(x)(RID(x)(P) ;; Q) = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; Q) \<and> $x\<acute> =\<^sub>u $x)"
    by (simp add: RID_def usubst)
  also from assms have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> (\<exists> $x \<bullet> $x\<acute> =\<^sub>u $x)) ;; (\<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_auto)
  also from assms have "... = (((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    apply (rel_auto)
    apply (metis vwb_lens.put_eq)
    apply (metis mwb_lens.put_put vwb_lens_mwb)
  done
  also from assms have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp, metis (full_types) mwb_lens.put_put vwb_lens_def wb_lens_weak weak_lens.put_get)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp, fastforce)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)))"
    by (rel_auto)
  also have "... = (RID(x)(P) ;; RID(x)(Q))"
    by (rel_auto)
  finally show ?thesis .
qed

lemma RID_seq_right:
  assumes "vwb_lens x"
  shows "RID(x)(P ;; RID(x)(Q)) = (RID(x)(P) ;; RID(x)(Q))"
proof -
  have "RID(x)(P ;; RID(x)(Q)) = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (simp add: RID_def usubst)
  also from assms have "... = (((\<exists> $x \<bullet>  P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> (\<exists> $x\<acute> \<bullet> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_auto)
  also from assms have "... = (((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    apply (rel_auto)
    apply (metis vwb_lens.put_eq)
    apply (metis mwb_lens.put_put vwb_lens_mwb)
  done
  also from assms have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp, metis (full_types) mwb_lens.put_put vwb_lens_def wb_lens_weak weak_lens.put_get)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp, fastforce)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)))"
    by (rel_auto)
  also have "... = (RID(x)(P) ;; RID(x)(Q))"
    by (rel_auto)
  finally show ?thesis .
qed

definition unrest_relation :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> bool" (infix "\<sharp>\<sharp>" 20)
where "(x \<sharp>\<sharp> P) \<longleftrightarrow> (P = RID(x)(P))"

declare unrest_relation_def [urel_defs]

lemma skip_r_runrest [unrest]:
  "vwb_lens x \<Longrightarrow> x \<sharp>\<sharp> II"
  by (simp add: RID_skip_r unrest_relation_def)

lemma assigns_r_runrest:
  "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: RID_assigns_r_diff unrest_relation_def)

lemma seq_r_runrest [unrest]:
  assumes "vwb_lens x" "x \<sharp>\<sharp> P" "x \<sharp>\<sharp> Q"
  shows "x \<sharp>\<sharp> (P ;; Q)"
  by (metis RID_seq_left assms unrest_relation_def)

lemma false_runrest [unrest]: "x \<sharp>\<sharp> false"
  by (rel_auto)

lemma and_runrest [unrest]: "\<lbrakk> vwb_lens x; x \<sharp>\<sharp> P; x \<sharp>\<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> (P \<and> Q)"
  by (metis RID_conj unrest_relation_def)

lemma or_runrest [unrest]: "\<lbrakk> x \<sharp>\<sharp> P; x \<sharp>\<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> (P \<or> Q)"
  by (simp add: RID_disj unrest_relation_def)

subsection {* Alphabet laws *}

lemma aext_cond [alpha]:
  "(P \<triangleleft> b \<triangleright> Q) \<oplus>\<^sub>p a = ((P \<oplus>\<^sub>p a) \<triangleleft>(b \<oplus>\<^sub>p a)\<triangleright>(Q \<oplus>\<^sub>p a))"
  by (rel_auto)

lemma aext_seq [alpha]:
  "wb_lens a \<Longrightarrow> ((P ;; Q) \<oplus>\<^sub>p (a \<times>\<^sub>L a)) = ((P \<oplus>\<^sub>p (a \<times>\<^sub>L a)) ;; (Q \<oplus>\<^sub>p (a \<times>\<^sub>L a)))"
  by (rel_simp, metis wb_lens_weak weak_lens.put_get)
text {* We introduce the power syntax derived from semirings *}
  
subsection {* Algebraic Properties *}

interpretation upred_semiring: semiring_1
  where times = seqr and one = skip_r and zero = false\<^sub>h and plus = Lattices.sup
  by (unfold_locales, (rel_auto)+)


abbreviation upower :: "'\<alpha> hrel \<Rightarrow> nat \<Rightarrow> '\<alpha> hrel" (infixr "\<^bold>^" 100) where
"upower P n \<equiv> upred_semiring.power P n"

translations
  "P \<^bold>^ i" <= "CONST power.power II op ;; P i"
  "P \<^bold>^ i" <= "(CONST power.power II op ;; P) i"

text {* Set up transfer tactic for powers *}

lemma upower_rep_eq:
  "\<lbrakk>P \<^bold>^ i\<rbrakk>\<^sub>e = (\<lambda> b. b \<in> ({p. \<lbrakk>P\<rbrakk>\<^sub>e p} ^^ i))"
proof (induct i arbitrary: P)
  case 0
  then show ?case
    by (auto, rel_auto)
next
  case (Suc i)
  show ?case
    by (simp add: Suc seqr.rep_eq relpow_commute)
qed

lemma upower_rep_eq_alt:
  "\<lbrakk>power.power \<langle>id\<rangle>\<^sub>a op ;; P i\<rbrakk>\<^sub>e = (\<lambda>b. b \<in> ({p. \<lbrakk>P\<rbrakk>\<^sub>e p} ^^ i))"
  by (metis skip_r_def upower_rep_eq)

update_uexpr_rep_eq_thms
  
lemma Sup_power_expand:
  fixes P :: "nat \<Rightarrow> 'a::complete_lattice"
  shows "P(0) \<sqinter> (\<Sqinter>i. P(i+1)) = (\<Sqinter>i. P(i))"
proof -
  have "UNIV = insert (0::nat) {1..}"
    by auto
  moreover have "(\<Sqinter>i. P(i)) = \<Sqinter> (P ` UNIV)"
    by (blast)
  moreover have "\<Sqinter> (P ` insert 0 {1..}) = P(0) \<sqinter> SUPREMUM {1..} P"
    by (simp)
  moreover have "SUPREMUM {1..} P = (\<Sqinter>i. P(i+1))"
    by (simp add: atLeast_Suc_greaterThan)
  ultimately show ?thesis
    by (simp only:)
qed

lemma Sup_upto_Suc: "(\<Sqinter>i\<in>{0..Suc n}. P \<^bold>^ i) = (\<Sqinter>i\<in>{0..n}. P \<^bold>^ i) \<sqinter> P \<^bold>^ Suc n"
proof -
  have "(\<Sqinter>i\<in>{0..Suc n}. P \<^bold>^ i) = (\<Sqinter>i\<in>insert (Suc n) {0..n}. P \<^bold>^ i)"
    by (simp add: atLeast0_atMost_Suc)
  also have "... = P \<^bold>^ Suc n \<sqinter> (\<Sqinter>i\<in>{0..n}. P \<^bold>^ i)"
    by (simp)
  finally show ?thesis
    by (simp add: Lattices.sup_commute)
qed

text {* The following two proofs are adapted from the AFP entry 
  \href{https://www.isa-afp.org/entries/Kleene_Algebra.shtml}{Kleene Algebra}. 
  See also~\cite{Armstrong2012,Armstrong2015}. *}

lemma seqr_left_unit [simp]:
  "II ;; P = P"
  by rel_auto

lemma seqr_right_unit [simp]:
  "P ;; II = P"
  by rel_auto
    
lemma seqr_assoc: "P ;; (Q ;; R) = (P ;; Q) ;; R"
  by rel_auto

lemma seqr_assoc': "(P ;; Q) ;; R = P ;; (Q ;; R) "
  by rel_auto    
    
lemma upower_inductl: "Q \<sqsubseteq> (P ;; Q \<sqinter> R) \<Longrightarrow> Q \<sqsubseteq> P \<^bold>^ n ;; R"
proof (induct n)
  case 0
  then show ?case by (auto)
next
  case (Suc n)
  then show ?case
    by (auto, metis (no_types, hide_lams) dual_order.trans order_refl seqr_assoc seqr_mono)
qed

lemma upower_inductr:
  assumes "Q \<sqsubseteq> (R \<sqinter> Q ;; P)"
  shows "Q \<sqsubseteq> R ;; (P \<^bold>^ n)"
using assms proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have "R ;; P \<^bold>^ Suc n = (R ;; P \<^bold>^ n) ;; P"
    by (metis seqr_assoc upred_semiring.power_Suc2)
  also have "Q ;; P \<sqsubseteq> ..."
    using Suc.hyps assms seqr_mono by auto
  also have "Q \<sqsubseteq> ..."
    using assms by auto
  finally show ?case .
qed

lemma SUP_atLeastAtMost_first:
  fixes P :: "nat \<Rightarrow> 'a::complete_lattice"
  assumes "m \<le> n"
  shows "(\<Sqinter>i\<in>{m..n}. P(i)) = P(m) \<sqinter> (\<Sqinter>i\<in>{Suc m..n}. P(i))"
  by (metis SUP_insert assms atLeastAtMost_insertL)
    
lemma upower_seqr_iter: "P \<^bold>^ n = (;; Q : replicate n P \<bullet> Q)"
  by (induct n) simp_all
    
subsubsection {* Kleene Star *}

definition ustar :: "'\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("_\<^sup>\<star>" [999] 999) where
"P\<^sup>\<star> = (\<Sqinter>i\<in>{0..} \<bullet> P\<^bold>^i)"

lemma ustar_rep_eq:
  "\<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>e = (\<lambda>b. b \<in> ({p. \<lbrakk>P\<rbrakk>\<^sub>e p}\<^sup>*))"
  by (simp add: ustar_def, rel_auto, simp_all add: relpow_imp_rtrancl rtrancl_imp_relpow)

update_uexpr_rep_eq_thms
  
subsubsection {* Omega *}

definition uomega :: "'\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("_\<^sup>\<omega>" [999] 999) where
"P\<^sup>\<omega> = (\<mu> X \<bullet> P ;; X)"

subsection {* Relation Algebra Laws *}

theorem RA1: "(P ;; (Q ;; R)) = ((P ;; Q) ;; R)"
  using seqr_assoc by auto

theorem RA2: "(P ;; II) = P" "(II ;; P) = P"
  by simp_all

theorem RA3: "P\<^sup>-\<^sup>- = P"
  by simp

theorem RA4: "(P ;; Q)\<^sup>- = (Q\<^sup>- ;; P\<^sup>-)"
  by simp

theorem RA5: "(P \<or> Q)\<^sup>- = (P\<^sup>- \<or> Q\<^sup>-)"
  by (rel_auto)
    
named_theorems urel_comp  
  
lemma seqr_or_distl[urel_comp]:
  "((P \<or> Q) ;; R) = ((P ;; R) \<or> (Q ;; R))"
  by rel_auto
    
theorem RA6: "((P \<or> Q) ;; R) = (P;;R \<or> Q;;R)"
  using seqr_or_distl by blast

theorem RA7: "((P\<^sup>- ;; (\<not>(P ;; Q))) \<or> (\<not>Q)) = (\<not>Q)"
  by (rel_auto)

subsection {* Kleene Algebra Laws *}

theorem ustar_unfoldl: "P\<^sup>\<star> \<sqsubseteq> II \<sqinter> P;;P\<^sup>\<star>"
  by (rel_simp, simp add: rtrancl_into_trancl2 trancl_into_rtrancl)

theorem ustar_inductl:
  assumes "Q \<sqsubseteq> R" "Q \<sqsubseteq> P ;; Q"
  shows "Q \<sqsubseteq> P\<^sup>\<star> ;; R"
proof -
  have "P\<^sup>\<star> ;; R = (\<Sqinter> i. P \<^bold>^ i ;; R)"
    by (simp add: ustar_def UINF_as_Sup_collect' seq_SUP_distr)
  also have "Q \<sqsubseteq> ..."
    by (simp add: SUP_least assms upower_inductl)
  finally show ?thesis .
qed

theorem ustar_inductr:
  assumes "Q \<sqsubseteq> R" "Q \<sqsubseteq> Q ;; P"
  shows "Q \<sqsubseteq> R ;; P\<^sup>\<star>"
proof -
  have "R ;; P\<^sup>\<star> = (\<Sqinter> i. R ;; P \<^bold>^ i)"
    by (simp add: ustar_def UINF_as_Sup_collect' seq_SUP_distl)
  also have "Q \<sqsubseteq> ..."
    by (simp add: SUP_least assms upower_inductr)
  finally show ?thesis .
qed

lemma ustar_refines_nu: "(\<nu> X \<bullet> P ;; X \<sqinter> II) \<sqsubseteq> P\<^sup>\<star>"
  by (metis (no_types, lifting) lfp_greatest semilattice_sup_class.le_sup_iff 
      semilattice_sup_class.sup_idem upred_semiring.mult_2_right 
      upred_semiring.one_add_one ustar_inductl)

lemma ustar_as_nu: "P\<^sup>\<star> = (\<nu> X \<bullet> P ;; X \<sqinter> II)"
proof (rule antisym)
  show "(\<nu> X \<bullet> P ;; X \<sqinter> II) \<sqsubseteq> P\<^sup>\<star>"
    by (simp add: ustar_refines_nu)
  show "P\<^sup>\<star> \<sqsubseteq> (\<nu> X \<bullet> P ;; X \<sqinter> II)"
    by (metis lfp_lowerbound upred_semiring.add_commute ustar_unfoldl)
qed
  
subsection {* Omega Algebra Laws *}

lemma uomega_induct:
  "P ;; P\<^sup>\<omega> \<sqsubseteq> P\<^sup>\<omega>"
  by (simp add: uomega_def, metis eq_refl gfp_unfold monoI seqr_mono)


end
