section \<open>Algebraic laws for abrupt designs\<close>

theory algebraic_laws_abrupt
  imports algebraic_laws_abrupt_aux
          "../Design/Algebraic_laws_design"
begin

(* TODO: add laws for assigns when composed with try catch... *)
subsection \<open>Simpset configuration\<close>
declare urel_comp [uabr_comp]
declare urel_cond [uabr_cond]

subsection Throw

lemma throw_abr_left_zero_true_abr[uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R;; true) = (true)"
  by rel_auto

lemma throw_abr_left_zero_true_lift_abr[uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R;; \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R) = (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma throw_abr_left_zero_false_lift_abr[uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R;; \<lceil>false\<rceil>\<^sub>A\<^sub>B\<^sub>R) = (\<lceil>false\<rceil>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma throw_abr_left_zero_skip_abr[uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R;; SKIP\<^sub>A\<^sub>B\<^sub>R) = (THROW\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma throw_abr_left_zero_assigns_abr[uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R;; \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R) = (THROW\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma throw_abr_left_unit_top_abr[uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R;; \<top>\<^sub>A\<^sub>B\<^sub>R) = (\<top>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma throw_abr_idem [uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R;; THROW\<^sub>A\<^sub>B\<^sub>R) = THROW\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto
 
lemma throw_abr_simpl_abr [uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R;; Simpl\<^sub>A\<^sub>B\<^sub>R P) = THROW\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto  
    
lemma not_abrupt_left_zero_throw_abr[uabr_comp]:
  "(($x);; THROW\<^sub>A\<^sub>B\<^sub>R) = ($x)"
  by rel_auto

lemma bot_left_zero_throw_abr[uabr_comp]:
  "(\<top>\<^sub>A\<^sub>B\<^sub>R;; THROW\<^sub>A\<^sub>B\<^sub>R) = (\<top>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto


lemma throw_abr_right_zero_skip_abr[uabr_comp]:
  "(SKIP\<^sub>A\<^sub>B\<^sub>R ;; THROW\<^sub>A\<^sub>B\<^sub>R) = THROW\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto

lemma assigns_abr_throw_abr_right[uabr_comp]:
  "\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R;; THROW\<^sub>A\<^sub>B\<^sub>R = Simpl\<^sub>A\<^sub>B\<^sub>R(\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger>($abrupt\<acute> \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R))"
  by rel_auto

subsection Skip

text \<open>In this section we introduce the algebraic laws of programming related to the SKIP
      statement.\<close>

lemma true_right_zero_skip_cpa_abr[uabr_comp]:
  "(SKIP\<^sub>A\<^sub>B\<^sub>R;; true) = (true)"
  by rel_auto

lemma true_lift_abr_right_zero_skip_abr[uabr_comp]:
  "(SKIP\<^sub>A\<^sub>B\<^sub>R;; \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R) = (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma false_lift_abr_right_zero_skip_abr[uabr_comp]:
  "(SKIP\<^sub>A\<^sub>B\<^sub>R;; \<lceil>false\<rceil>\<^sub>A\<^sub>B\<^sub>R) = (\<lceil>false\<rceil>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma skip_abr_left_unit_assigns_abr[uabr_comp]:
  "(SKIP\<^sub>A\<^sub>B\<^sub>R;; \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R) = (\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma top_abr_right_zero_skip_abr_[uabr_comp]:
  "(SKIP\<^sub>A\<^sub>B\<^sub>R;; \<top>\<^sub>A\<^sub>B\<^sub>R) = (\<top>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma skip_abr_abrupt_left_zero[uabr_comp]:
  "($x;; SKIP\<^sub>A\<^sub>B\<^sub>R) = $x"
  by rel_auto

lemma bot_left_zero_skip_abr[uabr_comp]:
  "(\<top>\<^sub>A\<^sub>B\<^sub>R;; SKIP\<^sub>A\<^sub>B\<^sub>R) = (\<top>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma skip_abr_idem [uabr_comp]:
  "(SKIP\<^sub>A\<^sub>B\<^sub>R;; SKIP\<^sub>A\<^sub>B\<^sub>R) = SKIP\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto

lemma skip_abr_alpha_eq:
  "SKIP\<^sub>A\<^sub>B\<^sub>R = Simpl\<^sub>A\<^sub>B\<^sub>R (\<not>$abrupt\<acute> \<and> ($\<Sigma>\<^sub>A\<^sub>B\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>A\<^sub>B\<^sub>R))"
  by (simp add: skip_lift_cpa_def skip_abr_def)

lemma simpl_pre_skip_abr_post:
  "(Simpl\<^sub>A\<^sub>B\<^sub>R \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<and> SKIP\<^sub>A\<^sub>B\<^sub>R) = (SKIP\<^sub>A\<^sub>B\<^sub>R \<and> Simpl\<^sub>A\<^sub>B\<^sub>R \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>>)"
  by rel_auto

lemma simpl_pre_skip_abr_var:
  fixes x :: "(bool \<Longrightarrow> 'b abr_des)"
  shows "(Simpl\<^sub>A\<^sub>B\<^sub>R $x \<and> SKIP\<^sub>A\<^sub>B\<^sub>R) = (SKIP\<^sub>A\<^sub>B\<^sub>R \<and> Simpl\<^sub>A\<^sub>B\<^sub>R $x\<acute>)"
  by rel_auto

lemma skip_abr_post_left_unit[uabr_comp]:
  "(S \<turnstile> (SKIP\<^sub>A\<^sub>B\<^sub>R;; Q)) = (S \<turnstile> Q)"
  apply pred_simp
  apply rel_simp
  apply fastforce
done

lemma simpl_post_left_unit[uabr_comp]:
  "(S \<turnstile> (Simpl\<^sub>A\<^sub>B\<^sub>R (\<not>$abrupt\<acute> \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R);; Q)) = (S \<turnstile> Q)"
  apply pred_simp
  apply rel_simp
  apply transfer
  apply auto
done

subsection \<open>Assignment Laws\<close>
text \<open>In this section we introduce the algebraic laws of programming related to the assignment
      statement.\<close>

lemma [urel_cond]:
  "S \<turnstile> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>R\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and> $abrupt\<acute>);; (P \<triangleleft> \<not> $abrupt \<triangleright> Q)) =
   S \<turnstile> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>R\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and> $abrupt\<acute>);; Q)"
  apply rel_simp
  apply fastforce
done

lemma [urel_cond]:
  "S \<turnstile> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>R\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and> $abrupt\<acute>);; (P \<triangleleft> $abrupt \<triangleright> Q)) =
   S \<turnstile> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>R\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and> $abrupt\<acute>);; P)"
  apply pred_simp
  apply fastforce
done

lemma not_abrupt_assigns_abr_L6_left_des[urel_cond]:
  "((S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; (P \<triangleleft> $abrupt \<triangleright> Q))) \<triangleleft> \<not> $abrupt \<triangleright> R) =
   ((S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; Q)) \<triangleleft> \<not> $abrupt \<triangleright> R)"
  unfolding assigns_abr_def
  apply pred_simp
  apply fastforce
done

lemma abrupt_assigns_abr_L6_left_des[urel_cond]:
  "((S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; (P \<triangleleft> \<not> $abrupt \<triangleright> Q))) \<triangleleft> $abrupt \<triangleright> R) =
   ((S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; Q)) \<triangleleft> $abrupt \<triangleright> R)"
  unfolding assigns_abr_def
  apply pred_simp
  apply rel_simp
  apply fastforce
done

lemma not_abrupt_assigns_abr_L6_right_des[urel_cond]:
  "(R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; (P \<triangleleft> $abrupt \<triangleright> Q)))) =
   (R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; P)))"
  unfolding assigns_abr_def
  apply pred_simp
  apply rel_simp
  apply fastforce
done

lemma abrupt_assigns_abr_L6_right_des[urel_cond]:
 "(R \<triangleleft> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; (P \<triangleleft> \<not> $abrupt \<triangleright> Q)))) =
  (R \<triangleleft> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; P)))"
  apply pred_simp
  apply rel_simp
  apply fastforce
done

lemma not_abrupt_left_assigns_abr_post_des[urel_cond]:
  "R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; P)) =
   R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> ((\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and> $abrupt\<acute>));; P))"
  unfolding assigns_abr_def
  apply pred_simp
  apply rel_simp 
done


lemma usubst_abr_cancel [usubst]:
  assumes 1:"weak_lens v"
  shows "($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub></$v\<rbrakk> = \<lceil>expr\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><"
  using 1
  by  rel_auto

lemma usubst_abr_lift_cancel[usubst]:
  assumes 1:"weak_lens v"
  shows "\<lceil>($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub></$v\<rbrakk>\<rceil>\<^sub>A\<^sub>B\<^sub>R = \<lceil>expr\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><"
  using 1
  by  rel_auto

lemma assigns_abr_id [uabr_simpl]: "SKIP\<^sub>A\<^sub>B\<^sub>R = \<langle>id\<rangle>\<^sub>A\<^sub>B\<^sub>R"
  unfolding skip_abr_def assigns_abr_def
  by (rel_auto)

lemma assign_test[uabr_comp]:
  assumes 1:"mwb_lens x"
  shows     "(x :=\<^sub>A\<^sub>B\<^sub>R \<guillemotleft>u\<guillemotright>;; x :=\<^sub>A\<^sub>B\<^sub>R \<guillemotleft>v\<guillemotright>) = (x :=\<^sub>A\<^sub>B\<^sub>R \<guillemotleft>v\<guillemotright>)"
  using 1
  by (simp add: usubst uabr_comp)

lemma assign_abr_left_comp_subst[uabr_comp]:
  "(x :=\<^sub>A\<^sub>B\<^sub>R u;; Simpl\<^sub>A\<^sub>B\<^sub>R(\<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> \<lceil>Q\<rceil>\<^sub>A\<^sub>B\<^sub>R)) = Simpl\<^sub>A\<^sub>B\<^sub>R(\<lceil>P\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> \<lceil>Q\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma assign_abr_twice[uabr_comp]:
  assumes "mwb_lens x" and  "x \<sharp> f"
  shows "(x :=\<^sub>A\<^sub>B\<^sub>R e;; x :=\<^sub>A\<^sub>B\<^sub>R f) = (x :=\<^sub>A\<^sub>B\<^sub>R f)"
  using assms
  by (simp add: uabr_comp usubst)

lemma assign_abr_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x :=\<^sub>A\<^sub>B\<^sub>R e;; y :=\<^sub>A\<^sub>B\<^sub>R f) = (y :=\<^sub>A\<^sub>B\<^sub>R f;; x :=\<^sub>A\<^sub>B\<^sub>R e)"
  using assms
  by (simp add: uabr_comp usubst usubst_upd_comm)

lemma assign_abr_cond_abr[uabr_comp]: (*needs more laws to be automatic*)
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "(x :=\<^sub>A\<^sub>B\<^sub>R e;; (bif\<^sub>A\<^sub>B\<^sub>R b then Simpl\<^sub>A\<^sub>B\<^sub>R P else Simpl\<^sub>A\<^sub>B\<^sub>R Q eif)) =
         (bif\<^sub>A\<^sub>B\<^sub>R (b\<lbrakk>e/x\<rbrakk>) then (x :=\<^sub>A\<^sub>B\<^sub>R e;; Simpl\<^sub>A\<^sub>B\<^sub>R P)  else (x :=\<^sub>A\<^sub>B\<^sub>R e;; Simpl\<^sub>A\<^sub>B\<^sub>R Q) eif)"
  by rel_auto

lemma assign_c_uop1[uabr_comp]:
  assumes 1: "mwb_lens v"
  shows "(v :=\<^sub>A\<^sub>B\<^sub>R e1;; v :=\<^sub>A\<^sub>B\<^sub>R (uop F (&v))) = (v :=\<^sub>A\<^sub>B\<^sub>R (uop F e1))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_bop1[uabr_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v :=\<^sub>A\<^sub>B\<^sub>R e1;; v :=\<^sub>A\<^sub>B\<^sub>R (bop bp (&v) e2)) = (v :=\<^sub>A\<^sub>B\<^sub>R (bop bp e1 e2))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_bop2[uabr_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v :=\<^sub>A\<^sub>B\<^sub>R e1;; v :=\<^sub>A\<^sub>B\<^sub>R (bop bp e2 (&v))) = (v :=\<^sub>A\<^sub>B\<^sub>R (bop bp e2 e1))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_trop1[uabr_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :=\<^sub>A\<^sub>B\<^sub>R e1;; v :=\<^sub>A\<^sub>B\<^sub>R (trop tp (&v) e2 e3)) =
         (v :=\<^sub>A\<^sub>B\<^sub>R (trop tp e1 e2 e3))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_trop2[uabr_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :=\<^sub>A\<^sub>B\<^sub>R e1;; v :=\<^sub>A\<^sub>B\<^sub>R (trop tp e2 (&v) e3)) =
         (v :=\<^sub>A\<^sub>B\<^sub>R (trop tp e2 e1 e3))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_trop3[uabr_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :=\<^sub>A\<^sub>B\<^sub>R e1;; v :=\<^sub>A\<^sub>B\<^sub>R (trop tp e2 e3 (&v))) =
         (v :=\<^sub>A\<^sub>B\<^sub>R (trop tp e2 e3 e1))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_qtop1[uabr_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :=\<^sub>A\<^sub>B\<^sub>R e1;; v :=\<^sub>A\<^sub>B\<^sub>R (qtop tp (&v) e2 e3 e4)) =
         (v :=\<^sub>A\<^sub>B\<^sub>R (qtop tp e1 e2 e3 e4))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_qtop2[uabr_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :=\<^sub>A\<^sub>B\<^sub>R e1;; v :=\<^sub>A\<^sub>B\<^sub>R (qtop tp e2 (&v) e3 e4)) =
         (v :=\<^sub>A\<^sub>B\<^sub>R (qtop tp e2 e1 e3 e4))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_qtop3[uabr_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :=\<^sub>A\<^sub>B\<^sub>R e1;; v :=\<^sub>A\<^sub>B\<^sub>R (qtop tp e2 e3 (&v) e4)) =
         (v :=\<^sub>A\<^sub>B\<^sub>R (qtop tp e2 e3 e1 e4))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_qtop4[uabr_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :=\<^sub>A\<^sub>B\<^sub>R e1;; v :=\<^sub>A\<^sub>B\<^sub>R (qtop tp e2 e3 e4 (&v))) =
         (v :=\<^sub>A\<^sub>B\<^sub>R (qtop tp e2 e3 e4 e1))"
  by (simp add: usubst uabr_comp assms)

text \<open>In the sequel we define assignment laws proposed by Hoare\<close>

lemma assign_abr_vwb_skip_abr[uabr_comp]:
  assumes 1: "vwb_lens v"
  shows "(v :=\<^sub>A\<^sub>B\<^sub>R &v) = SKIP\<^sub>A\<^sub>B\<^sub>R"
  by (simp add: assms usubst uabr_simpl)

lemma assign_c_simultaneous:
  assumes  1: "vwb_lens var2"
  and      2: "var1 \<bowtie> var2"
  shows "var1, var2 :=\<^sub>A\<^sub>B\<^sub>R expr, &var2 = var1 :=\<^sub>A\<^sub>B\<^sub>R expr"
  by (simp add: assms usubst_upd_comm usubst)

lemma assign_c_seq[uabr_comp]:
  assumes  1: "vwb_lens var2"
  shows"(var1 :=\<^sub>A\<^sub>B\<^sub>R expr);; (var2 :=\<^sub>A\<^sub>B\<^sub>R &var2) = (var1 :=\<^sub>A\<^sub>B\<^sub>R expr)"
  by (simp add: assms usubst uabr_comp)

lemma assign_c_cond_c_uop[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v"
  shows "bif\<^sub>A\<^sub>B\<^sub>R uop F expr then (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif =
          v :=\<^sub>A\<^sub>B\<^sub>R expr;; bif\<^sub>A\<^sub>B\<^sub>R uop F (&v) then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
   using assms
   unfolding assigns_abr_def
   apply (simp only: simpl_abr_comp_semir)
   apply  pred_simp
   apply rel_simp
   done
     
lemma assign_c_cond_bop1[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif\<^sub>A\<^sub>B\<^sub>R bop bp expr exp2 then (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif =
          v :=\<^sub>A\<^sub>B\<^sub>R expr;; bif\<^sub>A\<^sub>B\<^sub>R bop bp (&v) exp2 then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  using assms
  unfolding assigns_abr_def
  apply (simp only: simpl_abr_comp_semir)
  apply  pred_simp
  apply rel_simp
  done

lemma assign_c_cond_bop2[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif\<^sub>A\<^sub>B\<^sub>R bop bp exp2 expr then (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif =
          v :=\<^sub>A\<^sub>B\<^sub>R expr;; bif\<^sub>A\<^sub>B\<^sub>R bop bp  exp2 (&v) then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  using assms
  unfolding assigns_abr_def
  apply (simp only: simpl_abr_comp_semir)
  apply  pred_simp
  apply rel_simp
done

lemma assign_cond_trop1[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif\<^sub>A\<^sub>B\<^sub>R trop bp expr exp2 exp3 then (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif =
         v :=\<^sub>A\<^sub>B\<^sub>R expr;; bif\<^sub>A\<^sub>B\<^sub>R trop bp (&v) exp2 exp3 then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  using assms
  unfolding assigns_abr_def
  apply (simp only: simpl_abr_comp_semir)
  apply  pred_simp
  apply rel_simp
done

lemma assign_cond_trop2[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif\<^sub>A\<^sub>B\<^sub>R trop bp exp2 expr exp3 then (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif =
         v :=\<^sub>A\<^sub>B\<^sub>R expr;; bif\<^sub>A\<^sub>B\<^sub>R trop bp  exp2 (&v) exp3 then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  using assms
  unfolding assigns_abr_def
  apply (simp only: simpl_abr_comp_semir)
  apply  pred_simp
  apply rel_simp
done

lemma assign_cond_trop3[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif\<^sub>A\<^sub>B\<^sub>R trop bp exp2 exp3 expr then (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif =
         v :=\<^sub>A\<^sub>B\<^sub>R expr;; bif\<^sub>A\<^sub>B\<^sub>R trop bp exp2 exp3 (&v) then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  using assms
  unfolding assigns_abr_def
  apply (simp only: simpl_abr_comp_semir)
  apply  pred_simp
  apply rel_simp
done

lemma assign_cond_qtop1[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif\<^sub>A\<^sub>B\<^sub>R qtop bp expr exp2 exp3 exp4 then (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif =
         v :=\<^sub>A\<^sub>B\<^sub>R expr;; bif\<^sub>A\<^sub>B\<^sub>R qtop bp (&v) exp2 exp3 exp4 then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  using assms
  unfolding assigns_abr_def
  apply (simp only: simpl_abr_comp_semir)
  apply  pred_simp
  apply rel_simp
done

lemma assign_c_cond_qtop2[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4:"v \<sharp> exp4"
  shows "bif\<^sub>A\<^sub>B\<^sub>R qtop bp exp2 expr  exp3 exp4 then (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif =
         v :=\<^sub>A\<^sub>B\<^sub>R expr;; bif\<^sub>A\<^sub>B\<^sub>R qtop bp exp2 (&v) exp3 exp4 then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  using assms
  unfolding assigns_abr_def
  apply (simp only: simpl_abr_comp_semir)
  apply  pred_simp
  apply rel_simp
done

lemma assign_c_cond_qtop3[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif\<^sub>A\<^sub>B\<^sub>R qtop bp exp2 exp3 expr exp4 then (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif =
         v :=\<^sub>A\<^sub>B\<^sub>R expr;; bif\<^sub>A\<^sub>B\<^sub>R qtop bp exp2 exp3 (&v) exp4 then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  using assms
  unfolding assigns_abr_def
  apply (simp only: simpl_abr_comp_semir)
  apply  pred_simp
  apply rel_simp
done

lemma assign_c_cond_qtop4[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif\<^sub>A\<^sub>B\<^sub>R qtop bp exp2 exp3 exp4 expr then (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v :=\<^sub>A\<^sub>B\<^sub>R expr;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif =
         v :=\<^sub>A\<^sub>B\<^sub>R expr;; bif\<^sub>A\<^sub>B\<^sub>R qtop bp exp2  exp3 exp4 (&v) then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  using assms
  unfolding assigns_abr_def
  apply (simp only: simpl_abr_comp_semir)
  apply  pred_simp
  apply rel_simp
done

lemma assigns_abr_cond_abr [uabr_cond]:
  "(bif\<^sub>A\<^sub>B\<^sub>R bexp then (v :=\<^sub>A\<^sub>B\<^sub>R exp1) else (v :=\<^sub>A\<^sub>B\<^sub>R exp2) eif) =
   (v :=\<^sub>A\<^sub>B\<^sub>R (exp1 \<triangleleft> bexp \<triangleright> exp2))"
  by rel_auto


subsection \<open>While laws for designs\<close>
  
text \<open>In this section we introduce the algebraic laws of programming related to the while
      statement.\<close>
lemma "mono (\<lambda>X. bif\<^sub>A\<^sub>B\<^sub>R b then (B ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"
  apply (rule monoI)
  apply (rule cond_mono)
     apply (rule cond_mono)
theorem while_abr_des_unfold_gen:
  assumes HB: "B is H1"
  shows "while\<^sub>D\<^sub>A\<^sub>B\<^sub>R b do B od = (bif\<^sub>A\<^sub>B\<^sub>R b then (B;;while\<^sub>D\<^sub>A\<^sub>B\<^sub>R b do B od) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"
proof -
  have m:"mono (\<lambda>X. bif\<^sub>A\<^sub>B\<^sub>R b then (B ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"
      apply (simp only: cond_mono)

    by (auto intro: monoI seqr_mono cond_mono)
  have H: "(\<lambda>X. bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif) \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    using HB
    apply pred_simp apply rel_simp apply smt done       
  have "(while\<^sub>D b do B od) = (\<mu>\<^sub>D X \<bullet> bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)"
    by (simp add: While_lfp_des_def)
  also have "... = (bif\<^sub>D b then (B;; (\<mu>\<^sub>D X \<bullet> bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)) else SKIP\<^sub>D eif)"
    using mono_Monotone_utp_order [OF m, of "\<H>\<^bsub>DES\<^esub>"] H
          design_theory_continuous.LFP_weak_unfold 
    by auto
  also have "... = (bif\<^sub>D b then (B;; while\<^sub>D b do B od) else SKIP\<^sub>D eif)"
    by (simp add: While_lfp_des_def)
  finally show ?thesis .
qed
     
lemma while_inv_des_unfold:
   assumes HB: "B is H1"
  shows "(while\<^sub>D b invr p  do B od) = 
   (bif\<^sub>D b then (B ;; (while\<^sub>D b invr p  do B od)) else SKIP\<^sub>D eif)"
  unfolding While_inv_des_def using while_des_unfold_gen assms
  by auto

lemma while_inv_vrt_des_unfold:
   assumes HB: "B is H1"
  shows "(while\<^sub>D b invr p vrt e do B od) = 
   (bif\<^sub>D b then (B ;; (while\<^sub>D b invr p vrt e do B od)) else SKIP\<^sub>D eif)"
  unfolding While_inv_vrt_des_def using while_des_unfold_gen assms
  by auto
    
theorem while_bot_des_true: 
  "while\<^sub>D true do P od = (\<mu>\<^sub>D X \<bullet> (P ;; X))"
  by (simp add: While_lfp_des_def alpha)

lemma while_inv_des_true: 
  "while\<^sub>D true invr p do P od = (\<mu>\<^sub>D X \<bullet> (P ;; X))"
   unfolding While_inv_des_def using while_bot_des_true
   by auto    

lemma while_inv_vrt_des_true: 
  "while\<^sub>D true invr p vrt e do P od = (\<mu>\<^sub>D X \<bullet> (P ;; X))"
   unfolding While_inv_vrt_des_def using while_bot_des_true
   by auto 
     
lemma while_des_false:
  shows "(while\<^sub>D false do P od) = SKIP\<^sub>D"
  by (simp add: While_lfp_des_def alpha skip_d_def 
      design_theory_continuous.LFP_const rdesign_is_H1_H2)

lemma while_inv_des_false:
  shows "(while\<^sub>D false invr p do P od) = SKIP\<^sub>D"
   unfolding While_inv_des_def using while_des_false
   by auto  

lemma while_inv_vrt_des_false:
  shows "(while\<^sub>D false invr p vrt e do P od) = SKIP\<^sub>D"
   unfolding While_inv_vrt_des_def using while_des_false
   by auto  
        
theorem while_top_des_unfold_gen:
  assumes HB: "B is H1"
  shows
  "while\<^sup>\<top>\<^sup>D b do B od = (bif\<^sub>D b then (B ;; while\<^sup>\<top>\<^sup>D b do B od) else SKIP\<^sub>D eif)"
proof -
  have m:"mono (\<lambda>X. bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)"
    by (auto intro: monoI seqr_mono cond_mono)
  have H: "(\<lambda>X. bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif) \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"  
    using HB
    apply pred_simp apply rel_simp apply smt done     
  have "(while\<^sup>\<top>\<^sup>D b do B od) = (\<nu>\<^sub>D X \<bullet> bif\<^sub>D b then (B;; X) else SKIP\<^sub>D eif)"
    by (simp add: While_gfp_des_def)
  also have "... = (bif\<^sub>D b then (B ;; (\<nu>\<^sub>D X \<bullet> bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)) else SKIP\<^sub>D eif)"
    using mono_Monotone_utp_order [OF m, of "\<H>\<^bsub>DES\<^esub>"] H
          design_theory_continuous.GFP_weak_unfold 
    by auto
  also have "... = (bif\<^sub>D b then (B ;; while\<^sup>\<top>\<^sup>D b do B od) else SKIP\<^sub>D eif)"
    by (simp add:While_gfp_des_def)
  finally show ?thesis .
qed    
 
theorem while_top_des_false: 
  "while\<^sup>\<top>\<^sup>D false do P od = SKIP\<^sub>D"
 by (simp add: While_gfp_des_def alpha skip_d_def 
      design_theory_continuous.GFP_const rdesign_is_H1_H2)
    
(*lemma while_true:
  shows "(while true do (P\<turnstile>Q) od) = false"it should eq to \<top>\<^sub>D
  apply (simp add: While_lfp_des_def alpha)
   apply (rule antisym)
  apply (simp_all)
  apply (rule lfp_lowerbound)
  apply (simp)
  done*)

subsection \<open>While laws for normal designs\<close>
text \<open>In this section we introduce the algebraic laws of programming related to the while
      statement.\<close>
  
theorem while_bot_ndes_unfold_gen:
  assumes HB: "B is H1"
  shows
  "while\<^sub>N b do B od = (bif\<^sub>D b then (B;; while\<^sub>N b do B od) else SKIP\<^sub>D eif)"
proof -
  have m:"mono (\<lambda>X. bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)"
    by (auto intro: monoI seqr_mono cond_mono)
  have H: "(\<lambda>X. bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif) \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
    using HB apply pred_simp apply rel_simp apply smt done       
  have "(while\<^sub>N b do B od) = (\<mu>\<^sub>N X \<bullet> bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)"
    by (simp add: While_lfp_ndes_def)
  also have "... = (bif\<^sub>D b then (B ;; (\<mu>\<^sub>N X \<bullet> bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)) else SKIP\<^sub>D eif)"
    using mono_Monotone_utp_order [OF m, of "\<H>\<^bsub>NDES\<^esub>"] H
          normal_design_theory_continuous.LFP_weak_unfold 
    by auto
  also have "... = (bif\<^sub>D b then (B ;; while\<^sub>N b do B od) else SKIP\<^sub>D eif)"
    by (simp add: While_lfp_ndes_def)
  finally show ?thesis .
qed
    
lemma while_inv_ndes_unfold:
  assumes HB: "B is H1"
  shows
  "(while\<^sub>N b invr p  do B od) = 
   (bif\<^sub>D b then (B ;; (while\<^sub>N b invr p  do B od)) else SKIP\<^sub>D eif)"
  unfolding While_inv_ndes_def using while_bot_ndes_unfold_gen assms
  by auto  

lemma while_inv_vrt_ndes_unfold:
  assumes HB: "B is H1"
  shows
  "(while\<^sub>N b invr p vrt e do B od) = 
   (bif\<^sub>D b then (B ;; (while\<^sub>N b invr p vrt e do B od)) else SKIP\<^sub>D eif)"
  unfolding While_inv_vrt_ndes_def using while_bot_ndes_unfold_gen assms
  by auto 

theorem while_bot_ndes_true: "while\<^sub>N true do P od = (\<mu>\<^sub>N X \<bullet> (P;; X))"
  by (simp add: While_lfp_ndes_def alpha)
        
lemma while_inv_ndes_true:
  "(while\<^sub>N true invr p  do B od) = (\<mu>\<^sub>N X \<bullet> (B;; X))"
  unfolding While_inv_ndes_def using while_bot_ndes_true 
  by auto 

lemma while_inv_vrt_ndes_true:
  "(while\<^sub>N true invr p vrt e do B od) = (\<mu>\<^sub>N X \<bullet> (B;; X))"
  unfolding While_inv_vrt_ndes_def using while_bot_ndes_true 
  by auto
    
lemma while_ndes_false:
  shows "(while\<^sub>N false do P od) = SKIP\<^sub>D"
  by (simp add: While_lfp_ndes_def alpha skip_d_is_H1_H3  
      normal_design_theory_continuous.LFP_const)

lemma while_inv_ndes_false:
  "(while\<^sub>N false invr p  do B od) = SKIP\<^sub>D"
  unfolding While_inv_ndes_def using while_ndes_false 
  by auto  

lemma while_inv_vrt_ndes_false:
  "(while\<^sub>N false invr p vrt e do B od) = SKIP\<^sub>D"
  unfolding While_inv_vrt_ndes_def using while_ndes_false 
  by auto 
          
theorem while_top_ndes_unfold:
  assumes HB: "B is H1"
  shows
  "while\<^sup>\<top>\<^sup>N b do B od = (bif\<^sub>D b then (B ;; while\<^sup>\<top>\<^sup>N b do B od) else SKIP\<^sub>D eif)"
proof -
  have m:"mono (\<lambda>X. bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)"
    by (auto intro: monoI seqr_mono cond_mono)
  have H: "(\<lambda>X. bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif) \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H" 
    using HB
    apply pred_simp apply rel_simp apply smt done     
  have "(while\<^sup>\<top>\<^sup>N b do B od) = (\<nu>\<^sub>N X \<bullet> bif\<^sub>D b then (B;; X) else SKIP\<^sub>D eif)"
    by (simp add: While_gfp_ndes_def)
  also have "... = (bif\<^sub>D b then (B ;; (\<nu>\<^sub>N X \<bullet> bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)) else SKIP\<^sub>D eif)"
    using mono_Monotone_utp_order [OF m, of "\<H>\<^bsub>NDES\<^esub>"] H
          normal_design_theory_continuous.GFP_weak_unfold 
    by auto
  also have "... = (bif\<^sub>D b then (B ;; while\<^sup>\<top>\<^sup>N b do B od) else SKIP\<^sub>D eif)"
    by (simp add:While_gfp_ndes_def)
  finally show ?thesis .
qed

theorem while_bot_ndes_false: "while\<^sup>\<top>\<^sup>N false do B od = SKIP\<^sub>D"
 by (simp add: While_gfp_ndes_def alpha skip_d_is_H1_H3  
      normal_design_theory_continuous.GFP_const)
    
subsection \<open>assume laws\<close>

lemma assume_twice[uabr_comp]: "(b\<^sup>\<top>\<^sup>C;; c\<^sup>\<top>\<^sup>C) = (b \<and> c)\<^sup>\<top>\<^sup>C"
  apply pred_simp
  apply auto
  apply (rel_simp)+
  apply blast
  apply (rel_simp)+
  apply (metis (full_types))
done

lemma assert_twice[uabr_comp]: "(b\<^sub>\<bottom>\<^sub>C;; c\<^sub>\<bottom>\<^sub>C) = (b \<and> c)\<^sub>\<bottom>\<^sub>C"
  apply pred_simp
  apply auto
  apply (rel_simp)+
  apply blast
  apply (rel_simp)+
  apply (metis (full_types))
done

subsection \<open>Try Catch laws\<close>
(*see utp_hoare_helper*)


end
