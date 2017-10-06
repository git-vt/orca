section \<open>Algebraic laws of programming\<close>

text \<open>In this section we introduce the semantic rules related to the different
      statements of IMP. In the literature this also known as the algebraic laws of programming.
      In our framework we will use these rules in order to optimize a given program written in our
      language, and this before any deductive proof verification activity or formal testing.\<close>

theory Algebraic_laws_design
  imports Algebraic_laws_design_aux
begin


section {*Algebraic laws for designs*}

subsection Skip

text \<open>In this section we introduce the algebraic laws of programming related to the SKIP
      statement.\<close>

lemma true_left_zero_skip_cpaD[udes_comp]:
  "(SKIP\<^sub>D;; true) = (true)"
  by rel_auto

lemma true_liftD_left_zero_skipD[udes_comp]:
  "(SKIP\<^sub>D;; \<lceil>true\<rceil>\<^sub>D) = (\<lceil>true\<rceil>\<^sub>D)"
  by rel_auto

lemma false_liftD_left_zero_skipD[udes_comp]:
  "(SKIP\<^sub>D;; \<lceil>false\<rceil>\<^sub>D) = (\<lceil>false\<rceil>\<^sub>D)"
  by rel_auto

lemma skipD_left_unit_assignsD[udes_comp]:
  "(SKIP\<^sub>D;; \<langle>\<sigma>\<rangle>\<^sub>D) = (\<langle>\<sigma>\<rangle>\<^sub>D)"
  by rel_auto

lemma skipD_topD_left_zero[udes_comp]:
  "(SKIP\<^sub>D;; \<top>\<^sub>D) = (\<top>\<^sub>D)"
  by rel_auto

lemma skipDDupt_left_zero[udes_comp]:
  "($x;; SKIP\<^sub>D) = $x"
  by rel_auto

lemma skipD_bot_left_zero[udes_comp]:
  "(\<top>\<^sub>D;; SKIP\<^sub>D) = (\<top>\<^sub>D)"
  by rel_auto

lemma skip_d_alpha_eq:
  "SKIP\<^sub>D =  ($ok \<Rightarrow> ($ok\<acute> \<and> ($\<Sigma>\<^sub>D\<acute> =\<^sub>u $\<Sigma>\<^sub>D)))"
   by rel_simp

lemma simpl_pre_skip_d_post:
  "(\<lceil>b\<rceil>\<^sub>D\<^sub>< \<and> SKIP\<^sub>D =\<^sub>u $ok) = (SKIP\<^sub>D =\<^sub>u $ok \<and> \<lceil>b\<rceil>\<^sub>D\<^sub>>)"
  by rel_auto

lemma simpl_pre_skip_d_var:
  fixes x :: "(bool \<Longrightarrow> 'b des)"
  shows "($x \<and> SKIP\<^sub>D =\<^sub>u $ok) = (SKIP\<^sub>D =\<^sub>u $ok \<and> $x\<acute>)"
  by rel_auto

lemma skip_d_post_left_unit[udes_comp]:
  "(S \<turnstile> (SKIP\<^sub>D;; Q)) = (S \<turnstile> Q)"
  apply pred_simp
  apply rel_simp
  apply fastforce
done

subsection \<open>Assignment Laws\<close>
text \<open>In this section we introduce the algebraic laws of programming related to the assignment
      statement.\<close>

lemma [urel_cond]:
  "S \<turnstile> (\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<lceil>R\<rceil>\<^sub>D \<and> $b\<acute>);; (P \<triangleleft> \<not> $b \<triangleright> Q)) =
   S \<turnstile> (\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<lceil>R\<rceil>\<^sub>D \<and> $b\<acute>);; Q)"
  apply rel_simp
  apply fastforce
done

lemma [urel_cond]:
  "S \<turnstile> (\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<lceil>R\<rceil>\<^sub>D \<and> $b\<acute>);; (P \<triangleleft> $b \<triangleright> Q)) =
   S \<turnstile> (\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<lceil>R\<rceil>\<^sub>D \<and> $b\<acute>);; P)"
  apply pred_simp
  apply fastforce
done

lemma usubst_d_cancel [usubst]:
  assumes 1:"weak_lens v"
  shows "($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub>D\<^sub></$v\<rbrakk> = \<lceil>expr\<rceil>\<^sub>D\<^sub><"
  using 1
  by  rel_auto

lemma usubst_d_lift_cancel[usubst]:
  assumes 1:"weak_lens v"
  shows "\<lceil>($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub></$v\<rbrakk>\<rceil>\<^sub>D = \<lceil>expr\<rceil>\<^sub>D\<^sub><"
  using 1
  by  rel_auto

lemma assigns_d_id : "SKIP\<^sub>D = \<langle>id\<rangle>\<^sub>D"
  unfolding skip_d_def assigns_d_def
  by (rel_auto)
    
lemma assign_test[udes_comp]:
  assumes 1:"mwb_lens x"
  shows     "(x :=\<^sub>D \<guillemotleft>u\<guillemotright>;; x :=\<^sub>D \<guillemotleft>v\<guillemotright>) = (x :=\<^sub>D \<guillemotleft>v\<guillemotright>)"
  using 1
  by (simp add: usubst udes_comp)

lemma assign_d_left_comp_subst[udes_comp]:
  "(x :=\<^sub>D u;; (\<lceil>P\<rceil>\<^sub>D \<turnstile> \<lceil>Q\<rceil>\<^sub>D)) = (\<lceil>P\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>D \<turnstile> \<lceil>Q\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>D)"
  by rel_blast

lemma assign_d_twice[udes_comp]:
  assumes "mwb_lens x" and  "x \<sharp> f"
  shows "(x :=\<^sub>D e;; x :=\<^sub>D f) = (x :=\<^sub>D f)"
  using assms
  by (simp add: udes_comp usubst)

lemma assign_d_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x :=\<^sub>D e ;; y :=\<^sub>D f) = (y :=\<^sub>D f ;; x :=\<^sub>D e)"
  using assms
  by (simp add: udes_comp usubst usubst_upd_comm)

lemma assign_d_cond_d[udes_comp]: (*needs more laws to be automatic*)
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "(x :=\<^sub>D e ;; (bif\<^sub>D b then P\<^sub>1 \<turnstile> Q\<^sub>1 else P\<^sub>2 \<turnstile> Q\<^sub>2 eif)) =
         (bif\<^sub>D (b\<lbrakk>e/x\<rbrakk>) then (x :=\<^sub>D e;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (x :=\<^sub>D e ;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif)"
  apply (simp add: usubst udes_comp)
  apply rel_auto
done

lemma assign_d_uop1[udes_comp]:
  assumes 1: "mwb_lens v"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (uop F (&v))) = (v :=\<^sub>D (uop F e1))"
  by (simp add: usubst  udes_comp assms)

lemma assign_d_bop1[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (bop bp (&v) e2)) = (v :=\<^sub>D (bop bp e1 e2))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_bop2[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (bop bp e2 (&v))) = (v :=\<^sub>D (bop bp e2 e1))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_trop1[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (trop tp (&v) e2 e3)) =
         (v :=\<^sub>D (trop tp e1 e2 e3))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_trop2[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (trop tp e2 (&v) e3)) =
         (v :=\<^sub>D (trop tp e2 e1 e3))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_trop3[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (trop tp e2 e3 (&v))) =
         (v :=\<^sub>D (trop tp e2 e3 e1))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_qtop1[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (qtop tp (&v) e2 e3 e4)) =
         (v :=\<^sub>D (qtop tp e1 e2 e3 e4))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_qtop2[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (qtop tp e2 (&v) e3 e4)) =
         (v :=\<^sub>D (qtop tp e2 e1 e3 e4))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_qtop3[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (qtop tp e2 e3 (&v) e4)) =
         (v :=\<^sub>D (qtop tp e2 e3 e1 e4))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_qtop4[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (qtop tp e2 e3 e4 (&v))) =
         (v :=\<^sub>D (qtop tp e2 e3 e4 e1))"
  by (simp add: usubst udes_comp assms)

text \<open>In the sequel we define assignment laws proposed by Hoare\<close>

lemma assign_d_vwb_skip_d[udes_comp]:
  assumes 1: "vwb_lens v"
  shows "(v :=\<^sub>D &v) = SKIP\<^sub>D"
  by (simp add: assms usubst)

lemma assign_c_simultaneous:
  assumes  1: "vwb_lens var2"
  and      2: "var1 \<bowtie> var2"
  shows "var1, var2 :=\<^sub>D expr, &var2 = var1 :=\<^sub>D expr"
  by (simp add: assms usubst_upd_comm usubst)

lemma assign_d_seq[udes_comp]:
  assumes  1: "vwb_lens var2"
  shows"(var1 :=\<^sub>D expr);; (var2 :=\<^sub>D &var2) = (var1 :=\<^sub>D expr)"
  using assms by rel_blast
    
lemma assign_d_cond_d_uop[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v"
  shows "bif\<^sub>D uop F expr then (v :=\<^sub>D expr;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr ;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
          v :=\<^sub>D expr;; bif\<^sub>D uop F (&v) then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms
  by (simp add: assign_d_cond_d subst_uop usubst_cancel)  

lemma assign_d_cond_bop1[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif\<^sub>D bop bp expr exp2 then (v :=\<^sub>D expr;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
          v :=\<^sub>D expr;; bif\<^sub>D bop bp (&v) exp2 then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms
  by (simp add: assign_d_cond_d subst_bop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_d_cond_bop2[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif\<^sub>D bop bp exp2 expr then (v :=\<^sub>D expr;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
          v :=\<^sub>D expr;; bif\<^sub>D bop bp exp2 (&v) then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_bop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_cond_trop1[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif\<^sub>D trop bp expr exp2 exp3 then (v :=\<^sub>D expr;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
         v :=\<^sub>D expr;; bif\<^sub>D trop bp (&v) exp2 exp3 then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_trop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_cond_trop2[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif\<^sub>D trop bp exp2 expr exp3 then (v :=\<^sub>D expr;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
         v :=\<^sub>D expr;; bif\<^sub>D trop bp  exp2 (&v) exp3 then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_trop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_cond_trop3[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif\<^sub>D trop bp exp2 exp3 expr then (v :=\<^sub>D expr;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
         v :=\<^sub>D expr;; bif\<^sub>D trop bp exp2 exp3 (&v) then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_trop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_cond_qtop1[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif\<^sub>D qtop bp expr exp2 exp3 exp4 then (v :=\<^sub>D expr;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
         v :=\<^sub>D expr;; bif\<^sub>D qtop bp (&v) exp2 exp3 exp4 then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_qtop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_d_cond_qtop2[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4:"v \<sharp> exp4"
  shows "bif\<^sub>D qtop bp exp2 expr  exp3 exp4 then (v :=\<^sub>D expr;;(P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
         v :=\<^sub>D expr;; bif\<^sub>D qtop bp exp2 (&v) exp3 exp4 then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_qtop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_d_cond_qtop3[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif\<^sub>D qtop bp exp2 exp3 expr exp4 then (v :=\<^sub>D expr;;(P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
         v :=\<^sub>D expr;; bif\<^sub>D qtop bp exp2 exp3 (&v) exp4 then(P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_qtop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_d_cond_qtop4[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif\<^sub>D qtop bp exp2 exp3 exp4 expr then (v :=\<^sub>D expr;;(P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
         v :=\<^sub>D expr;; bif\<^sub>D qtop bp exp2  exp3 exp4 (&v) then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_qtop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_d_cond_If [udes_cond]:
  "(bif\<^sub>D bexp then (v :=\<^sub>D exp1) else (v :=\<^sub>D exp2) eif) =
   (v :=\<^sub>D (exp1 \<triangleleft> bexp \<triangleright> exp2))"
  by rel_auto

subsection \<open>While laws\<close>
text \<open>In this section we introduce the algebraic laws of programming related to the while
      statement.\<close>
  
theorem while_unfold:
  "while b do (P \<turnstile> Q) od = (bif\<^sub>D b then ((P \<turnstile> Q);; while b do (P \<turnstile> Q) od) else SKIP\<^sub>D eif)"
proof -
  have m:"mono (\<lambda>X. bif\<^sub>D b then ((P \<turnstile> Q) ;; X) else SKIP\<^sub>D eif)"
    by (auto intro: monoI seqr_mono cond_mono)
  have H: "(\<lambda>X. bif\<^sub>D b then ((P \<turnstile> Q) ;; X) else SKIP\<^sub>D eif) \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H" 
    apply pred_simp apply rel_simp apply smt done       
  have "(while b do (P \<turnstile> Q) od) = (\<mu>\<^sub>D X \<bullet> bif\<^sub>D b then ((P \<turnstile> Q) ;; X) else SKIP\<^sub>D eif)"
    by (simp add: While_lfp_des_def)
  also have "... = (bif\<^sub>D b then ((P \<turnstile> Q);; (\<mu>\<^sub>D X \<bullet> bif\<^sub>D b then ((P \<turnstile> Q) ;; X) else SKIP\<^sub>D eif)) else SKIP\<^sub>D eif)"
    using mono_Monotone_utp_order [OF m, of "\<H>\<^bsub>DES\<^esub>"] H
          design_theory_continuous.LFP_weak_unfold 
    by auto
  also have "... = (bif\<^sub>D b then ((P \<turnstile> Q);; while b do (P \<turnstile> Q) od) else SKIP\<^sub>D eif)"
    by (simp add: While_lfp_des_def)
  finally show ?thesis .
qed

theorem while_bot_true: "while true do (P \<turnstile> Q) od = (\<mu>\<^sub>D X \<bullet> ((P \<turnstile> Q);; X))"
  by (simp add: While_lfp_des_def alpha)
        
lemma while_false:
  shows "(while false do (P \<turnstile> Q) od) = SKIP\<^sub>D"
proof -
  have "(while false do (P \<turnstile> Q) od) = bif\<^sub>D false then ((P \<turnstile> Q) ;; while false do (P \<turnstile> Q) od) else SKIP\<^sub>D eif"
    using while_unfold[of _ P] by simp
  also have "... = SKIP\<^sub>D" by rel_blast
  finally show ?thesis .
qed

lemma while_inv_unfold:
  "(while b invr p do (P \<turnstile> Q) od) = 
   (bif\<^sub>D b then ((P \<turnstile> Q) ;; (while b invr p do (P \<turnstile> Q) od)) else SKIP\<^sub>D eif)"
  unfolding While_inv_des_def using while_unfold
  by auto

theorem while_top_unfold:
  "while\<^sup>\<top>\<^sup>D b do (P \<turnstile> Q) od = (bif\<^sub>D b then ((P \<turnstile> Q) ;; while\<^sup>\<top>\<^sup>D b do (P \<turnstile> Q) od) else SKIP\<^sub>D eif)"
proof -
  have m:"mono (\<lambda>X. bif\<^sub>D b then ((P \<turnstile> Q) ;; X) else SKIP\<^sub>D eif)"
    by (auto intro: monoI seqr_mono cond_mono)
  have H: "(\<lambda>X. bif\<^sub>D b then ((P \<turnstile> Q) ;; X) else SKIP\<^sub>D eif) \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H" 
    apply pred_simp apply rel_simp apply smt done     
  have "(while\<^sup>\<top>\<^sup>D b do (P \<turnstile> Q) od) = (\<nu>\<^sub>D X \<bullet> bif\<^sub>D b then ((P \<turnstile> Q);; X) else SKIP\<^sub>D eif)"
    by (simp add: While_gfp_des_def)
  also have "... = (bif\<^sub>D b then ((P \<turnstile> Q) ;; (\<nu>\<^sub>D X \<bullet> bif\<^sub>D b then ((P \<turnstile> Q) ;; X) else SKIP\<^sub>D eif)) else SKIP\<^sub>D eif)"
    using mono_Monotone_utp_order [OF m, of "\<H>\<^bsub>DES\<^esub>"] H
          design_theory_continuous.GFP_weak_unfold 
    by auto
  also have "... = (bif\<^sub>D b then ((P \<turnstile> Q);; while\<^sup>\<top>\<^sup>D b do (P \<turnstile> Q) od) else SKIP\<^sub>D eif)"
    by (simp add:While_gfp_des_def)
  finally show ?thesis .
qed

theorem while_bot_false: "while\<^sup>\<top>\<^sup>D false do (P \<turnstile> Q) od = SKIP\<^sub>D"
 proof -
  have "(while\<^sup>\<top>\<^sup>D false do (P \<turnstile> Q) od) = bif\<^sub>D false then ((P \<turnstile> Q) ;; while\<^sup>\<top>\<^sup>D false do (P \<turnstile> Q) od) else SKIP\<^sub>D eif"
    using while_top_unfold[of _ P] by simp
  also have "... = SKIP\<^sub>D" by rel_blast
  finally show ?thesis .
qed

(*lemma while_true:
  shows "(while true do (P\<turnstile>Q) od) = false"it should eq to \<top>\<^sub>D
  apply (simp add: While_lfp_des_def alpha)
   apply (rule antisym)
  apply (simp_all)
  apply (rule lfp_lowerbound)
  apply (simp)
  done*)

 
subsection \<open>assume laws\<close>

lemma assume_twice[udes_comp]: "(b\<^sup>\<top>\<^sup>D;; c\<^sup>\<top>\<^sup>D) = (b \<and> c)\<^sup>\<top>\<^sup>D"
  apply pred_simp
  apply auto
  apply (rel_simp)
  apply blast
    apply (rel_simp)
    apply blast
   apply (rel_simp)
   apply blast
  apply (rel_simp)
    apply blast
done

lemma assert_twice[udes_comp]: "(b\<^sub>\<bottom>\<^sub>D;; c\<^sub>\<bottom>\<^sub>D) = (b \<and> c)\<^sub>\<bottom>\<^sub>D"
 apply pred_simp
  apply auto
  apply (rel_simp)
  apply blast
    apply (rel_simp)
    apply blast
   apply (rel_simp)
   apply blast
  apply (rel_simp)
    apply blast
  done
    
subsection \<open>Try Catch laws\<close>
(*see utp_hoare_helper*)


end
