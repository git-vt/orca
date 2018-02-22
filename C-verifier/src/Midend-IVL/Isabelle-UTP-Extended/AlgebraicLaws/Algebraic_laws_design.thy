(******************************************************************************
 * Orca: A Functional Correctness Verifier for Imperative Programs
 *       Based on Isabelle/UTP
 *
 * Copyright (c) 2016-2018 Virginia Tech, USA
 *               2016-2018 Technische Universität München, Germany
 *               2016-2018 University of York, UK
 *               2016-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * This software may be distributed and modified according to the terms of
 * the GNU Lesser General Public License version 3.0 or any later version.
 * Note that NO WARRANTY is provided.
 *
 * See CONTRIBUTORS, LICENSE and CITATION files for details.
 ******************************************************************************)

section \<open>Algebraic laws of programming\<close>

text \<open>In this section we introduce the semantic rules related to the different
      statements of IMP. In the literature this also known as the algebraic laws of programming.
      In our framework we will use these rules in order to optimize a given program written in our
      language, and this before any deductive proof verification activity or formal testing.\<close>

theory Algebraic_laws_design
  imports Algebraic_laws_design_aux
begin
  
section {*Algebraic laws for designs constructs*}

subsection Skip

text \<open>In this section we introduce the algebraic laws of programming related to the SKIP
      statement.\<close>

lemma skip_left_unit_design:
  fixes P :: "'a hrel_des"
  assumes "P is \<^bold>H"
  shows"(SKIP\<^sub>D ;; P) = P"
  by (simp add: H1_H2_impl_H1 H1_left_unit assms)   

lemmas skip_left_unit_ndesign = skip_left_unit_design[OF H1_H3_impl_H2]

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

lemma skipD_topD_right_zero[udes_comp]:
  "(SKIP\<^sub>D;; \<top>\<^sub>D) = (\<top>\<^sub>D)"
  by rel_auto

lemma skipD_uvar_left_zero[udes_comp]:
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

lemma skip_d_is_H1_H2:
  "SKIP\<^sub>D is \<^bold>H" 
  by rel_auto

lemma skip_d_post_left_unit[udes_comp]:
  "(S \<turnstile> (SKIP\<^sub>D;; Q)) = (S \<turnstile> Q)"
  apply pred_simp
  apply rel_simp
  apply fastforce
  done
    
lemma skip_refine_des:
  assumes "`(SKIP\<^sub>D \<Rightarrow> (p \<turnstile> q))`"
  shows " (p \<turnstile> q) \<sqsubseteq> SKIP\<^sub>D"
proof (rule refine_reverse_impl, goal_cases)
  case 1
  then show ?case using assms by pred_simp 
qed

lemma skip_d_left_unit:
  "P is H1 \<Longrightarrow> SKIP\<^sub>D ;; P = P"
  by rel_blast
    
subsection \<open>Assignment Laws\<close>
text \<open>In this section we introduce the algebraic laws of programming related to the assignment
      statement.\<close>

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

lemma assigns_d_id: 
  "SKIP\<^sub>D = \<langle>id\<rangle>\<^sub>D"
  unfolding skip_d_def assigns_d_def
  by (rel_auto)
    
lemma assign_design_test[udes_comp]:
  assumes 1:"mwb_lens x"
  shows     "(x :=\<^sub>D \<guillemotleft>u\<guillemotright>;; x :=\<^sub>D \<guillemotleft>v\<guillemotright>) = (x :=\<^sub>D \<guillemotleft>v\<guillemotright>)"
  using 1
  by (simp add: usubst udes_comp)

lemma assigns_d_left_comp_subst[udes_comp]:
  "(x :=\<^sub>D u;; (\<lceil>P\<rceil>\<^sub>D \<turnstile> \<lceil>Q\<rceil>\<^sub>D)) = (\<lceil>P\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>D \<turnstile> \<lceil>Q\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>D)"
  by rel_blast

lemma assigns_d_left_comp_subst_hdesigns[udes_comp]:
  assumes "P is \<^bold>H"
  shows "(x :=\<^sub>D u;; (P)) = (\<lceil>[x \<mapsto>\<^sub>s u]\<rceil>\<^sub>s\<^sub>D \<dagger> P)" (*fix the syntax sugar for substitution lifting*)
  using assms  
  by rel_blast
    
lemmas assigns_d_left_comp_subst_ndesigns[udes_comp] = 
  assigns_d_left_comp_subst_hdesigns[OF H1_H3_impl_H2] 

lemma assign_d_twice[udes_comp]:
  assumes "mwb_lens x" and  "x \<sharp> f"
  shows "(x :=\<^sub>D e;; x :=\<^sub>D f) = (x :=\<^sub>D f)"
  using assms
  by (simp add: udes_comp usubst)

lemma assigns_d_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x :=\<^sub>D e ;; y :=\<^sub>D f) = (y :=\<^sub>D f ;; x :=\<^sub>D e)"
  using assms
  by (simp add: udes_comp usubst usubst_upd_comm)

lemma assigns_d_left_cond_d_H1[udes_comp]: (*needs more laws to be automatic*)
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "P is H1" and "Q is H1"  
  shows "(x :=\<^sub>D e ;; (bif\<^sub>D b then P else Q eif)) =
         (bif\<^sub>D (b\<lbrakk>e/x\<rbrakk>) then (x :=\<^sub>D e;; P) else (x :=\<^sub>D e ;; Q) eif)"
  using assms  
  apply (simp add: usubst udes_comp)
  apply rel_simp
  apply smt
  done    
lemmas assigns_d_left_cond_d_hdesigns[udes_comp] = 
  assigns_d_left_cond_d_H1[OF H1_H2_impl_H1 H1_H2_impl_H1]

lemmas assigns_d_left_cond_d_ndesigns[udes_comp] = 
  assigns_d_left_cond_d_hdesigns[OF H1_H3_impl_H2 H1_H3_impl_H2]   
  
lemma assigns_d_uop1[udes_comp]:
  assumes 1: "mwb_lens v"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (uop F (&v))) = (v :=\<^sub>D (uop F e1))"
  by (simp add: usubst udes_comp assms)

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

lemma assign_d_simultaneous:
  assumes  1: "vwb_lens var2"
  and      2: "var1 \<bowtie> var2"
  shows "var1, var2 :=\<^sub>D expr, &var2 = var1 :=\<^sub>D expr"
  by (simp add: assms usubst_upd_comm usubst)

lemma assign_d_seq[udes_comp]:
  assumes  1: "vwb_lens var2"
  shows"(var1 :=\<^sub>D expr);; (var2 :=\<^sub>D &var2) = (var1 :=\<^sub>D expr)"
  using assms by rel_blast
    
lemma assign_d_cond_d_uop_H1[udes_comp]: (*needs more laws to be automatic*)
  assumes "P is H1" and "Q is H1" and 1: "weak_lens v"  
  shows "bif\<^sub>D uop F expr then (v :=\<^sub>D expr;; P) else (v :=\<^sub>D expr ;; Q) eif =
          v :=\<^sub>D expr;; bif\<^sub>D uop F (&v) then P else Q eif"
  using assms
  by (simp add: assigns_d_left_cond_d_H1 subst_uop usubst_cancel)
    
lemmas assign_d_cond_d_uop_hdesigns[udes_comp] = 
    assign_d_cond_d_uop_H1 [OF H1_H2_impl_H1 H1_H2_impl_H1]
    
lemmas assign_d_cond_d_uop_ndesigns [udes_comp] = 
  assign_d_cond_d_uop_hdesigns[OF H1_H3_impl_H2 H1_H3_impl_H2] 
  
lemma assign_d_cond_d_bop1_H1[udes_comp]: (*needs more laws to be automatic*)
  assumes "P is H1" and "Q is H1" and 1: "weak_lens v" and 2: "v \<sharp> exp2" 
  shows "bif\<^sub>D bop bp expr exp2 then (v :=\<^sub>D expr;; P) else (v :=\<^sub>D expr;; Q) eif =
          v :=\<^sub>D expr;; bif\<^sub>D bop bp (&v) exp2 then P else Q eif"
  using assms
  by (simp add: assigns_d_left_cond_d_H1 subst_bop subst_to_singleton(2) subst_unrest usubst_cancel)

lemmas assign_d_cond_d_bop1_hdesigns[udes_comp] =
  assign_d_cond_d_bop1_H1 [OF H1_H2_impl_H1 H1_H2_impl_H1] 
     
lemmas assign_d_cond_d_bop1_ndesigns[udes_comp] = 
  assign_d_cond_d_bop1_hdesigns [OF H1_H3_impl_H2 H1_H3_impl_H2] 
    
lemma assign_d_cond_d_bop2_H1[udes_comp]: (*needs more laws to be automatic*)
  assumes "P is H1" and "Q is H1" and 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif\<^sub>D bop bp exp2 expr then (v :=\<^sub>D expr;; P) else (v :=\<^sub>D expr;; Q) eif =
          v :=\<^sub>D expr;; bif\<^sub>D bop bp exp2 (&v) then P else Q eif"
  using assms  
  by (simp add: assigns_d_left_cond_d_H1 subst_bop subst_to_singleton(2) subst_unrest usubst_cancel)

lemmas assign_d_cond_d_bop2_hdesigns[udes_comp] =
  assign_d_cond_d_bop2_H1 [OF H1_H2_impl_H1 H1_H2_impl_H1]     
    
lemmas assign_d_cond_d_bop2_ndesigns[udes_comp] = 
  assign_d_cond_d_bop2_hdesigns [OF H1_H3_impl_H2 H1_H3_impl_H2] 

lemma assign_d_cond_d_trop1_H1[udes_comp]: (*needs more laws to be automatic*)
  assumes "P is H1" and "Q is H1" and 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif\<^sub>D trop bp expr exp2 exp3 then (v :=\<^sub>D expr;; P) else (v :=\<^sub>D expr;; Q) eif =
         v :=\<^sub>D expr;; bif\<^sub>D trop bp (&v) exp2 exp3 then P else Q eif"
  using assms  
  by (simp add: assigns_d_left_cond_d_H1 subst_trop subst_to_singleton(2) subst_unrest usubst_cancel)

lemmas assign_d_cond_d_trop1_hdesigns[udes_comp] =   
    assign_d_cond_d_trop1_H1 [OF H1_H2_impl_H1 H1_H2_impl_H1]
    
lemmas assign_d_cond_d_trop1_ndesigns[udes_comp] = 
  assign_d_cond_d_trop1_hdesigns [OF H1_H3_impl_H2 H1_H3_impl_H2]
  
lemma assign_d_cond_d_trop2_H1[udes_comp]: (*needs more laws to be automatic*)
  assumes "P is H1" and "Q is H1" and 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif\<^sub>D trop bp exp2 expr exp3 then (v :=\<^sub>D expr;; P) else (v :=\<^sub>D expr;; Q) eif =
         v :=\<^sub>D expr;; bif\<^sub>D trop bp  exp2 (&v) exp3 then P else Q eif"
  using assms  
  by (simp add: assigns_d_left_cond_d_H1 subst_trop subst_to_singleton(2) subst_unrest usubst_cancel)

lemmas assign_d_cond_d_trop2_hdesigns[udes_comp] =   
    assign_d_cond_d_trop2_H1 [OF H1_H2_impl_H1 H1_H2_impl_H1]
      
lemmas assign_d_cond_d_trop2_ndesigns[udes_comp] = 
  assign_d_cond_d_trop2_hdesigns [OF H1_H3_impl_H2 H1_H3_impl_H2]    

lemma assign_d_cond_d_trop3_H1[udes_comp]: (*needs more laws to be automatic*)
  assumes "P is H1" and "Q is H1" and 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif\<^sub>D trop bp exp2 exp3 expr then (v :=\<^sub>D expr;; P) else (v :=\<^sub>D expr;; Q) eif =
         v :=\<^sub>D expr;; bif\<^sub>D trop bp exp2 exp3 (&v) then P else Q eif"
  using assms  
  by (simp add: assigns_d_left_cond_d_H1 subst_trop subst_to_singleton(2) subst_unrest usubst_cancel)

lemmas assign_d_cond_d_trop3_hdesigns[udes_comp] =   
    assign_d_cond_d_trop3_H1 [OF H1_H2_impl_H1 H1_H2_impl_H1]
    
lemmas assign_d_cond_d_trop3_ndesigns[udes_comp] = 
  assign_d_cond_d_trop3_hdesigns [OF H1_H3_impl_H2 H1_H3_impl_H2]
  
lemma assign_d_cond_d_qtop1_H1[udes_comp]: (*needs more laws to be automatic*)
  assumes "P is H1" and "Q is H1" and 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif\<^sub>D qtop bp expr exp2 exp3 exp4 then (v :=\<^sub>D expr;; P) else (v :=\<^sub>D expr;; Q) eif =
         v :=\<^sub>D expr;; bif\<^sub>D qtop bp (&v) exp2 exp3 exp4 then P else Q eif"
  using assms  
  by (simp add: assigns_d_left_cond_d_H1 subst_qtop subst_to_singleton(2) subst_unrest usubst_cancel)

lemmas assign_d_cond_d_qtop1_hdesigns[udes_comp] =     
     assign_d_cond_d_qtop1_H1 [OF H1_H2_impl_H1 H1_H2_impl_H1]
     
lemmas assign_d_cond_d_qtop1_ndesigns[udes_comp] = 
  assign_d_cond_d_qtop1_hdesigns [OF H1_H3_impl_H2 H1_H3_impl_H2]
  
lemma assign_d_cond_d_qtop2_H1[udes_comp]: (*needs more laws to be automatic*)
  assumes "P is H1" and "Q is H1" and 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4:"v \<sharp> exp4"
  shows "bif\<^sub>D qtop bp exp2 expr  exp3 exp4 then (v :=\<^sub>D expr;;P) else (v :=\<^sub>D expr;; Q) eif =
         v :=\<^sub>D expr;; bif\<^sub>D qtop bp exp2 (&v) exp3 exp4 then P else Q eif"
  using assms  
  by (simp add: assigns_d_left_cond_d_H1 subst_qtop subst_to_singleton(2) subst_unrest usubst_cancel)

lemmas  assign_d_cond_d_qtop2_hdesigns[udes_comp] =     
  assign_d_cond_d_qtop2_H1[OF H1_H2_impl_H1 H1_H2_impl_H1]
  
lemmas assign_d_cond_d_qtop2_ndesigns[udes_comp] = 
  assign_d_cond_d_qtop2_hdesigns [OF H1_H3_impl_H2 H1_H3_impl_H2]
  
lemma assign_d_cond_d_qtop3_H1[udes_comp]: (*needs more laws to be automatic*)
  assumes "P is H1" and "Q is H1" and 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif\<^sub>D qtop bp exp2 exp3 expr exp4 then (v :=\<^sub>D expr;;P) else (v :=\<^sub>D expr;; Q) eif =
         v :=\<^sub>D expr;; bif\<^sub>D qtop bp exp2 exp3 (&v) exp4 then P else Q eif"
  using assms  
  by (simp add: assigns_d_left_cond_d_H1 subst_qtop subst_to_singleton(2) subst_unrest usubst_cancel)

lemmas  assign_d_cond_d_qtop3_hdesigns[udes_comp] =     
  assign_d_cond_d_qtop3_H1[OF H1_H2_impl_H1 H1_H2_impl_H1]
  
lemmas assign_d_cond_d_qtop3_ndesigns[udes_comp] = 
  assign_d_cond_d_qtop3_hdesigns [OF H1_H3_impl_H2 H1_H3_impl_H2]

lemma assign_d_cond_d_qtop4_H1[udes_comp]: (*needs more laws to be automatic*)
  assumes "P is H1" and "Q is H1" and 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif\<^sub>D qtop bp exp2 exp3 exp4 expr then (v :=\<^sub>D expr;; P) else (v :=\<^sub>D expr;; Q) eif =
         v :=\<^sub>D expr;; bif\<^sub>D qtop bp exp2  exp3 exp4 (&v) then P else Q eif"
  using assms  
  by (simp add: assigns_d_left_cond_d_H1 subst_qtop subst_to_singleton(2) subst_unrest usubst_cancel)

lemmas  assign_d_cond_d_qtop4_hdesigns[udes_comp] =     
  assign_d_cond_d_qtop4_H1[OF H1_H2_impl_H1 H1_H2_impl_H1]
  
lemmas assign_d_cond_d_qtop4_ndesigns[udes_comp] = 
  assign_d_cond_d_qtop4_hdesigns[OF H1_H3_impl_H2 H1_H3_impl_H2]
    
lemma assign_d_cond_d_If [udes_cond]:
  "(bif\<^sub>D bexp then (v :=\<^sub>D exp1) else (v :=\<^sub>D exp2) eif) =
   (v :=\<^sub>D (exp1 \<triangleleft> bexp \<triangleright> exp2))"
  by rel_auto

subsection \<open>Sequential composition laws for designs\<close>

lemma weaker_seq_r_H1_H2_closed[closure]:
  assumes "P is H1"  "Q is \<^bold>H"
  shows "(P ;; Q) is \<^bold>H"
proof -
  obtain Q\<^sub>1 Q\<^sub>2 where Q_def:"Q = Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2" and Q\<^sub>1_Q\<^sub>2_is_H1_H2:"Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2 is \<^bold>H"
    using assms(2) unfolding Healthy_def
   by (metis H1_H2_eq_rdesign )
   moreover have "(P ;; (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2)) is \<^bold>H"
   proof -
     have *:"H1 P = P" 
       using assms(1)[unfolded Healthy_def] .
     then show ?thesis using Q\<^sub>1_Q\<^sub>2_is_H1_H2 unfolding  Healthy_def H2_def 
       by (simp add: H1_rdesign H1_distrib_left_J H1_distrib_left_rdesign  seqr_assoc')
     qed 
  ultimately show ?thesis by simp
qed      
  
lemma weaker_seq_r_H1_H3_closed:
  assumes 1: "P is H1"
  assumes 2: "Q is \<^bold>N"
  shows      "(P;; Q) is \<^bold>N" 
proof -
 from 1 2 have 11:"\<lfloor>pre\<^sub>D Q\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D Q = Q"
    by (metis ndesign_form)
  then show ?thesis
    using 1 2 
  proof -
    have seq_r_H1_H2_closed_def: "\<forall>P Q. \<not> (P is H1) \<or> \<not> (Q is \<^bold>H) \<or> P ;; Q is (\<lambda>P. \<^bold>H P)"
      using weaker_seq_r_H1_H2_closed by fastforce
    have "\<forall>P. (P is \<^bold>N \<longrightarrow> P is \<^bold>H) = (\<not> (P is \<^bold>N) \<or> P is \<^bold>H)"
      by auto
    then have "\<forall>P. \<not> (P is \<^bold>N) \<or> P is \<^bold>H" 
      using H1_H3_impl_H2 by blast
    then have "Q is \<^bold>H" using 2
           by blast
    then have "P ;; Q is (\<lambda>P. \<^bold>H P)"
      using seq_r_H1_H2_closed_def 1 by blast 
    from this[THEN H1_H2_impl_H1] show ?thesis 
      using 11[simplified HOL.eq_commute] H3_ndesign[of "\<lfloor>pre\<^sub>D Q\<rfloor>\<^sub><" "post\<^sub>D Q"]
        unfolding Healthy_def H3_def 
        by (metis seqr_assoc)
  qed
qed

theorem H1_H3_eq_ndesign:
  assumes 1:"out\<alpha> \<sharp> pre\<^sub>D(P)"
  shows   "(\<^bold>N(P)) = (\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P))"
proof -
  from 1 have f2: "H3 P = H3 (H2 P)"
     by (metis H2_H3_absorb H2_H3_commute)
  have "\<^bold>H P = \<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D P"
    using 1 by (simp add: H1_H2_eq_rdesign ndesign_def)
  then show ?thesis
    using f2 by (simp add: H1_H3_commute H3_ndesign)
qed 
  
subsection \<open>Conditional laws for designs\<close> 
 
lemma if_d_true:
  "bif\<^sub>D true then P else Q eif = P"  
  by rel_simp
    
lemma if_d_false:
  "bif\<^sub>D false then P else Q eif = Q"  
  by rel_simp
    
lemma ifd_rdesign_pre_post:
  assumes P_is_H:"P is \<^bold>H"
  assumes Q_is_H:"Q is \<^bold>H"   
  shows   
   "bif\<^sub>D b then P else Q eif = 
    bif\<^sub>D b then (pre\<^sub>D P) \<turnstile>\<^sub>r post\<^sub>D P else (pre\<^sub>D Q) \<turnstile>\<^sub>r post\<^sub>D Q eif" 
proof -
 show ?thesis     
  using rdesign_split P_is_H Q_is_H 
  by metis    
qed

theorem rdesign_dcond:
  "bif\<^sub>D b then (P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2) else (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2) eif = (P\<^sub>1 \<triangleleft> b \<triangleright>\<^sub>r Q\<^sub>1) \<turnstile>\<^sub>r (P\<^sub>2 \<triangleleft> b \<triangleright>\<^sub>r Q\<^sub>2)"
  by (rel_auto)   
 
lemma  if_d_H1_H2_intro:   
  assumes P_is_H: "P is \<^bold>H" 
  assumes Q_is_H:"Q is \<^bold>H"  
  shows "bif\<^sub>D b then P else Q eif is \<^bold>H"
  apply (subst rdesign_form [OF P_is_H, THEN  HOL.sym])  
  apply (subst rdesign_form [OF Q_is_H, THEN  HOL.sym]) 
  apply (simp add: rdesign_dcond rdesign_is_H1_H2)
  done
    
lemma  if_d_H1_H3_intro: 
  assumes unrest_1: " out\<alpha> \<sharp> pre\<^sub>D P"
  assumes unrest_2: "out\<alpha> \<sharp> pre\<^sub>D Q"  
  assumes P_is_H: "P is \<^bold>H" 
  assumes Q_is_H:"Q is \<^bold>H"  
  shows "bif\<^sub>D b then P else Q eif is \<^bold>N"  
  apply (subst H1_H3_intro[OF P_is_H unrest_1, THEN ndesign_form, THEN HOL.sym])  
  apply (subst H1_H3_intro[OF Q_is_H unrest_2, THEN ndesign_form, THEN HOL.sym])  
  apply (simp add: ndesign_H1_H3 ndesign_dcond)
  done  

lemma stronger_if_d_seq_r_H1_H2_closed:
  assumes 1: "P is H1"
  and     2: "Q is \<^bold>H"
  shows "(\<lambda>X. bif\<^sub>D b then P ;; X else Q eif) \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"   
proof (rule  FuncSet.Pi_I)
  fix x :: "('b, 'a) rel_des"
  assume 11: "x \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"      
  have H2_seq_idemp: "(P ;; x::'a hrel_des) = H2 (P ;; x)"
    using weaker_seq_r_H1_H2_closed[OF 1 11[THEN Set.CollectD]] rdesign_split 
    by (metis (no_types) H2_rdesign)  
  have "Q = H2 Q"
    using rdesign_split 2 by (metis (no_types) H2_rdesign)
  then show "bif\<^sub>D b then P ;; x else Q eif \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    using weaker_seq_r_H1_H2_closed[OF 1 11[THEN Set.CollectD]] 2
      by (simp add: if_d_H1_H2_intro rdesign_is_H1_H2) 
qed  
  
lemma stronger_if_d_seq_r_H1_H3_closed:
  assumes 1: "P is H1"
  and     2: "Q is \<^bold>N"
  shows "(\<lambda>X. bif\<^sub>D b then P ;; X else Q eif) \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"   
proof (rule  FuncSet.Pi_I)
  fix x :: "('b, 'a) rel_des"
  assume 11: "x \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  have H3_seq_idemp: "(P ;; x::'a hrel_des) = H3 (P ;; x)"
    using weaker_seq_r_H1_H3_closed[OF 1 11[THEN Set.CollectD]] ndesign_split 
    by (metis (no_types) H3_ndesign)  
  have "Q = H3 Q"
    using ndesign_split 2 by (metis (no_types) H3_ndesign)
  then show "bif\<^sub>D b then P ;; x else Q eif \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
    apply (subst weaker_seq_r_H1_H3_closed[OF 1 11[THEN Set.CollectD], THEN ndesign_form, THEN  HOL.sym])
    apply (subst 2[THEN ndesign_form, THEN  HOL.sym])  
    apply (simp add: ndesign_H1_H3 ndesign_dcond)
    done                       
qed 

lemma if_d_skip_d_not_ok:
  "bif\<^sub>D true then SKIP\<^sub>D ;; (\<not> $ok) else SKIP\<^sub>D eif = (\<not> $ok)"
  by (simp add: aext_true des_top_ndes_def ndesign_def)
    
lemma if_d_skip_d_true:
  "bif\<^sub>D true then SKIP\<^sub>D ;; true else SKIP\<^sub>D eif = true"
  by rel_simp

lemma if_d_H4_true:
  assumes "body is H4"
  shows "bif\<^sub>D true then body ;; true else SKIP\<^sub>D eif = true"
  using assms by rel_auto
   
lemma if_d_mono:
  "mono (\<lambda>X. bif\<^sub>D b then P ;; X else Q eif)"
  by (auto intro: monoI seqr_mono cond_mono) 
  
subsection \<open>Recursion laws for designs\<close>  

lemma H1_H3_mu_refine_intro:
  assumes 1:"P is \<^bold>N"
  assumes 2:"P \<sqsubseteq> F P"
  assumes 3:"out\<alpha> \<sharp> pre\<^sub>D(P)"  
  assumes 4:"`\<lceil>\<lfloor>pre\<^sub>D(P:: 'a hrel_des)\<rfloor>\<^sub><\<rceil>\<^sub>D\<^sub><  \<Rightarrow> (\<mu>\<^sub>N F \<Leftrightarrow> \<nu>\<^sub>N F)`"  
  shows   "P \<sqsubseteq> \<mu>\<^sub>N F"
proof -
  from 3 H1_H3_eq_ndesign[of P]
  have is_H1_H3_eq_ndesign:
    "\<^bold>N P = \<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D P"  
    by simp 
  also have pre_post_ndesign_mu_refine:"\<dots> \<sqsubseteq> \<mu>\<^sub>N F"    
  proof - 
    have 1:"\<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D P \<sqsubseteq> F (\<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D P)"
      using 1 2 ndesign_form[of P]
      by simp
    also have "`\<lceil>\<lfloor>pre\<^sub>D P\<rfloor>\<^sub><\<rceil>\<^sub>D\<^sub>< \<Rightarrow> \<mu>\<^sub>N F \<Leftrightarrow> \<nu>\<^sub>N F`"
      using 4 by simp
    from assms have "(\<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D P) \<sqsubseteq> \<nu>\<^sub>N F"
      by (simp add: 1 ndesign_H1_H3 normal_design_theory_continuous.GFP_upperbound)  
    with assms show ?thesis
      by (rel_auto, metis (no_types, lifting))
  qed       
  ultimately show ?thesis 
    by (simp add: "1" ndes_elim)  
qed
  
lemma ndesign_mu_refine_intro:
  assumes "(C \<turnstile>\<^sub>n S) \<sqsubseteq> F(C \<turnstile>\<^sub>n S)" "`\<lceil>C\<rceil>\<^sub>D\<^sub>< \<Rightarrow> (\<mu>\<^sub>N F \<Leftrightarrow> \<nu>\<^sub>N F)`"
  shows "(C \<turnstile>\<^sub>n S) \<sqsubseteq> \<mu>\<^sub>N F"
proof (rule H1_H3_mu_refine_intro, goal_cases)
  case 1
  then show ?case by (simp add: ndesign_H1_H3)
next
  case 2
  then show ?case by (simp add: assms(1))
next
  case 3
  then show ?case by (simp add: unrest_pre_out\<alpha>)
next
  case 4
  then show ?case by (simp add: assms(2))
qed  
  
subsection \<open>While laws for designs\<close>
  
text \<open>In this section we introduce the algebraic laws of programming related to the while
      statement.\<close>
 
lemma while_gfp_des_def_alt:
"(while\<^sup>\<top>\<^sup>D b do body od) = (\<nu>\<^sub>D X \<bullet> bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif)"
    unfolding from_until_gfp_des_def while_gfp_des_def 
    by (simp add: skip_left_unit_design)
      
lemma while_lfp_des_def_alt:
"(while\<^sub>\<bottom>\<^sub>D b do body od) = (\<mu>\<^sub>D X \<bullet> bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif)"
    unfolding from_until_lfp_des_def while_lfp_des_def 
    by (simp add: skip_left_unit_design)
       
theorem while_gfp_des_unfold:
  assumes HB: "body is H1"
  shows
  "while\<^sup>\<top>\<^sup>D b do body od = (bif\<^sub>D b then (body ;; while\<^sup>\<top>\<^sup>D b do body od) else SKIP\<^sub>D eif)"
proof -
  have m:"mono (\<lambda>X. bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif)"
    by (auto intro: monoI seqr_mono cond_mono)
  have H: "(\<lambda>X. bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif) \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"  
   by (rule stronger_if_d_seq_r_H1_H2_closed[OF HB skip_d_is_H1_H2])    
  have "(while\<^sup>\<top>\<^sup>D b do body od) = (\<nu>\<^sub>D X \<bullet> bif\<^sub>D b then (body;; X) else SKIP\<^sub>D eif)"
    by (simp add: while_gfp_des_def_alt)
  also have "... = (bif\<^sub>D b then (body ;; (\<nu>\<^sub>D X \<bullet> bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif)) else SKIP\<^sub>D eif)"
    using mono_Monotone_utp_order [OF m, of "\<H>\<^bsub>DES\<^esub>"] H
          design_theory_continuous.GFP_weak_unfold 
    by auto
  also have "... = (bif\<^sub>D b then (body ;; while\<^sup>\<top>\<^sup>D b do body od) else SKIP\<^sub>D eif)"
    by (simp add:while_gfp_des_def_alt)
  finally show ?thesis .
qed    

theorem while_lfp_des_unfold:
  assumes HB: "body is H1"
  shows "while\<^sub>\<bottom>\<^sub>D b do body od = (bif\<^sub>D b then (body;; while\<^sub>\<bottom>\<^sub>D b do body od) else SKIP\<^sub>D eif)"
proof -
  have m:"mono (\<lambda>X. bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif)"
    by (auto intro: monoI seqr_mono cond_mono)
  have H: "(\<lambda>X. bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif) \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    by (rule stronger_if_d_seq_r_H1_H2_closed[OF HB skip_d_is_H1_H2])     
  have "(while\<^sub>\<bottom>\<^sub>D b do body od) = (\<mu>\<^sub>D X \<bullet> bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif)"
    unfolding from_until_lfp_des_def 
    by (simp add: while_lfp_des_def_alt skip_left_unit_design)
  also have "... = (bif\<^sub>D b then (body;; (\<mu>\<^sub>D X \<bullet> bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif)) else SKIP\<^sub>D eif)"
    using mono_Monotone_utp_order [OF m, of "\<H>\<^bsub>DES\<^esub>"] H
          design_theory_continuous.LFP_weak_unfold 
    by auto
  also have "... = (bif\<^sub>D b then (body;; while\<^sub>\<bottom>\<^sub>D b do body od) else SKIP\<^sub>D eif)"
    by (simp add: while_lfp_des_def_alt)
  finally show ?thesis .
qed
    
theorem while_lfp_des_true: 
  "while\<^sub>\<bottom>\<^sub>D true do body od = (\<mu>\<^sub>D X \<bullet> (body ;; X))"
  by (simp add: while_lfp_des_def_alt alpha)      

lemma while_lfp_des_false:
  shows "(while\<^sub>\<bottom>\<^sub>D false do body od) = SKIP\<^sub>D"
  by (simp add: while_lfp_des_def_alt alpha skip_d_def 
      design_theory_continuous.LFP_const rdesign_is_H1_H2)
         
theorem while_gfp_des_false: 
  "while\<^sup>\<top>\<^sup>D false do body od = SKIP\<^sub>D"
 by (simp add: while_gfp_des_def_alt alpha skip_d_def 
      design_theory_continuous.GFP_const rdesign_is_H1_H2)

theorem while_gfp_des_non_termination: (*because of this lemma and the lemma utp_designs.design_top we do not use gfp for capturing termination *)
  "while\<^sup>\<top>\<^sup>D true do SKIP\<^sub>D od = \<top>\<^sub>D"
  unfolding while_gfp_des_def_alt
proof (rule design_theory_continuous.weak.GFP_idem [of "(\<lambda>X. bif\<^sub>D true then SKIP\<^sub>D ;; X else SKIP\<^sub>D eif)",
      unfolded utp_theory_des_top_is_not_ok if_d_skip_d_not_ok] , goal_cases)
  case 1
  then show ?case by (simp add: H1_H2_impl_H1 if_d_H1_H2_intro skip_d_is_H1_H2 weaker_seq_r_H1_H2_closed)
next
  case 2
  then show ?case by (simp add: aext_true seqr_mono utp_theory.Mono_utp_orderI)
next
  case 3
  then show ?case  unfolding idempotent_def by (simp add: aext_true seqr_assoc)                       
qed

theorem while_lfp_des_non_termination: 
  "while\<^sub>\<bottom>\<^sub>D true do  SKIP\<^sub>D od = \<bottom>\<^sub>D"
  unfolding while_lfp_des_def_alt
proof (rule design_theory_continuous.weak.LFP_idem [of "(\<lambda>X. bif\<^sub>D true then SKIP\<^sub>D ;; X else SKIP\<^sub>D eif)",
      unfolded utp_theory_des_bot_is_true if_d_skip_d_true] , goal_cases)
  case 1
  then show ?case by (simp add: H1_H2_impl_H1 if_d_H1_H2_intro skip_d_is_H1_H2 weaker_seq_r_H1_H2_closed)
next
  case 2
  then show ?case by (simp add: aext_true seqr_mono utp_theory.Mono_utp_orderI)
next
  case 3
  then show ?case  unfolding idempotent_def by (simp add: aext_true seqr_assoc)                       
qed  

      
subsection \<open>While laws for normal designs\<close>

text \<open>In this section we introduce the algebraic laws of programming related to the while
      statement.\<close>
    
lemma while_gfp_ndes_def_alt:
"(while\<^sup>\<top>\<^sup>N b do body od) = (\<nu>\<^sub>N X \<bullet> bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif)"
    unfolding from_until_gfp_ndes_def while_gfp_ndes_def 
    by (simp add: skip_left_unit_ndesign)
    
lemma while_lfp_ndes_def_alt:
"(while\<^sub>\<bottom>\<^sub>N b do body od) = (\<mu>\<^sub>N X \<bullet> bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif)"
    unfolding from_until_lfp_ndes_def while_lfp_ndes_def 
    by (simp add: skip_left_unit_ndesign)
 
lemma while_gfp_ndes_is_H1_H3: 
  "while\<^sup>\<top>\<^sup>N b do body od is \<^bold>N"  
  unfolding while_gfp_ndes_def_alt
  by simp 
    
lemma while_lfp_ndes_is_H1_H3: 
  "while\<^sub>\<bottom>\<^sub>N b do body od is \<^bold>N"  
  unfolding while_lfp_ndes_def_alt
  by simp 
    
lemma while_gfp_ndes_is_H1_H2: 
  "while\<^sup>\<top>\<^sup>D b do body od is \<^bold>H"  
  unfolding while_gfp_des_def_alt
  by simp  
    
lemma while_lfp_ndes_is_H1_H2: 
  "while\<^sub>\<bottom>\<^sub>D b do body od is \<^bold>H"  
  unfolding while_lfp_des_def_alt
  by simp  
    
theorem while_gfp_ndes_unfold:
  assumes HB: "body is H1"
  shows
  "while\<^sup>\<top>\<^sup>N b do body od = (bif\<^sub>D b then (body ;; while\<^sup>\<top>\<^sup>N b do body od) else SKIP\<^sub>D eif)"
proof -
  have m:"mono (\<lambda>X. bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif)"
    by (auto intro: monoI seqr_mono cond_mono)
  have H: "(\<lambda>X. bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif) \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H" 
    by (rule stronger_if_d_seq_r_H1_H3_closed[OF HB skip_d_is_H1_H3])          
  have "(while\<^sup>\<top>\<^sup>N b do body od) = (\<nu>\<^sub>N X \<bullet> bif\<^sub>D b then (body;; X) else SKIP\<^sub>D eif)"
    by (simp add: while_gfp_ndes_def_alt)
  also have "... = (bif\<^sub>D b then (body ;; (\<nu>\<^sub>N X \<bullet> bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif)) else SKIP\<^sub>D eif)"
    using mono_Monotone_utp_order [OF m, of "\<H>\<^bsub>NDES\<^esub>"] H
          normal_design_theory_continuous.GFP_weak_unfold 
    by auto
  also have "... = (bif\<^sub>D b then (body ;; while\<^sup>\<top>\<^sup>N b do body od) else SKIP\<^sub>D eif)"
    by (simp add: while_gfp_ndes_def_alt)
  finally show ?thesis .
qed
  
theorem while_lfp_ndes_unfold:
  assumes HB: "body is H1"
  shows
  "while\<^sub>\<bottom>\<^sub>N b do body od = (bif\<^sub>D b then (body;; while\<^sub>\<bottom>\<^sub>N b do body od) else SKIP\<^sub>D eif)"
proof -
  have m:"mono (\<lambda>X. bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif)"
    by (auto intro: monoI seqr_mono cond_mono)
  have H: "(\<lambda>X. bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif) \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
    by (rule stronger_if_d_seq_r_H1_H3_closed[OF HB skip_d_is_H1_H3])       
  have "(while\<^sub>\<bottom>\<^sub>N b do body od) = (\<mu>\<^sub>N X \<bullet> bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif)"
    by (simp add: while_lfp_ndes_def_alt)
  also have "... = (bif\<^sub>D b then (body ;; (\<mu>\<^sub>N X \<bullet> bif\<^sub>D b then (body ;; X) else SKIP\<^sub>D eif)) else SKIP\<^sub>D eif)"
    using mono_Monotone_utp_order [OF m, of "\<H>\<^bsub>NDES\<^esub>"] H
          normal_design_theory_continuous.LFP_weak_unfold 
    by auto
  also have "... = (bif\<^sub>D b then (body ;; while\<^sub>\<bottom>\<^sub>N b do body od) else SKIP\<^sub>D eif)"
    by (simp add: while_lfp_ndes_def_alt)
  finally show ?thesis .
qed
    
theorem while_lfp_ndes_true: 
  "while\<^sub>\<bottom>\<^sub>N true do body od = (\<mu>\<^sub>N X \<bullet> (body;; X))"
  by (simp add: while_lfp_ndes_def_alt alpha)
 
lemma while_lfp_ndes_false:
  "(while\<^sub>\<bottom>\<^sub>N false do body od) = SKIP\<^sub>D"
  by (simp add: while_lfp_ndes_def_alt alpha skip_d_is_H1_H3  
      normal_design_theory_continuous.LFP_const)

theorem while_gfp_ndes_false: "while\<^sup>\<top>\<^sup>N false do body od = SKIP\<^sub>D"
 by (simp add: while_gfp_ndes_def_alt alpha skip_d_is_H1_H3  
      normal_design_theory_continuous.GFP_const)
    
theorem while_gfp_ndes_non_termination: (*because of this lemma and the lemma utp_designs.design_top we do not use gfp for capturing termination *)
  "while\<^sup>\<top>\<^sup>N true do SKIP\<^sub>D od = \<top>\<^sub>D"
  unfolding while_gfp_ndes_def_alt
proof (rule normal_design_theory_continuous.weak.GFP_idem [of "(\<lambda>X. bif\<^sub>D true then SKIP\<^sub>D ;; X else SKIP\<^sub>D eif)",
      unfolded utp_theory_ndes_top_is_not_ok if_d_skip_d_not_ok] , goal_cases)
  case 1
  then show ?case by (simp add: aext_true skip_left_unit_ndesign) 
next
  case 2
  then show ?case by (simp add: aext_true seqr_mono utp_theory.Mono_utp_orderI)
next
  case 3
  then show ?case  unfolding idempotent_def by (simp add: aext_true seqr_assoc)                       
qed

theorem while_lfp_ndes_non_termination: 
  "while\<^sub>\<bottom>\<^sub>N true do  SKIP\<^sub>D od = \<bottom>\<^sub>D"
  unfolding while_lfp_ndes_def_alt
proof (rule normal_design_theory_continuous.weak.LFP_idem [of "(\<lambda>X. bif\<^sub>D true then SKIP\<^sub>D ;; X else SKIP\<^sub>D eif)",
      unfolded utp_theory_ndes_bot_is_true if_d_skip_d_true] , goal_cases)
  case 1
  then show ?case  by (simp add: aext_true skip_left_unit_ndesign)
next
  case 2
  then show ?case by (simp add: aext_true seqr_mono utp_theory.Mono_utp_orderI)
next
  case 3
  then show ?case  unfolding idempotent_def by (simp add: aext_true seqr_assoc)                       
qed    
      
lemma abort_situation_left_zero:
  "Q is \<^bold>N \<Longrightarrow> 
    ((\<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<and> post\<^sub>D P wp false) \<turnstile>\<^sub>n false) ;; Q =  ((\<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<and> post\<^sub>D P wp false) \<turnstile>\<^sub>n false)"  
  by rel_blast
    
lemma nested_abort_situation:
  "\<mu>\<^sub>N (\<lambda> X . ((\<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<and> post\<^sub>D P wp false) \<turnstile>\<^sub>n false) ;; X) = ((\<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<and> post\<^sub>D P wp false) \<turnstile>\<^sub>n false)"
  apply (subst (1) normal_design_theory_continuous.LFP_healthy_comp)
  apply (simp add: comp_def)
  apply (subst  abort_situation_left_zero)    
  using Healthy_Idempotent is_Ncarrier_is_ndesigns apply auto[1]
  apply (simp add: ndesign_H1_H3 normal_design_theory_continuous.LFP_unfold utp_theory.Mono_utp_orderI)
  done 

subsection \<open>Iteration laws for designs\<close>
  
theorem from_until_gfp_des_alt_def:
  "from\<^sup>\<top>\<^sup>D init until exit do body od = init ;; while\<^sup>\<top>\<^sup>D \<not> exit do body od"
  unfolding while_gfp_des_def_alt from_until_gfp_des_def 
  by simp  

lemma from_until_while_gfp_des:
  "from\<^sup>\<top>\<^sup>D SKIP\<^sub>D until exit do body od = while\<^sup>\<top>\<^sup>D \<not> exit do body od"
  unfolding from_until_gfp_des_alt_def
  by (simp add: skip_left_unit_design while_gfp_des_def_alt)
   
lemma from_until_lfp_ndes_is_H1_H3:
  "init is H1 \<Longrightarrow>from\<^sub>\<bottom>\<^sub>N init until exit do body od is \<^bold>N"
  unfolding from_until_lfp_ndes_def
  by (simp add: weaker_seq_r_H1_H3_closed)

lemma from_until_gfp_des_is_H1_H3:
  "init is H1 \<Longrightarrow>from\<^sup>\<top>\<^sup>N init until exit do body od is \<^bold>N"
  unfolding from_until_gfp_ndes_def
  by (simp add: weaker_seq_r_H1_H3_closed)
    
lemma from_until_lfp_des_is_H1_H2:
  "init is H1 \<Longrightarrow> from\<^sub>\<bottom>\<^sub>D init until exit do body od is \<^bold>H"
   unfolding from_until_lfp_des_def
   by (simp add: weaker_seq_r_H1_H2_closed)

lemma from_until_gfp_ndes_is_H1_H2:
  "init is H1 \<Longrightarrow> from\<^sup>\<top>\<^sup>D init until exit do body od is \<^bold>H"
   unfolding from_until_gfp_des_def
   by (simp add: weaker_seq_r_H1_H2_closed)
     
theorem from_until_gfp_des_unfold:
  assumes HB: "body is H1"
  shows "from\<^sup>\<top>\<^sup>D init until exit do body od = 
         init ;; (bif\<^sub>D \<not> exit then (body;; while\<^sup>\<top>\<^sup>D \<not> exit do body od) else SKIP\<^sub>D eif)"
  unfolding from_until_gfp_des_alt_def using while_gfp_des_unfold[OF HB]
  by simp
    
theorem from_until_lfp_des_alt_def:
  "from\<^sub>\<bottom>\<^sub>D init until exit do body od = init ;; while\<^sub>\<bottom>\<^sub>D \<not> exit do body od"
  unfolding while_lfp_des_def_alt from_until_lfp_des_def 
  by simp  

lemma from_until_while_lfp_des:
  "from\<^sub>\<bottom>\<^sub>D SKIP\<^sub>D until exit do body od = while\<^sub>\<bottom>\<^sub>D \<not> exit do body od"
  unfolding from_until_lfp_des_alt_def
  by (simp add: skip_left_unit_design while_lfp_des_def_alt)
    
theorem from_until_lfp_des_unfold:
  assumes HB: "body is H1"
  shows "from\<^sub>\<bottom>\<^sub>D init until exit do body od = 
         init ;; (bif\<^sub>D \<not> exit then (body;; while\<^sub>\<bottom>\<^sub>D \<not> exit do body od) else SKIP\<^sub>D eif)"
  unfolding from_until_lfp_des_alt_def using while_lfp_des_unfold[OF HB]
  by simp

theorem do_while_gfp_des_alt_def:
  "do body while\<^sup>\<top>\<^sup>D exit od = body ;; while\<^sup>\<top>\<^sup>D exit do body od"
  unfolding  do_while_gfp_des_def from_until_gfp_des_alt_def
  by simp  

theorem do_while_lfp_des_alt_def:
  "do body while\<^sub>\<bottom>\<^sub>D exit od = body ;; while\<^sub>\<bottom>\<^sub>D exit do body od"
  unfolding  do_while_lfp_des_def from_until_lfp_des_alt_def
  by simp  
    
lemma do_while_gfp_des_is_H1_H2: 
  "body is H1 \<Longrightarrow> do body while\<^sup>\<top>\<^sup>D b od is \<^bold>H"
  unfolding do_while_gfp_des_def from_until_gfp_des_def
  by (simp add: weaker_seq_r_H1_H2_closed)
    
lemma do_while_lfp_des_is_H1_H2: 
  "body is H1 \<Longrightarrow> do body while\<^sub>\<bottom>\<^sub>D b od is \<^bold>H"
  unfolding do_while_lfp_des_def from_until_lfp_des_def
  by (simp add: weaker_seq_r_H1_H2_closed)  

lemma do_while_gfp_ndes_is_H1_H3:
 "body is H1 \<Longrightarrow> do body while\<^sup>\<top>\<^sup>N b od is \<^bold>N"
  unfolding do_while_gfp_ndes_def from_until_gfp_ndes_def
  by (simp add: weaker_seq_r_H1_H3_closed)
    
lemma do_while_lfp_ndes_is_H1_H3:
  "body is H1 \<Longrightarrow> do body while\<^sub>\<bottom>\<^sub>N b od is \<^bold>N"
  unfolding do_while_lfp_ndes_def from_until_lfp_ndes_def
  by (simp add: weaker_seq_r_H1_H3_closed)
    
theorem do_while_gfp_des_unfold:
  assumes HB: "body is H1"
  shows "do body while\<^sup>\<top>\<^sup>D exit od = 
         body ;; (bif\<^sub>D exit then (body;; while\<^sup>\<top>\<^sup>D exit do body od) else SKIP\<^sub>D eif)"
  unfolding do_while_gfp_des_alt_def using while_gfp_des_unfold[OF HB]
  by simp

theorem do_while_lfp_des_unfold:
  assumes HB: "body is H1"
  shows "do body while\<^sub>\<bottom>\<^sub>D exit od = 
         body ;; (bif\<^sub>D exit then (body;; while\<^sub>\<bottom>\<^sub>D exit do body od) else SKIP\<^sub>D eif)"
  unfolding do_while_lfp_des_alt_def using while_lfp_des_unfold[OF HB]
  by simp    

theorem for_gfp_des_alt_def:
  "for\<^sup>\<top>\<^sup>D (init, exit, incr) do body od = init ;; while\<^sup>\<top>\<^sup>D exit do body;;incr od"
  unfolding  for_gfp_des_def from_until_gfp_des_alt_def
  by simp  
     
theorem for_lfp_des_alt_def:
 "for\<^sub>\<bottom>\<^sub>D (init, exit, incr) do body od = init ;; while\<^sub>\<bottom>\<^sub>D exit do body;;incr od"
  unfolding  for_lfp_des_def from_until_lfp_des_alt_def
  by simp  

lemma for_gfp_ndes_is_H1_H2:
  "init is H1 \<Longrightarrow>for\<^sup>\<top>\<^sup>D (init,b,incr) do body od is \<^bold>H"
  unfolding for_gfp_des_def from_until_gfp_des_def 
  by (simp add: weaker_seq_r_H1_H2_closed)  

lemma for_lfp_des_is_H1_H2:
  "init is H1 \<Longrightarrow>for\<^sub>\<bottom>\<^sub>D (init,b,incr) do body od is \<^bold>H"
  unfolding for_lfp_des_def from_until_lfp_des_def 
  by (simp add: weaker_seq_r_H1_H2_closed)  

lemma for_gfp_ndes_is_H1_H3: 
  "init is H1 \<Longrightarrow>for\<^sup>\<top>\<^sup>N (init,b,incr) do body od is \<^bold>N"
  unfolding for_gfp_ndes_def from_until_gfp_ndes_def 
  by (simp add: weaker_seq_r_H1_H3_closed)  

lemma for_lfp_ndes_is_H1_H3:
  "init is H1 \<Longrightarrow>for\<^sub>\<bottom>\<^sub>N (init,b,incr) do body od is \<^bold>N"
  unfolding for_lfp_ndes_def from_until_lfp_ndes_def 
  by (simp add: weaker_seq_r_H1_H3_closed)
    
theorem for_gfp_des_unfold:
  assumes HB: "body is H1"
  assumes Hinit: "incr is H1" 
  shows "for\<^sup>\<top>\<^sup>D (init, exit, incr) do body od = 
         init ;; (bif\<^sub>D exit then (body;;incr;;while\<^sup>\<top>\<^sup>D exit do body ;; incr od) else SKIP\<^sub>D eif)"
  unfolding for_gfp_des_alt_def using while_gfp_des_unfold[of "body ;; incr" "exit", OF seq_is_H1[OF HB Hinit]] 
  by (metis seqr_assoc)
    
theorem for_lfp_des_unfold:
  assumes HB: "body is H1"
  assumes Hinit: "incr is H1"   
  shows
  "for\<^sub>\<bottom>\<^sub>D (init, exit, incr) do body od = 
   init ;; (bif\<^sub>D exit then (body;;incr;;while\<^sub>\<bottom>\<^sub>D exit do body ;; incr od) else SKIP\<^sub>D eif)"
  unfolding for_lfp_des_alt_def using while_lfp_des_unfold[of "body ;; incr" "exit", OF seq_is_H1[OF HB Hinit]] 
  by (metis seqr_assoc)  

subsection \<open>Iteration laws for normal designs\<close>
  
theorem from_until_gfp_ndes_alt_def:
  "from\<^sup>\<top>\<^sup>N init until exit do body od = init ;; while\<^sup>\<top>\<^sup>N \<not> exit do body od"
  unfolding while_gfp_ndes_def_alt from_until_gfp_ndes_def 
  by simp  

lemma from_until_while_gfp_ndes:
  "from\<^sup>\<top>\<^sup>N SKIP\<^sub>D until exit do body od = while\<^sup>\<top>\<^sup>N \<not> exit do body od"
  unfolding from_until_gfp_ndes_alt_def
  by (simp add: skip_left_unit_ndesign while_gfp_ndes_def_alt)
        
theorem from_until_gfp_ndes_unfold:
  assumes HB: "body is H1"
  shows "from\<^sup>\<top>\<^sup>N init until exit do body od = 
         init ;; (bif\<^sub>D \<not> exit then (body;; while\<^sup>\<top>\<^sup>N \<not> exit do body od) else SKIP\<^sub>D eif)"
  unfolding from_until_gfp_ndes_alt_def using while_gfp_ndes_unfold[OF HB]
  by simp
    
theorem from_until_lfp_ndes_alt_def:
  "from\<^sub>\<bottom>\<^sub>N init until exit do body od = init ;; while\<^sub>\<bottom>\<^sub>N \<not> exit do body od"
  unfolding while_lfp_ndes_def_alt from_until_lfp_ndes_def 
  by simp  

lemma from_until_while_lfp_ndes:
  "from\<^sub>\<bottom>\<^sub>N SKIP\<^sub>D until exit do body od = while\<^sub>\<bottom>\<^sub>N \<not> exit do body od"
  unfolding from_until_lfp_ndes_alt_def
  by (simp add: skip_left_unit_ndesign while_lfp_ndes_def_alt)
    
theorem from_until_lfp_ndes_unfold:
  assumes HB: "body is H1"
  shows "from\<^sub>\<bottom>\<^sub>N init until exit do body od = 
         init ;; (bif\<^sub>D \<not> exit then (body;; while\<^sub>\<bottom>\<^sub>N \<not> exit do body od) else SKIP\<^sub>D eif)"
  unfolding from_until_lfp_ndes_alt_def using while_lfp_ndes_unfold[OF HB]
  by simp

theorem do_while_gfp_ndes_alt_def:
  "do body while\<^sup>\<top>\<^sup>N exit od = body ;; while\<^sup>\<top>\<^sup>N exit do body od"
  unfolding  do_while_gfp_ndes_def from_until_gfp_ndes_alt_def
  by simp  
    
theorem do_while_gfp_ndes_unfold:
  assumes HB: "body is H1"
  shows "do body while\<^sup>\<top>\<^sup>N exit od = 
         body ;; (bif\<^sub>D exit then (body;; while\<^sup>\<top>\<^sup>N exit do body od) else SKIP\<^sub>D eif)"
  unfolding do_while_gfp_ndes_alt_def using while_gfp_ndes_unfold[OF HB]
  by simp

theorem do_while_lfp_ndes_alt_def:
  "do body while\<^sub>\<bottom>\<^sub>N exit od = body ;; while\<^sub>\<bottom>\<^sub>N exit do body od"
  unfolding  do_while_lfp_ndes_def from_until_lfp_ndes_alt_def
  by simp  
    
theorem do_while_lfp_ndes_unfold:
  assumes HB: "body is H1"
  shows "do body while\<^sub>\<bottom>\<^sub>N exit od = 
         body ;; (bif\<^sub>D exit then (body;; while\<^sub>\<bottom>\<^sub>N exit do body od) else SKIP\<^sub>D eif)"
  unfolding do_while_lfp_ndes_alt_def using while_lfp_ndes_unfold[OF HB]
  by simp    

theorem for_gfp_ndes_alt_def:
  "for\<^sup>\<top>\<^sup>N (init, exit, incr) do body od = init ;; while\<^sup>\<top>\<^sup>N exit do body;;incr od"
  unfolding  for_gfp_ndes_def from_until_gfp_ndes_alt_def
  by simp  
    
theorem for_gfp_ndes_unfold:
  assumes HB: "body is H1"
  assumes Hinit: "incr is H1" 
  shows "for\<^sup>\<top>\<^sup>N (init, exit, incr) do body od = 
         init ;; (bif\<^sub>D exit then (body;;incr;;while\<^sup>\<top>\<^sup>N exit do body ;; incr od) else SKIP\<^sub>D eif)"
  unfolding for_gfp_ndes_alt_def using while_gfp_ndes_unfold[of "body ;; incr" "exit", OF seq_is_H1[OF HB Hinit]] 
  by (metis seqr_assoc)

theorem for_lfp_ndes_alt_def:
 "for\<^sub>\<bottom>\<^sub>N (init, exit, incr) do body od = init ;; while\<^sub>\<bottom>\<^sub>N exit do body;;incr od"
  unfolding  for_lfp_ndes_def from_until_lfp_ndes_alt_def
  by simp  
    
theorem for_lfp_ndes_unfold:
  assumes HB: "body is H1"
  assumes Hinit: "incr is H1"   
  shows
  "for\<^sub>\<bottom>\<^sub>N (init, exit, incr) do body od = 
   init ;; (bif\<^sub>D exit then (body;;incr;;while\<^sub>\<bottom>\<^sub>N exit do body ;; incr od) else SKIP\<^sub>D eif)"
  unfolding for_lfp_ndes_alt_def using while_lfp_ndes_unfold[of "body ;; incr" "exit", OF seq_is_H1[OF HB Hinit]] 
  by (metis seqr_assoc)  
    
subsection \<open>assume laws\<close>

lemma assume_d_twice[udes_comp]: "(b\<^sup>\<top>\<^sup>D;; c\<^sup>\<top>\<^sup>D) = (b \<and> c)\<^sup>\<top>\<^sup>D"
  apply pred_simp
  apply auto
  apply (rel_simp)
  apply blast
    apply (rel_simp)
    apply blast
done

lemma assert_d_twice[udes_comp]: "(b\<^sub>\<bottom>\<^sub>D;; c\<^sub>\<bottom>\<^sub>D) = (b \<and> c)\<^sub>\<bottom>\<^sub>D"
 apply pred_simp
  apply auto
  apply (rel_simp)+
    apply blast
  done
    
subsection \<open>Frame and antiframe\<close>
  
lemma frame_d_is_H1_H3:
  assumes "P is \<^bold>N" 
  shows "frame\<^sub>D a P is \<^bold>N"
  using assms unfolding  frame\<^sub>D_def
  by rel_auto  

lemma antiframe_d_is_H1_H3:
  assumes "P is \<^bold>N" 
  shows "antiframe\<^sub>D a P is \<^bold>N"
  using assms unfolding  frame\<^sub>D_def
  by rel_auto  
    
lemma frame_d_assign_d_is_H4:
 "frame\<^sub>D a \<langle>\<sigma>\<rangle>\<^sub>D is H4"
   unfolding  frame\<^sub>D_def 
   by rel_auto
end

  

