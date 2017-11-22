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
  apply (rel_auto )
  apply smt
  done
    
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
    
lemma H1_H2_impl_H1: "P is \<^bold>H \<Longrightarrow> P is H1"  
  by pred_blast
    
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
  
lemma design_is_H1:
  "(P \<turnstile> Q) is H1"  
  by pred_auto 

lemma weaker_seq_r_H1_H2_closed [closure]:
  assumes "P is H1"  "Q is \<^bold>H"
  shows "(P ;; Q) is \<^bold>H"
proof -
 obtain Q\<^sub>1 Q\<^sub>2 where "Q = Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2"
   by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def assms(2)) 
   moreover have "(P ;; (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2)) is \<^bold>H"
   proof -
     have "H1 P = P"
       by (metis Healthy_def assms(1))
     then show ?thesis
       by (metis (no_types) H1_H3_commute H1_H3_idempotent H1_H3_impl_H2 H3_def Healthy_def assms(2) calculation design_left_unit seq_r_H1_H2_closed seqr_assoc)
   qed 
  ultimately show ?thesis by simp
qed             

subsection \<open>While laws for designs\<close>
  
text \<open>In this section we introduce the algebraic laws of programming related to the while
      statement.\<close>

theorem while_des_unfold_gen:
  assumes HB: "B is H1"
  shows "while\<^sub>D b do B od = (bif\<^sub>D b then (B;; while\<^sub>D b do B od) else SKIP\<^sub>D eif)"
proof -
  have m:"mono (\<lambda>X. bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)"
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

(*lemma while_true:
  shows "(while true do (P\<turnstile>Q) od) = false"it should eq to \<top>\<^sub>D
  apply (simp add: While_lfp_des_def alpha)
   apply (rule antisym)
  apply (simp_all)
  apply (rule lfp_lowerbound)
  apply (simp)
  done*)
 
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
    
subsection {*Refinement laws*}

lemma cond_refine_des: 
  assumes "((b \<and> p) \<turnstile> q) \<sqsubseteq> C\<^sub>1" and "((\<not>b \<and> p) \<turnstile> q)\<sqsubseteq> C\<^sub>2" 
  shows "(p \<turnstile> q) \<sqsubseteq> (C\<^sub>1 \<triangleleft> b \<triangleright> C\<^sub>2)"
  using assms by rel_blast
    
lemma seq_refine_unrest_des:
  assumes "out\<alpha> \<sharp> p" "in\<alpha> \<sharp> q"
  assumes "(p \<turnstile> \<lceil>s\<rceil>\<^sub>D\<^sub>>) \<sqsubseteq> P" and "(\<lceil>s\<rceil>\<^sub>D\<^sub>< \<turnstile> q) \<sqsubseteq> Q"
  shows "(p \<turnstile> q) \<sqsubseteq> (P ;; Q)"
  apply (insert assms)  
  apply rel_auto
   apply metis+ 
  done
    
lemma skip_refine_des:
  "`(SKIP\<^sub>D \<Rightarrow> (p \<turnstile> q))` \<Longrightarrow> (p \<turnstile> q) \<sqsubseteq> SKIP\<^sub>D"
  by pred_auto   


end
