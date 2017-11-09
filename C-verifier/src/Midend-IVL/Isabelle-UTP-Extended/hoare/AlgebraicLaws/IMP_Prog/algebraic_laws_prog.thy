section \<open>Algebraic laws for abrupt designs\<close>

theory algebraic_laws_prog
  imports "../../../impl/utp_prog_des_more"
begin

(* TODO: add laws for assigns when composed with try catch... *)

named_theorems algebraic_laws_prog  

subsection Skip

text \<open>In this section we introduce the algebraic laws of programming related to the SKIP
      statement.\<close>

lemma skip_prog_left_unit [algebraic_laws_prog]:
  "(SKIP ; P) = P"
  by simp
    
lemma skip_prog_right_unit[algebraic_laws_prog]:
  "(P ; SKIP) = P"
  by simp

subsection \<open>Assignment Laws\<close>
text \<open>In this section we introduce the algebraic laws of programming related to the assignment
      statement.\<close>
  
lemma assigns_prog_id [algebraic_laws_prog]: "\<langle>id\<rangle>\<^sub>p = SKIP"
  by (simp add: prog_rep_eq)

lemma assigns_prog_test[algebraic_laws_prog]:
  assumes 1:"mwb_lens x"
  shows     "(x :== \<guillemotleft>u\<guillemotright> ; x :== \<guillemotleft>v\<guillemotright>) = (x :== \<guillemotleft>v\<guillemotright>)"
  using 1
  by (simp add: prog_rep_eq assign_design_test)

lemma assigns_prog_left_subst: (*we need to re express the algebraic laws for substitution*)
  "(x :== u ; P) = (psubst [x \<mapsto>\<^sub>s u] P)"
  by (simp add: prog_rep_eq  usubst H1_H3_impl_H2 Rep_prog_H1_H3_closed assigns_d_comp_ext )

lemma assigns_prog_twice[algebraic_laws_prog]:
  assumes "mwb_lens x" and  "x \<sharp> f"
  shows "(x :== e ; x :== f) = (x :== f)"
  using assms
  by (simp add: prog_rep_eq assign_d_twice)

lemma assigns_prog_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x :== e ; y :==  f) = (y :== f ; x :==  e)"
  using assms
  by (simp add: prog_rep_eq assigns_d_commute)

lemma assigns_prog_left_cond_cond[algebraic_laws_prog]: 
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "(x :== e ; (IF b THEN P ELSE Q FI)) =
         (IF (b\<lbrakk>e/x\<rbrakk>) THEN (x :== e ; P) ELSE (x :== e ; Q) FI)"    
  by (simp add: prog_rep_eq closure assigns_d_left_cond_d_ndesigns)

lemma assigns_prog_uop1[algebraic_laws_prog]:
  assumes 1: "mwb_lens v"
  shows "(v :== e1 ; v :== (uop F (&v))) = (v :== (uop F e1))"
  by (simp add: prog_rep_eq assigns_d_uop1 assms)

lemma assign_prog_bop1[algebraic_laws_prog]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v :== e1 ; v :== (bop bp (&v) e2)) = (v :== (bop bp e1 e2))"
  by (simp add: prog_rep_eq assign_d_bop1 assms)

lemma assign_prog_bop2[algebraic_laws_prog]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v :== e1 ; v :== (bop bp e2 (&v))) = (v :== (bop bp e2 e1))"
  by (simp add: prog_rep_eq assign_d_bop2 assms)

lemma assign_prog_trop1[algebraic_laws_prog]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :== e1 ; v :== (trop tp (&v) e2 e3)) =
         (v :== (trop tp e1 e2 e3))"
  by (simp add: prog_rep_eq assign_d_trop1 assms)

lemma assign_prog_trop2[algebraic_laws_prog]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :== e1 ; v :== (trop tp e2 (&v) e3)) =
         (v :== (trop tp e2 e1 e3))"
  by (simp add: prog_rep_eq assign_d_trop2 assms)

lemma assign_prog_trop3[algebraic_laws_prog]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :== e1 ; v :== (trop tp e2 e3 (&v))) =
         (v :== (trop tp e2 e3 e1))"
  by (simp add: prog_rep_eq assign_d_trop3 assms)

lemma assign_prog_qtop1[algebraic_laws_prog]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :== e1 ; v :== (qtop tp (&v) e2 e3 e4)) =
         (v :== (qtop tp e1 e2 e3 e4))"
  by (simp add: prog_rep_eq assign_d_qtop1 assms)

lemma assign_prog_qtop2[algebraic_laws_prog]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :== e1 ; v :== (qtop tp e2 (&v) e3 e4)) =
         (v :== (qtop tp e2 e1 e3 e4))"
  by (simp add: prog_rep_eq assign_d_qtop2 assms)

lemma assign_prog_qtop3[algebraic_laws_prog]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :== e1 ; v :== (qtop tp e2 e3 (&v) e4)) =
         (v :== (qtop tp e2 e3 e1 e4))"
  by (simp add: prog_rep_eq assign_d_qtop3 assms)

lemma assign_prog_qtop4[algebraic_laws_prog]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :== e1 ; v :== (qtop tp e2 e3 e4 (&v))) =
         (v :== (qtop tp e2 e3 e4 e1))"
  by (simp add: prog_rep_eq assign_d_qtop4 assms)

text \<open>In the sequel we define assignment laws proposed by Hoare\<close>

lemma assign_prog_vwb_skip_prog[algebraic_laws_prog]:
  assumes 1: "vwb_lens v"
  shows "(v :== &v) = SKIP"
  by (simp add: assms prog_rep_eq assign_d_vwb_skip_d)

lemma assign_prog_simultaneous:
  assumes  1: "vwb_lens var2"
  and      2: "var1 \<bowtie> var2"
  shows "var1, var2 :== expr, &var2 = var1 :== expr"
  by (simp add: assms assign_d_simultaneous prog_rep_eq)

lemma assign_prog_seq[algebraic_laws_prog]:
  assumes  1: "vwb_lens var2"
  shows"(var1 :== expr) ; (var2 :== &var2) = (var1 :== expr)"
  by (simp add: assms prog_rep_eq assign_d_seq)

lemma assign_prog_cond_prog_uop[algebraic_laws_prog]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v"
  shows "IF uop F expr THEN (v :== expr ;  C1) ELSE (v :== expr ; C2) FI =
          v :== expr ; IF uop F (&v) THEN  C1 ELSE C2 FI"
  by (simp add: assms prog_rep_eq closure assign_d_cond_d_uop_ndesigns)
     
lemma assign_prog_cond_bop1[algebraic_laws_prog]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "IF bop bp expr exp2 THEN (v :== expr ; C1) ELSE (v :== expr ; C2) FI =
          v :== expr ; IF bop bp (&v) exp2 THEN C1 ELSE C2 FI"
  by (simp add: assms prog_rep_eq closure assign_d_cond_d_bop1_ndesigns)
  
lemma assign_prog_cond_bop2[algebraic_laws_prog]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "IF bop bp exp2 expr THEN (v :== expr ; C1) ELSE (v :== expr ; C2) FI =
          v :== expr ; IF bop bp  exp2 (&v) THEN  C1 ELSE C2 FI"
  by (simp add: assms prog_rep_eq closure assign_d_cond_d_bop2_ndesigns)
 

lemma assign_prog_cond_prog_trop1[algebraic_laws_prog]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "IF trop bp expr exp2 exp3 THEN (v :== expr ; C1) ELSE (v :== expr ; C2) FI =
         v :== expr ; IF trop bp (&v) exp2 exp3 THEN  C1 ELSE  C2 FI"
  by (simp add: assms prog_rep_eq closure assign_d_cond_d_trop1_ndesigns)
 

lemma assign_prog_cond_prog_trop2[algebraic_laws_prog]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "IF trop bp exp2 expr exp3 THEN (v :== expr ; C1) ELSE (v :== expr ; C2) FI =
         v :== expr ; IF trop bp exp2 (&v) exp3 THEN C1 ELSE C2 FI"
  by (simp add: assms prog_rep_eq closure assign_d_cond_d_trop2_ndesigns)
 

lemma assign_prog_cond_prog_trop3[algebraic_laws_prog]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "IF trop bp exp2 exp3 expr THEN (v :== expr ; C1) ELSE (v :== expr ; C2) FI =
         v :== expr ; IF trop bp exp2 exp3 (&v) THEN  C1 ELSE C2 FI"
  by (simp add: assms prog_rep_eq closure assign_d_cond_d_trop3_ndesigns)

lemma assign_prog_cond_prog_qtop1[algebraic_laws_prog]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "IF qtop bp expr exp2 exp3 exp4 THEN (v :== expr ; Simpl\<^sub>A\<^sub>B\<^sub>R C1) ELSE (v :== expr ; Simpl\<^sub>A\<^sub>B\<^sub>R C2) FI =
         v :== expr ; IF qtop bp (&v) exp2 exp3 exp4 THEN Simpl\<^sub>A\<^sub>B\<^sub>R C1 ELSE Simpl\<^sub>A\<^sub>B\<^sub>R C2 FI"
  by (simp add: assms prog_rep_eq closure assign_d_cond_d_qtop1_ndesigns)

lemma assign_prog_cond_prog_qtop2[algebraic_laws_prog]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4:"v \<sharp> exp4"
  shows "IF qtop bp exp2 expr  exp3 exp4 THEN (v :== expr ; C1) ELSE (v :== expr ; C2) FI =
         v :== expr ; IF qtop bp exp2 (&v) exp3 exp4 THEN C1 ELSE C2 FI"
  by (simp add: assms prog_rep_eq closure assign_d_cond_d_qtop2_ndesigns)

lemma assign_prog_cond_prog_qtop3[algebraic_laws_prog]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "IF qtop bp exp2 exp3 expr exp4 THEN (v :== expr ; C1) ELSE (v :== expr ; C2) FI =
         v :== expr ; IF qtop bp exp2 exp3 (&v) exp4 THEN C1 ELSE  C2 FI"
  by (simp add: assms prog_rep_eq closure assign_d_cond_d_qtop3_ndesigns)

lemma assign_prog_cond_prog_qtop4[algebraic_laws_prog]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "IF qtop bp exp2 exp3 exp4 expr THEN (v :== expr ; C1) ELSE (v :== expr ; C2) FI =
         v :== expr ; IF qtop bp exp2 exp3 exp4 (&v) THEN C1 ELSE C2 FI"
  by (simp add: assms prog_rep_eq closure assign_d_cond_d_qtop4_ndesigns)

lemma assigns_prog_cond_prog[algebraic_laws_prog]:
  "(IF bexp THEN (v :== exp1) ELSE (v :== exp2) FI) =
   (v :== (exp1 \<triangleleft> bexp \<triangleright> exp2))"
  by (simp add: prog_rep_eq closure assign_d_cond_d_If)

subsection \<open>While laws for designs\<close>
  
text \<open>In this section we introduce the algebraic laws of programming related to the while
      statement.\<close>

theorem while_prog_unfold:
  "WHILE b DO B OD = (IF b THEN (B ; WHILE b DO B OD) ELSE SKIP FI)"
proof -
  have *: "\<lbrakk>B\<rbrakk>\<^sub>p is H1"
    by (simp add: H1_H2_impl_H1[OF H1_H3_impl_H2] Rep_prog_H1_H3_closed) 
  also have **: "while\<^sub>N b do \<lbrakk>B\<rbrakk>\<^sub>p od = bif\<^sub>D b then \<lbrakk>B\<rbrakk>\<^sub>p ;; while\<^sub>N b do \<lbrakk>B\<rbrakk>\<^sub>p od else SKIP\<^sub>D eif"
    by (rule while_bot_ndes_unfold_gen[OF *])
  then show ?thesis by (simp only: prog_rep_eq)        
qed
         
lemma while_inv_prog_unfold:
  "INVR I WHILE b DO B OD = (IF b THEN (B ; INVR I WHILE b DO B OD) ELSE SKIP FI)"
  unfolding pwhile_inv_prog_def using while_prog_unfold 
  by auto

lemma while_inv_vrt_des_unfold:
   "INVR I VRT E WHILE b DO B OD = 
   (IF b THEN (B ; (INVR I VRT E WHILE b DO B OD)) ELSE SKIP FI)"
  unfolding pwhile_inv_vrt_prog_def using while_prog_unfold 
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
