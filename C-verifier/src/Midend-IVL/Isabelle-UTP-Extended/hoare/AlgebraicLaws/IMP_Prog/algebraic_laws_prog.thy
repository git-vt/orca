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

theorem while_bot_prog_true: 
  "WHILE true DO B OD = (\<mu>\<^sub>p X \<bullet> B ; X)"
proof -
  have "while\<^sub>N true do \<lbrakk>B\<rbrakk>\<^sub>p od = \<mu>\<^sub>N (op ;; \<lbrakk>B\<rbrakk>\<^sub>p)"
    by (rule while_bot_ndes_true)
  also have "\<dots> = \<mu>\<^sub>N (op ;; \<lbrakk>B\<rbrakk>\<^sub>p \<circ> \<H>\<^bsub>NDES\<^esub>)"
    by (rule normal_design_theory_continuous.LFP_healthy_comp)  
  also have "\<dots> = \<mu>\<^sub>N (Rep_prog \<circ> op ; B \<circ> Abs_prog)"
    apply (subst (2) normal_design_theory_continuous.LFP_healthy_comp)
    apply (simp add: comp_def prog_rep_eq Abs_prog_Rep_prog_Ncarrier)
    done  
  finally show ?thesis by (simp add: prog_rep_eq)
qed
  
lemma while_inv_prog_true: 
  "INVR I WHILE true DO B OD = (\<mu>\<^sub>p X \<bullet> B ; X)"
   unfolding pwhile_inv_prog_def using while_bot_prog_true
   by auto    

lemma while_inv_vrt_prog_true: 
  "INVR I VRT E WHILE true DO B OD = (\<mu>\<^sub>p X \<bullet> B ; X)"
   unfolding pwhile_inv_vrt_prog_def using while_bot_prog_true
   by auto 
     
lemma while_prog_false:
  shows "(WHILE false DO P OD) = SKIP"
  by (simp add: prog_rep_eq while_ndes_false)  
    
lemma while_inv_prog_false:
  shows "(INVR I WHILE false DO B OD) = SKIP"
  by (simp add: prog_rep_eq while_ndes_false)  
 
lemma while_inv_vrt_prog_false:
  shows "(INVR I VRT E WHILE false DO B OD) = SKIP"
  by (simp add: prog_rep_eq while_ndes_false)          
    
subsection \<open>assume laws\<close>

lemma assume_twice[algebraic_laws_prog]: "((b\<^sup>\<top>\<^sup>P) ; (c\<^sup>\<top>\<^sup>P)) = (b \<and> c)\<^sup>\<top>\<^sup>P"
  by (simp add: prog_rep_eq) (metis assume_d_twice assume_des_def)  
 
lemma assert_twice[algebraic_laws_prog]: "(b\<^sub>\<bottom>\<^sub>P ; (c\<^sub>\<bottom>\<^sub>P)) = (b \<and> c)\<^sub>\<bottom>\<^sub>P"
  by (simp add: prog_rep_eq) (metis assert_d_twice assert_des_def) 

end
