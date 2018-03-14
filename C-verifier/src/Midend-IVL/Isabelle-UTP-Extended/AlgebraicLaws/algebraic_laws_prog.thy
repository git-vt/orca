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

section \<open>Algebraic laws for abrupt designs\<close>

theory algebraic_laws_prog
  imports "../impl/utp_prog_des_more"
begin

(* TODO: add laws for assigns when composed with try catch... *)
  
sledgehammer_params[(*stop_on_first,*)parallel_subgoals, join_subgoals]

named_theorems algebraic_laws_prog  

lemma Abs_prog_Rep_prog_ndesign:"\<lbrakk>Abs_prog (\<^bold>N P)\<rbrakk>\<^sub>p = (\<^bold>N P)" 
  by (simp add: Abs_prog_inverse H1_H3_idempotent Healthy_def')

lemmas Abs_prog_Rep_prog_Ncarrier= 
  Abs_prog_Rep_prog_ndesign[folded Ncarrier_ndesigns]
  
lemma fun_apply_rep_prog:
  "\<lbrakk>f X\<rbrakk>\<^sub>p = (Rep_prog \<circ> f \<circ> Abs_prog) \<lbrakk>X\<rbrakk>\<^sub>p"
  by (simp add: Rep_prog_inverse)  
    
subsection \<open>Monotonic laws\<close>
  
lemma Mono_progI:
  "(\<And>x y .x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y) \<Longrightarrow> mono_prog f"
  apply ptransfer
  apply (rule Mono_utp_orderI)
  apply (metis Abs_prog_Rep_prog_Ncarrier Healthy_if comp_apply)
  done
    
lemma Mono_progD:
  "mono_prog f \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
  apply ptransfer
  apply (drule Mono_utp_orderD)
  unfolding fun_apply_rep_prog mono_prog_def
     apply simp_all
   apply (metis Healthy_def' Healthy_if Rep_prog_H1_H3_closed ndes_hcond_def)+
  done
    
lemma Mono_progE:
  "mono_prog f \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> (f x \<sqsubseteq> f y \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  apply ptransfer
  unfolding fun_apply_rep_prog mono_prog_def
  using Mono_utp_orderD Rep_prog_H1_H3_closed is_Ncarrier_is_ndesigns
  by blast
    
lemma mono_Monotone_prog: 
  assumes M:"mono F"
  shows "mono_prog F"
  by (simp add: Mono_progI assms monoD) 

subsection \<open>Lattices laws\<close> 

lemma sup_prog_empty:
  "\<Squnion>\<^sub>p{} = ABORT"  
  by (simp add: prog_rep_eq utp_theory_ndes_bot_is_true)

lemma sup_prog_univ:
  "\<Squnion>\<^sub>pUNIV = MAGIC"    
  apply (simp add: prog_rep_eq sup_def least_def Upper_def)    
  apply (rule someI2_ex)
   apply (rule exI[where x = "(\<not> $ok)"])
   apply auto[]
     apply (metis H1_below_top Healthy_if ndes_hcond_def)
    apply rel_simp
   apply (metis des_top_is_H1_H3 is_Ncarrier_is_ndesigns magic.rep_eq range_eqI)
  apply auto[]
  apply (metis (no_types, hide_lams) H1_below_top Healthy_if antisym_conv des_top_ndes_def 
         magic.rep_eq ndes_hcond_def ndesign_is_healthy_NDES range_eqI)     
  done
    
lemma inf_prog_empty:
  "\<Sqinter>\<^sub>p{} = MAGIC"  
  by (simp add: prog_rep_eq utp_theory_ndes_top_is_not_ok)  
    
lemma inf_prog_univ:
  "\<Sqinter>\<^sub>pUNIV = ABORT"    
  apply (simp add: prog_rep_eq )
  by (metis (no_types, lifting)  Rep_prog UNIV_I image_empty image_subsetI 
      image_subset_iff normal_design_theory_continuous.bottom_lower 
      normal_design_theory_continuous.inf_closed normal_design_theory_continuous.inf_lower 
      normal_design_theory_continuous.weak_sup_empty order_antisym_conv order_refl 
      sup_prog.rep_eq utp_theory_ndes_bot_is_true)
      
lemma sup_prog_least:
  "(\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> z) \<Longrightarrow> \<Squnion>\<^sub>p A \<sqsubseteq> z" 
  apply (simp only: prog_rep_eq)
  apply (rule normal_design_theory_continuous.weak.sup_least)
  using  Rep_prog
    apply auto  
  done
    
lemma sup_prog_upper:
  "x \<in> A \<Longrightarrow> x \<sqsubseteq> \<Squnion>\<^sub>p A " 
  apply (simp only: prog_rep_eq)
  apply (metis (mono_tags, lifting) Rep_prog ball_imageD image_subsetI normal_design_theory_continuous.sup_upper)
  done
    
lemma sup_H1_H3_in_Upper:
  "(\<And>x. x \<in> A \<Longrightarrow> x is \<^bold>N ) \<Longrightarrow> \<^bold>\<Squnion>\<^bsub>NDES\<^esub>A \<in> Upper (uthy_order NDES) A" 
  unfolding Upper_def
  apply auto
   apply (rule normal_design_theory_continuous.sup_upper )  
    apply (simp_all add: is_Ncarrier_is_ndesigns subsetI)
  done
    
lemma sup_prog_in_Upper_prog:
  "(\<Squnion>\<^sub>p A) \<in> (Upper_prog A)"
  by (metis (mono_tags, lifting) Rep_prog_H1_H3_closed Upper_prog_def imageE image_eqI map_fun_def 
                                 o_def sup_H1_H3_in_Upper sup_prog_def)


lemma sup_H1_H3_is_least_Upper:
  "(\<And>x. x \<in> A \<Longrightarrow> x is \<^bold>N) \<Longrightarrow> least (uthy_order NDES) (\<^bold>\<Squnion>\<^bsub>NDES\<^esub> A) (Upper (uthy_order NDES) A)"
  unfolding least_def
  apply (auto simp add: is_Ncarrier_is_ndesigns)        
    apply (metis Upper_closed is_Healthy_subset_member is_Ncarrier_is_ndesigns utp_order_carrier)
  using sup_H1_H3_in_Upper apply auto[1]
  apply (rule normal_design_theory_continuous.weak.sup_least)
    apply (auto simp add: Upper_def is_Ncarrier_is_ndesigns )
  done   
    
lemma sup_prog_is_least_Upper_prog:
  "least_prog (\<Squnion>\<^sub>p A) (Upper_prog A)"
  by (metis (mono_tags, lifting) Rep_prog_H1_H3_closed Upper_prog.rep_eq imageE least_prog.rep_eq 
                                 sup_H1_H3_is_least_Upper sup_prog.rep_eq)

lemma sup_prog_alt_def:
  "(\<Squnion>\<^sub>p A) = (SOME x. least_prog x (Upper_prog A))" 
  apply (rule someI2_ex)
  using sup_prog_is_least_Upper_prog 
   apply blast
  apply (simp only: prog_rep_eq)   
  apply (metis Upper_prog.rep_eq least_prog.rep_eq ndes_utp_theory.least_unique sup_prog.rep_eq sup_prog_is_least_Upper_prog)
  done
    
lemma inf_prog_greatest:
  "(\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x ) \<Longrightarrow> z \<sqsubseteq> \<Sqinter>\<^sub>p A" 
  apply (simp only: prog_rep_eq)
  apply (rule normal_design_theory_continuous.weak.inf_greatest)
  using  Rep_prog
    apply auto  
  done
    
lemma inf_prog_lower:
  "x \<in> A \<Longrightarrow> \<Sqinter>\<^sub>p A \<sqsubseteq> x" 
  apply (simp only: prog_rep_eq) 
  apply (meson Rep_prog image_eqI image_subsetI normal_design_theory_continuous.inf_lower)
  done
    
lemma inf_H1_H3_in_Lower:
  "(\<And>x. x \<in> A \<Longrightarrow> x is \<^bold>N ) \<Longrightarrow> \<^bold>\<Sqinter>\<^bsub>NDES\<^esub>A \<in> Lower (uthy_order NDES) A" 
  unfolding Lower_def
  apply auto
   apply (rule normal_design_theory_continuous.inf_lower )  
    apply (simp_all add: is_Ncarrier_is_ndesigns subsetI)
  done
    
lemma inf_prog_in_Lower_prog:
  "(\<Sqinter>\<^sub>p A) \<in> (Lower_prog A)"
  by (metis (mono_tags, lifting) Rep_prog_H1_H3_closed Lower_prog_def imageE image_eqI map_fun_def 
                                 o_def inf_H1_H3_in_Lower inf_prog_def)

lemma inf_H1_H3_is_greatest_Lower:
  "(\<And>x. x \<in> A \<Longrightarrow> x is \<^bold>N) \<Longrightarrow> greatest (uthy_order NDES) (\<^bold>\<Sqinter>\<^bsub>NDES\<^esub> A) (Lower (uthy_order NDES) A)"
  unfolding greatest_def
  apply (auto simp add: is_Ncarrier_is_ndesigns)        
    apply (metis Lower_closed is_Healthy_subset_member is_Ncarrier_is_ndesigns utp_order_carrier)
  using inf_H1_H3_in_Lower apply auto[1]
  apply (rule normal_design_theory_continuous.weak.inf_greatest)
    apply (auto simp add: Lower_def is_Ncarrier_is_ndesigns )
  done   
    
lemma inf_prog_is_greatest_Lower_prog:
  "greatest_prog (\<Sqinter>\<^sub>p A) (Lower_prog A)"
  by (metis (mono_tags, lifting) Rep_prog_H1_H3_closed Lower_prog.rep_eq imageE greatest_prog.rep_eq 
                                 inf_H1_H3_is_greatest_Lower inf_prog.rep_eq)

lemma inf_prog_alt_def:
  "(\<Sqinter>\<^sub>p A) = (SOME x. greatest_prog x (Lower_prog A))" 
  apply (rule someI2_ex)
  using inf_prog_is_greatest_Lower_prog 
   apply blast
  apply (simp only: prog_rep_eq)   
  apply (metis Lower_prog.rep_eq greatest_prog.rep_eq ndes_utp_theory.greatest_unique inf_prog.rep_eq inf_prog_is_greatest_Lower_prog)
  done
   
lemma meet_prog_alt_def:
  "a \<sqinter>\<^sub>p b = \<Sqinter>\<^sub>p{a, b}"
  by (simp add: prog_rep_eq meet_def)

lemma utp_join_prog_alt_def:
  "a \<squnion>\<^sub>p b = \<Squnion>\<^sub>p{a, b}"
  by (simp add: prog_rep_eq join_def) 

lemma gfp_prog_alt_def:
  "\<nu>\<^sub>p F = \<Squnion>\<^sub>p{x. x \<sqsubseteq> F x}"
  apply (simp only: prog_rep_eq)
  unfolding GFP_def sup_def image_def
  apply auto
  apply (rule someI2_ex)
   apply (rule exI[where x = "\<^bold>\<Squnion>\<^bsub>NDES\<^esub> {y. \<exists>x. \<lbrakk>x\<rbrakk>\<^sub>p \<sqsubseteq> \<lbrakk>F x\<rbrakk>\<^sub>p \<and> y = \<lbrakk>x\<rbrakk>\<^sub>p}"])
    (*Test Timeout bug of sledgehammer para*)
   apply (rule sup_H1_H3_is_least_Upper)
  using Rep_prog 
   apply fastforce
  apply (rule someI2_ex)
   apply (rule exI[where x = "\<^bold>\<Squnion>\<^bsub>NDES\<^esub> {u. (u is \<H>\<^bsub>NDES\<^esub>) \<and> u \<sqsubseteq> \<lbrakk>F (Abs_prog u)\<rbrakk>\<^sub>p}"])
   apply (rule sup_H1_H3_is_least_Upper)
   apply (simp add: is_Ncarrier_is_ndesigns)
  apply (rule ndes_utp_theory.least_unique)
   apply auto
  unfolding least_def Upper_def
  apply auto
   apply (simp add: Rep_prog_inverse)
  unfolding Ball_def
  apply auto
  apply (metis Abs_prog_Rep_prog_Ncarrier Healthy_if)
  done
    
lemma lfp_prog_alt_def:
  "\<mu>\<^sub>p F = \<Sqinter>\<^sub>p{x. F x \<sqsubseteq> x}"      
  apply (simp only: prog_rep_eq)
  unfolding LFP_def inf_def image_def
  apply auto
  apply (rule someI2_ex)
   apply (rule exI[where x = "\<^bold>\<Sqinter>\<^bsub>NDES\<^esub>{y. \<exists>x. \<lbrakk>F x\<rbrakk>\<^sub>p \<sqsubseteq> \<lbrakk>x\<rbrakk>\<^sub>p \<and> y = \<lbrakk>x\<rbrakk>\<^sub>p}"])
   apply (rule inf_H1_H3_is_greatest_Lower)
  using Rep_prog 
   apply fastforce
  apply (rule someI2_ex)
   apply (rule exI[where x="\<^bold>\<Sqinter>\<^bsub>NDES\<^esub>{u. (u is \<H>\<^bsub>NDES\<^esub>) \<and> \<lbrakk>F (Abs_prog u)\<rbrakk>\<^sub>p \<sqsubseteq> u}"])
   apply (rule inf_H1_H3_is_greatest_Lower)
   apply (simp add: is_Ncarrier_is_ndesigns)
  apply (rule  ndes_utp_theory.greatest_unique)
   apply auto
  unfolding greatest_def Lower_def Ball_def
  apply auto
   apply (simp add: Rep_prog_inverse)
  apply (metis Abs_prog_Rep_prog_Ncarrier Healthy_if)
  done
    
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

lemma usubst_assign_p_apply:
  "\<sigma> \<dagger> \<langle>\<rho>\<rangle>\<^sub>p = \<langle>\<rho> o \<sigma>\<rangle>\<^sub>p"
  by (simp add: prog_rep_eq usubst)
    
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
    
subsection \<open>Conditional laws\<close>
  
lemma if_prog_pusbst_distr[usubst]:
 "\<sigma> \<dagger>  (IF b THEN P ELSE Q FI) =  IF \<sigma> \<dagger> b THEN \<sigma> \<dagger> P ELSE \<sigma> \<dagger> Q FI"  
  by (simp add: prog_rep_eq usubst)
    
lemma if_prog_idem[urel_cond]:
  "IF B THEN P ELSE P FI = P"
  by (simp add: prog_rep_eq urel_cond)

lemma if_prog_symm:
  "IF b THEN P ELSE Q FI = IF \<not>b THEN Q ELSE P FI"
  by pauto

lemma if_prog_assoc:
  "IF b THEN P ELSE IF b THEN Q ELSE R FI FI = 
   IF b THEN IF b THEN P ELSE Q FI ELSE R FI"
  by pauto

lemma if_prog_distr'[urel_cond]:
  "IF b THEN IF b' THEN P ELSE R FI ELSE IF b' THEN Q ELSE R FI FI =
   IF b' THEN IF b THEN P ELSE Q FI ELSE R FI"
  by pauto
    
lemma if_prog_true:
  "IF true THEN P ELSE Q FI = P"
  by pauto

lemma if_prog_false:
  "IF false THEN P ELSE Q FI = Q"
  by pauto

lemma if_prog_L6[urel_cond]:
  "IF b THEN P ELSE IF b THEN Q ELSE R FI FI = 
   IF b THEN P ELSE R FI"
  by pauto

lemma if_prog_conj[urel_cond]:
  "IF b \<and> c THEN P ELSE Q FI = IF b THEN IF c THEN P ELSE Q FI ELSE Q FI"
  by pauto

theorem if_prog_12:
  "IF bexp1 THEN (IF bexp2 THEN C1 ELSE C3 FI) ELSE (IF bexp3 THEN C2 ELSE C3 FI) FI = 
   IF (bexp2 \<triangleleft>bexp1\<triangleright>bexp3) THEN  (IF bexp1 THEN C1 ELSE C2 FI) ELSE C3 FI"
  by pauto
    
lemma comp_prog_if_prog_left_distr:
  "((IF b THEN P ELSE Q FI); R) = (IF b THEN (P ; R) ELSE (Q ; R) FI)"
  by pauto
    
lemma seq_prog_monoI:
  "P\<^sub>1 \<sqsubseteq> P\<^sub>2 \<Longrightarrow> Q\<^sub>1 \<sqsubseteq> Q\<^sub>2  \<Longrightarrow> (P\<^sub>1 ; Q\<^sub>1) \<sqsubseteq> (P\<^sub>2 ; Q\<^sub>2)"
   by (simp add: prog_rep_eq seqr_mono)

lemma if_prog_monoI:
  "P\<^sub>1 \<sqsubseteq> P\<^sub>2 \<Longrightarrow> Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<Longrightarrow> (IF b THEN P\<^sub>1 ELSE Q\<^sub>1 FI) \<sqsubseteq> (IF b THEN P\<^sub>2 ELSE Q\<^sub>2 FI)"
  by (simp add: prog_rep_eq cond_mono)
    
lemma if_prog_mono:
  "mono (\<lambda>X. IF b THEN P ; X ELSE Q FI)"
  by (auto intro: monoI seq_prog_monoI if_prog_monoI) 
    
subsection \<open>sequential composition laws\<close>

lemma seq_psubst_prog:
  "\<langle>\<rho>\<rangle>\<^sub>p ; P = (\<rho> \<dagger> P)"   
  by (simp add: prog_rep_eq usubst Rep_prog_H1_H3_closed [THEN H1_H2_impl_H1 [OF H1_H3_impl_H2]])
        
lemma seq_prog_assoc: "P ; (Q ; R) = (P ; Q) ; R"
  by (simp add: prog_rep_eq seqr_assoc)
    
subsection \<open>While laws for programs\<close>
  
text \<open>In this section we introduce the algebraic laws of programming related to the while
      statement.\<close>
        
lemma lfp_prog_unfold: 
  assumes M:"mono_prog f"  
  shows "\<mu>\<^sub>p f = f (\<mu>\<^sub>p f)"
proof -
    show ?thesis  
    apply (simp only: prog_rep_eq)
    unfolding fun_apply_rep_prog  prec_lfp_prog.rep_eq 
    apply (subst (1) normal_design_theory_continuous.LFP_healthy_comp) 
    apply (subst (2) normal_design_theory_continuous.LFP_healthy_comp)    
    using M 
      by (metis (mono_tags, lifting) Pi_I Rep_prog mono_prog.rep_eq normal_design_theory_continuous.LFP_healthy_comp normal_design_theory_continuous.LFP_unfold o_def)
qed

lemma lfp_prog_const: "\<mu>\<^sub>p (\<lambda>x. t) = t"
  by (simp add: mono_prog.rep_eq lfp_prog_unfold utp_theory.Mono_utp_orderI)

lemma lfp_prog_idem:
  "mono_prog f \<Longrightarrow> idem_prog f \<Longrightarrow> \<mu>\<^sub>p f = f ABORT"
proof (ptransfer,
       subst normal_design_theory_continuous.weak.LFP_idem[unfolded utp_theory_ndes_bot_is_true],
       goal_cases)
  case 1
  then show ?case using Rep_prog by fastforce
next
  case 2
  then show ?case  by simp 
next
  case 3
  then show ?case by simp 
next
  case 4
  then show ?case unfolding fun_apply_rep_prog by (simp add: abort.rep_eq)
qed

lemma lfp_prog_lowerbound:
  "f x \<sqsubseteq> x \<Longrightarrow> \<mu>\<^sub>p f \<sqsubseteq> x"
proof(ptransfer, rule normal_design_theory_continuous.weak.LFP_lowerbound, goal_cases)
  case 1
  then show ?case by (simp add: Rep_prog_H1_H3_closed)
next
  case 2
  then show ?case unfolding fun_apply_rep_prog by simp
qed 

lemma lfp_prog_greatest:
 "(\<And>u. f u \<sqsubseteq> u \<Longrightarrow> A \<sqsubseteq> u) \<Longrightarrow> A \<sqsubseteq>  \<mu>\<^sub>p f"   
proof(ptransfer, rule normal_design_theory_continuous.weak.LFP_greatest, goal_cases)
  case 1
  then show ?case by (simp add: Rep_prog_H1_H3_closed)
next
  case 2
  then show ?case unfolding fun_apply_rep_prog by (metis Abs_prog_Rep_prog_ndesign Healthy_def)
qed 
  
lemma lfp_prog_mono:
  "(\<And>u. f u \<sqsubseteq> g u)\<Longrightarrow> \<mu>\<^sub>p f \<sqsubseteq>  \<mu>\<^sub>p g"
  apply (rule lfp_prog_lowerbound[THEN lfp_prog_greatest])
  apply (blast intro: order_trans)  
  done
    
lemma lfp_prog_fixed_point:
   "f x = x \<Longrightarrow> \<mu>\<^sub>p f \<sqsubseteq> x"
   by (simp add: lfp_prog_lowerbound)
    
lemma while_lfp_prog_mu_prog:
  "WHILE b DO body OD = (\<mu>\<^sub>p X \<bullet> IF b THEN body ; X ELSE SKIP FI)"
  unfolding  while_lfp_prog_def from_until_lfp_prog_def skip_prog_left_unit
  by simp 
    
theorem while_lfp_prog_unfold:
  "WHILE b DO body OD = (IF b THEN (body ; WHILE b DO body OD) ELSE SKIP FI)"
proof -  
  have "(WHILE b DO body OD) = (\<mu>\<^sub>p X \<bullet> IF b THEN (body ; X) ELSE SKIP FI)"
    by (simp add: while_lfp_prog_mu_prog)
  also have "... = (IF b THEN (body ; (\<mu>\<^sub>p X \<bullet> IF b THEN (body ; X) ELSE SKIP FI)) ELSE SKIP FI)"
    proof (rule lfp_prog_unfold[OF Mono_progI ], goal_cases)
      case (1 x y)
      then show ?case by (simp add: if_prog_monoI seq_prog_monoI)
    qed  
  also have "... = (IF b THEN (body ; WHILE b DO body OD) ELSE SKIP FI)"
    by (simp add: while_lfp_prog_mu_prog)
  finally show ?thesis .
qed

theorem while_lfp_prog_true: 
  "WHILE true DO body OD = (\<mu>\<^sub>p X \<bullet>  body ; X)" 
  unfolding while_lfp_prog_mu_prog  if_prog_true ..
   
lemma while_lfp_prog_false:
  "(WHILE false DO body OD) = SKIP"
  unfolding while_lfp_prog_mu_prog if_prog_false
  by (simp add: lfp_prog_const) 

lemma while_lfp_prog_non_termination:
  "WHILE true DO SKIP OD = ABORT"
  unfolding while_lfp_prog_mu_prog if_prog_true 
  by (auto simp add: lfp_prog_idem Mono_progI Rep_prog_inverse idem_prog.rep_eq idempotent_def)
    
subsection \<open>Iteration laws\<close>
    
lemma from_until_lfp_prog_def_alt:
  "FROM init UNTIL b DO body OD = init ; WHILE \<not>b DO body OD"
  unfolding from_until_lfp_prog_def while_lfp_prog_mu_prog ..

lemma from_until_lfp_prog_unfold:
  "FROM init UNTIL b DO body OD = init ; IF \<not>b THEN body ; WHILE \<not>b DO body OD ELSE SKIP FI"
  unfolding from_until_lfp_prog_def_alt 
  using while_lfp_prog_unfold[of "\<not>b" body]
  by simp

lemma from_until_lfp_prog_true: 
  "FROM init UNTIL true DO body OD = init"
  unfolding from_until_lfp_prog_def_alt
  by (simp add: while_lfp_prog_false)
    
lemma from_until_lfp_prog_non_termination: (*should equal abort situation*)
  "FROM init UNTIL false DO SKIP OD = init ; ABORT"
  unfolding from_until_lfp_prog_def_alt
  by (simp add: while_lfp_prog_non_termination)
    
lemma do_while_lfp_prog_def_alt:
  "DO body WHILE b OD = body ; WHILE b DO body OD"
  unfolding do_while_lfp_prog_def from_until_lfp_prog_def_alt
  by simp
        
lemma do_while_lfp_prog_unfold: 
  "DO body WHILE b OD = body ; IF b THEN body; WHILE b DO body OD ELSE SKIP FI"
  unfolding do_while_lfp_prog_def_alt
  using while_lfp_prog_unfold[of b body]
  by simp
    
lemma do_while_lfp_prog_false:
  "DO body WHILE false OD = body"
  unfolding do_while_lfp_prog_def_alt
  by (simp add: while_lfp_prog_false)

lemma do_while_lfp_prog_non_termination:(*should equal abort situation*)
  "DO SKIP WHILE true OD = ABORT" 
  unfolding do_while_lfp_prog_def_alt
  by (simp add: while_lfp_prog_non_termination)

lemma for_lfp_prog_def_alt:
  "FOR (init, b, incr) DO body OD = 
   init ; WHILE b DO body ; incr OD"
  unfolding for_lfp_prog_def from_until_lfp_prog_def_alt
  by simp
    
lemma for_lfp_prog_unfold: 
  "FOR (init, b, incr) DO body OD = 
   init; IF b THEN body; incr; WHILE b DO body; incr OD ELSE SKIP FI"
  unfolding for_lfp_prog_def_alt 
  using while_lfp_prog_unfold [of b "body;incr"] seq_prog_assoc[THEN HOL.sym]
  by metis
    
lemma for_lfp_prog_false:
  "FOR (init, false, incr) DO body OD = init"
  unfolding for_lfp_prog_def_alt
  by (simp add: while_lfp_prog_false)

lemma for_lfp_prog_non_termination:
  "FOR (init, true, incr) DO SKIP OD = init; WHILE true DO incr OD"
  unfolding for_lfp_prog_def_alt
  by (simp add: while_lfp_prog_non_termination)

subsection \<open>assume laws\<close>

lemma assume_twice[algebraic_laws_prog]: "((b\<^sup>\<top>\<^sup>P) ; (c\<^sup>\<top>\<^sup>P)) = (b \<and> c)\<^sup>\<top>\<^sup>P"
  by (simp add: prog_rep_eq) (metis assume_d_twice assume_des_def)  
 
lemma assert_twice[algebraic_laws_prog]: "(b\<^sub>\<bottom>\<^sub>P ; (c\<^sub>\<bottom>\<^sub>P)) = (b \<and> c)\<^sub>\<bottom>\<^sub>P"
  by (simp add: prog_rep_eq) (metis assert_d_twice assert_des_def) 

end


