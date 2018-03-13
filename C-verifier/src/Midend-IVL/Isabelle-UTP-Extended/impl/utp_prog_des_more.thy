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

section {* Imperative Programs *}
  
theory utp_prog_des_more
  imports 
    "../../Isabelle-UTP/impl/utp_prog"
begin

section \<open>More Operators\<close>

subsection \<open>Conditional\<close>
 
lift_definition pcond_prog :: "'\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" ("IF (_)/ THEN (_) ELSE (_) FI") 
  is "IfD" 
  by (simp add: H1_H3_impl_H2 H3_unrest_out_alpha if_d_H1_H3_intro)
    
declare pcond_prog.rep_eq [prog_rep_eq]
  
subsection \<open>assert and assume\<close>

abbreviation passume_prog :: "'\<alpha> cond \<Rightarrow> '\<alpha> prog" ("_\<^sup>\<top>\<^sup>P")  
  where "passume_prog c \<equiv> (IF c THEN SKIP ELSE magic FI)"

abbreviation passert_prog :: "'\<alpha> upred \<Rightarrow> '\<alpha> prog" ("_\<^sub>\<bottom>\<^sub>P")
  where "passert_prog c \<equiv> (IF c THEN SKIP ELSE abort FI)"
    
subsection \<open>Recursion\<close>    

lift_definition Lower_prog:: "'\<alpha> prog set \<Rightarrow> '\<alpha> prog set"
  is "Lower (uthy_order NDES)" 
  by (metis Lower_closed is_Healthy_subset_member is_Ncarrier_is_ndesigns utp_order_carrier)
    
lift_definition Upper_prog:: "'\<alpha> prog set \<Rightarrow> '\<alpha> prog set"
  is "Upper (uthy_order NDES)" 
  by (metis Upper_closed is_Healthy_subset_member is_Ncarrier_is_ndesigns utp_order_carrier)
  
lift_definition least_prog:: " '\<alpha> prog \<Rightarrow> ('\<alpha> prog) set \<Rightarrow> bool"
  is "least (uthy_order NDES)".

lift_definition greatest_prog:: " '\<alpha> prog \<Rightarrow> ('\<alpha> prog) set \<Rightarrow> bool"
  is "greatest (uthy_order NDES)". 
    
lift_definition inf_prog :: "('\<alpha> prog) set \<Rightarrow> '\<alpha> prog" ("\<Sqinter>\<^sub>p_" [900] 900)
  is "inf (uthy_order NDES)"  
  by (simp add: subsetI)

lift_definition sup_prog  :: "('\<alpha> prog) set \<Rightarrow> '\<alpha> prog" ("\<Squnion>\<^sub>p_" [900] 900)
  is "sup (uthy_order NDES)"
  by (simp add: subsetI)
    
declare Lower_prog.rep_eq    [prog_rep_eq]  
declare Upper_prog.rep_eq    [prog_rep_eq] 
declare least_prog.rep_eq    [prog_rep_eq]  
declare greatest_prog.rep_eq [prog_rep_eq]   
declare inf_prog.rep_eq      [prog_rep_eq]  
declare sup_prog.rep_eq      [prog_rep_eq]
term "SOME x . least_prog x (Upper_prog A)"
term "SOME x . greatest_prog x (Lower_prog A)"
  
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

sledgehammer_params[stop_on_first,parallel_subgoals, join_subgoals]

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
    
lift_definition utp_meet_prog:: "'\<alpha> prog \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" (infixl "\<sqinter>\<^sub>p" 70)
  is "meet (uthy_order NDES)"
  by (simp add: closure)

lift_definition utp_join_prog:: "'\<alpha> prog \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" (infixl "\<squnion>\<^sub>p" 65)
  is "join (uthy_order NDES)"
  by (simp add: closure)
    
declare utp_meet_prog.rep_eq [prog_rep_eq]  
declare utp_join_prog.rep_eq [prog_rep_eq]
  
lemma utp_meet_prog_def_alt:
  "a \<sqinter>\<^sub>p b = \<Sqinter>\<^sub>p {a, b}"
  by (simp add: prog_rep_eq meet_def)

lemma utp_join_prog_def_alt:
  "a \<squnion>\<^sub>p b = \<Squnion>\<^sub>p {a, b}"
  by (simp add: prog_rep_eq join_def)

lift_definition prec_lfp_prog :: "('\<alpha> prog \<Rightarrow> '\<alpha> prog) \<Rightarrow> '\<alpha> prog" 
  is "ndesign_lfp" 
  apply (simp)
  apply (subst (1) normal_design_theory_continuous.LFP_healthy_comp)
  apply (subst (2) normal_design_theory_continuous.LFP_healthy_comp) 
  apply (simp add: comp_def H1_H3_commute H1_idem H3_idem Healthy_def ndes_hcond_def)
  done

lift_definition prec_gfp_prog :: "('\<alpha> prog \<Rightarrow> '\<alpha> prog) \<Rightarrow> '\<alpha> prog" 
  is "ndesign_gfp" 
  apply (simp)
  apply (subst (1) normal_design_theory_continuous.GFP_healthy_comp)
  apply (subst (2) normal_design_theory_continuous.GFP_healthy_comp) 
  apply (simp add: comp_def H1_H3_commute H1_idem H3_idem Healthy_def ndes_hcond_def)
  done
    
declare prec_lfp_prog.rep_eq [prog_rep_eq]  
declare prec_gfp_prog.rep_eq [prog_rep_eq]  
  
syntax
  "_pmu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu>\<^sub>p _ \<bullet> _" [0, 10] 10)
  "_pnu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<nu>\<^sub>p _ \<bullet> _" [0, 10] 10)

notation prec_lfp_prog ("\<mu>\<^sub>p")
notation prec_gfp_prog ("\<nu>\<^sub>p")

translations
  "\<mu>\<^sub>p X \<bullet> P" == "CONST prec_lfp_prog (\<lambda> X. P)"
  "\<nu>\<^sub>p X \<bullet> P" == "CONST prec_gfp_prog (\<lambda> X. P)" 

subsection{*Iterations*}    
text {*Since we will not use gfp to prove termination we lift only lfp definition.*}
(*TODO: make it independent from diesign and relation layers. namely: rather using lift_def for the derived operation, use fixed point.*)

definition from_until_lfp_prog :: 
  "'\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" 
  ("FROM (_)/ UNTIL (_)/ DO (_) OD")
where "FROM init UNTIL exit DO body OD = init ; (\<mu>\<^sub>p X \<bullet> IF \<not> exit THEN (body ; X) ELSE SKIP FI)"  

definition from_until_lfp_invr_prog :: 
  "'\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" 
  ("FROM (_)/ INVAR (_)/ UNTIL (_)/  DO (_) OD")  
where "FROM init INVAR invar UNTIL exit DO body OD = FROM init UNTIL exit DO body OD"

definition from_until_lfp_invr_vrt_prog :: 
  "'\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" 
  ("FROM (_)/ INVAR (_)/ VRT (_)/ UNTIL (_)/ DO (_) OD")
where "FROM init INVAR invar VRT vari UNTIL exit DO body OD = FROM init UNTIL exit DO body OD" 

definition while_lfp_prog :: 
  "'\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" 
  ("WHILE (_)/ DO (_) OD")
where "WHILE b DO body OD = FROM SKIP UNTIL \<not>b DO body OD"    

definition while_lfp_invr_prog :: 
  "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" 
  ("INVAR (_)/ WHILE (_)/ DO (_) OD")
where "INVAR invar WHILE b DO body OD = WHILE b DO body OD" 

definition while_lfp_invr_vrt_prog :: 
  "'\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" 
  ("INVAR (_)/ VRT (_)/ WHILE (_)/ DO (_) OD")
where "INVAR invar VRT vari WHILE b DO body OD = WHILE b DO body OD"

definition do_while_lfp_prog :: 
  "'\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> prog" 
  ("DO (_)/  WHILE (_) OD")
where "DO body WHILE b OD = FROM body UNTIL \<not> b DO body OD"
    
definition do_while_lfp_invr_prog :: 
  "'\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> prog" 
  ("DO (_)/ INVAR (_)/ WHILE (_) OD")
where "DO body INVAR invar WHILE b OD = DO body WHILE b OD"
    
definition do_while_lfp_invr_vrt_prog :: 
  "'\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> prog" 
  ("DO (_)/ INVAR (_)/ VRT (_)/ WHILE (_) OD")
where "DO body INVAR invar VRT vari WHILE b OD = DO body WHILE b OD"  

definition for_lfp_prog :: 
  "'\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" 
  ("FOR ('(_,_,_'))/ DO (_) OD")
where "FOR (init, b, incr) DO body OD = FROM init UNTIL \<not> b DO body ; incr OD"

definition for_lfp_invr_prog :: 
  "'\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" 
  ("FOR ('(_,_,_'))/ INVAR (_)/ DO (_) OD")
where "FOR (init, b, incr) INVAR invar DO body OD = FOR (init, b, incr) DO body OD"  
    
definition for_lfp_invr_vrt_prog :: 
  "'\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" 
  ("FOR ('(_,_,_'))/ INVAR (_)/ VRT (_)/ DO (_) OD")
where "FOR (init, b, incr) INVAR invar VRT vari DO body OD = FOR (init, b, incr) DO body OD"  

subsection{*Frame and anti-frame*}

lift_definition pframe_prog :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow>  '\<alpha> prog \<Rightarrow> '\<alpha> prog " is
  "frame\<^sub>D" unfolding frame\<^sub>D_def
  by rel_auto 

lift_definition pantiframe_prog :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow>  '\<alpha> prog \<Rightarrow> '\<alpha> prog " is
  "antiframe\<^sub>D" unfolding frame\<^sub>D_def
  by rel_auto 
    
subsection{*Lift and transfer package setup*}  
declare pframe_prog.rep_eq [prog_rep_eq]
declare pantiframe_prog.rep_eq [prog_rep_eq] 
  
translations
  "_frame x P" => "CONST pframe_prog x P"
  "_frame (_salphaset (_salphamk x)) P" <= "CONST pframe_prog x P"
  "_antiframe x P" => "CONST pantiframe_prog x P"
  "_antiframe (_salphaset (_salphamk x)) P" <= "CONST pantiframe_prog x P"
  
subsection \<open>monotonicity for PROG\<close>

lift_definition mono_prog::  "('a prog \<Rightarrow> 'a prog) \<Rightarrow> bool" 
 is "Mono\<^bsub>uthy_order NDES\<^esub>"    
proof -
  fix fun1 :: "'a hrel_des \<Rightarrow> 'a hrel_des" and fun2 :: "'a hrel_des \<Rightarrow> 'a hrel_des"
  assume a1: "\<And>x. x is \<^bold>N \<Longrightarrow> (fun1 x is \<^bold>N) \<and> fun1 x = fun2 x"
  have f2: "\<forall>f fa. (\<exists>u ua. (((u::('a des, _) rel) is f) \<and> (ua is f) \<and> u \<sqsubseteq> ua) \<and> \<not> fa u \<sqsubseteq> fa ua) \<or> Mono\<^bsub>utp_order f\<^esub> fa"
    by (meson Algebraic_laws_design_aux.Mono_utp_orderI)
  obtain uu :: "('a hrel_des \<Rightarrow> 'a hrel_des) \<Rightarrow> ('a hrel_des \<Rightarrow> 'a hrel_des) \<Rightarrow> 'a hrel_des" and uua :: "('a hrel_des \<Rightarrow> 'a hrel_des) \<Rightarrow> ('a hrel_des \<Rightarrow> 'a hrel_des) \<Rightarrow> 'a hrel_des" where
    "\<forall>x0 x1. (\<exists>v2 v3. ((v2 is x1) \<and> (v3 is x1) \<and> v2 \<sqsubseteq> v3) \<and> \<not> x0 v2 \<sqsubseteq> x0 v3) = (((uu x0 x1 is x1) \<and> (uua x0 x1 is x1) \<and> uu x0 x1 \<sqsubseteq> uua x0 x1) \<and> \<not> x0 (uu x0 x1) \<sqsubseteq> x0 (uua x0 x1))"
    by moura
  then have f3: "\<forall>f fa. (uu fa f is f) \<and> (uua fa f is f) \<and> uu fa f \<sqsubseteq> uua fa f \<and> \<not> fa (uu fa f) \<sqsubseteq> fa (uua fa f) \<or> Mono\<^bsub>utp_order f\<^esub> fa"
    using f2 by presburger
  have f4: "\<forall>u. \<not> (u is \<^bold>N) \<or> (fun1 u is \<^bold>N) \<and> fun1 u = fun2 u"
    using a1 by blast
  have "\<not> Mono\<^bsub>uthy_order NDES\<^esub> fun2 \<longrightarrow> uua fun2 \<H>\<^bsub>NDES\<^esub> is \<^bold>N"
    using f3 by (metis is_Ncarrier_is_ndesigns)
  then have f5: "\<not> Mono\<^bsub>uthy_order NDES\<^esub> fun2 \<longrightarrow> (fun1 (uua fun2 \<H>\<^bsub>NDES\<^esub>) is \<^bold>N) \<and> fun1 (uua fun2 \<H>\<^bsub>NDES\<^esub>) = fun2 (uua fun2 \<H>\<^bsub>NDES\<^esub>)"
    using f4 by meson
  have "\<not> Mono\<^bsub>uthy_order NDES\<^esub> fun2 \<longrightarrow> uu fun2 \<H>\<^bsub>NDES\<^esub> is \<^bold>N"
    using f3 by (metis is_Ncarrier_is_ndesigns)
  then have f6: "\<not> Mono\<^bsub>uthy_order NDES\<^esub> fun2 \<longrightarrow> \<not> fun1 (uu fun2 \<H>\<^bsub>NDES\<^esub>) \<sqsubseteq> fun1 (uua fun2 \<H>\<^bsub>NDES\<^esub>)"
    using f5 f4 f3 by auto
  { assume "fun2 (uu fun1 \<H>\<^bsub>NDES\<^esub>) \<sqsubseteq> fun2 (uua fun1 \<H>\<^bsub>NDES\<^esub>)"
    moreover
    { assume "\<not> (fun2 (uu fun1 \<H>\<^bsub>NDES\<^esub>) \<sqsubseteq> fun2 (uua fun1 \<H>\<^bsub>NDES\<^esub>)) = (fun1 (uu fun1 \<H>\<^bsub>NDES\<^esub>) \<sqsubseteq> fun1 (uua fun1 \<H>\<^bsub>NDES\<^esub>))"
      moreover
      { assume "\<not> (fun1 (uu fun1 \<H>\<^bsub>NDES\<^esub>) is \<^bold>N) \<or> \<not> fun1 (uu fun1 \<H>\<^bsub>NDES\<^esub>) = fun2 (uu fun1 \<H>\<^bsub>NDES\<^esub>)"
        then have "\<not> (uu fun1 \<H>\<^bsub>NDES\<^esub> is \<H>\<^bsub>NDES\<^esub>) \<or> \<not> (uua fun1 \<H>\<^bsub>NDES\<^esub> is \<H>\<^bsub>NDES\<^esub>) \<or> \<not> uu fun1 \<H>\<^bsub>NDES\<^esub> \<sqsubseteq> uua fun1 \<H>\<^bsub>NDES\<^esub> \<or> fun1 (uu fun1 \<H>\<^bsub>NDES\<^esub>) \<sqsubseteq> fun1 (uua fun1 \<H>\<^bsub>NDES\<^esub>)"
          using f4 by (metis is_Ncarrier_is_ndesigns) }
      ultimately have "\<not> (uu fun1 \<H>\<^bsub>NDES\<^esub> is \<H>\<^bsub>NDES\<^esub>) \<or> \<not> (uua fun1 \<H>\<^bsub>NDES\<^esub> is \<H>\<^bsub>NDES\<^esub>) \<or> \<not> uu fun1 \<H>\<^bsub>NDES\<^esub> \<sqsubseteq> uua fun1 \<H>\<^bsub>NDES\<^esub> \<or> fun1 (uu fun1 \<H>\<^bsub>NDES\<^esub>) \<sqsubseteq> fun1 (uua fun1 \<H>\<^bsub>NDES\<^esub>)"
        using f4 by (metis (no_types) is_Ncarrier_is_ndesigns) }
    ultimately have "\<not> (uu fun1 \<H>\<^bsub>NDES\<^esub> is \<H>\<^bsub>NDES\<^esub>) \<or> \<not> (uua fun1 \<H>\<^bsub>NDES\<^esub> is \<H>\<^bsub>NDES\<^esub>) \<or> \<not> uu fun1 \<H>\<^bsub>NDES\<^esub> \<sqsubseteq> uua fun1 \<H>\<^bsub>NDES\<^esub> \<or> fun1 (uu fun1 \<H>\<^bsub>NDES\<^esub>) \<sqsubseteq> fun1 (uua fun1 \<H>\<^bsub>NDES\<^esub>)"
      by meson }
  then have "\<not> Mono\<^bsub>uthy_order NDES\<^esub> fun2 \<or> \<not> (\<not> Mono\<^bsub>uthy_order NDES\<^esub> fun1) = Mono\<^bsub>uthy_order NDES\<^esub> fun2"
    using f3 Mono_utp_orderD by blast
  then show "Mono\<^bsub>uthy_order NDES\<^esub> fun1 = Mono\<^bsub>uthy_order NDES\<^esub> fun2"
    using f6 f3 Mono_utp_orderD by blast
qed
  
lift_definition idem_prog::  "('a prog \<Rightarrow> 'a prog) \<Rightarrow> bool" 
 is "Idem\<^bsub>uthy_order NDES\<^esub>"
proof -
  fix fun1 :: "'a hrel_des \<Rightarrow> 'a hrel_des" and fun2 :: "'a hrel_des \<Rightarrow> 'a hrel_des"
  assume a1: "\<And>x. x is \<^bold>N \<Longrightarrow> (fun1 x is \<^bold>N) \<and> fun1 x = fun2 x"
  obtain uu :: "('a hrel_des \<Rightarrow> 'a hrel_des) \<Rightarrow> 'a hrel_des gorder \<Rightarrow> 'a hrel_des" where
    "\<forall>x0 x1. (\<exists>v2. v2 \<in> carrier x1 \<and> \<not> x0 (x0 v2) .=\<^bsub>x1\<^esub> x0 v2) = (uu x0 x1 \<in> carrier x1 \<and> \<not> x0 (x0 (uu x0 x1)) .=\<^bsub>x1\<^esub> x0 (uu x0 x1))"
    by moura
  then have f2: "\<forall>p f. (\<not> Idem\<^bsub>p\<^esub> f \<or> (\<forall>u. \<not> u \<in> carrier p \<or> f (f u) .=\<^bsub>p\<^esub> f u)) \<and> (Idem\<^bsub>p\<^esub> f \<or> uu f p \<in> carrier p \<and> \<not> f (f (uu f p)) .=\<^bsub>p\<^esub> f (uu f p))"
    by (metis (no_types) idempotent_def)
  have f3: "\<lbrakk>\<H>\<^bsub>NDES::(NDES, 'a des) uthy\<^esub>\<rbrakk>\<^sub>H = carrier (uthy_order NDES)"
    by simp
  moreover
  { assume "\<not> Idem\<^bsub>uthy_order NDES\<^esub> fun2"
    then have "\<not> Idem\<^bsub>uthy_order NDES\<^esub> fun2 \<and> \<not> fun2 (fun2 (uu fun2 (uthy_order NDES))) .=\<^bsub>uthy_order NDES\<^esub> fun2 (uu fun2 (uthy_order NDES))"
      using f2 by meson
    then have "\<not> (\<not> Idem\<^bsub>uthy_order NDES\<^esub> fun1) = Idem\<^bsub>uthy_order NDES\<^esub> fun2"
      using f3 f2 a1 by (metis is_Ncarrier_is_ndesigns mem_Collect_eq) }
  ultimately show "Idem\<^bsub>uthy_order NDES\<^esub> fun1 = Idem\<^bsub>uthy_order NDES\<^esub> fun2"
    using f2 a1 by (metis is_Ncarrier_is_ndesigns mem_Collect_eq)
qed
declare mono_prog.rep_eq[prog_rep_eq]
declare idem_prog.rep_eq[prog_rep_eq]  
  
 
subsection{*Rep Abs and normal designs*}   

lemma Abs_prog_Rep_prog_ndesign:"\<lbrakk>Abs_prog (\<^bold>N P)\<rbrakk>\<^sub>p = (\<^bold>N P)" 
  by (simp add: Abs_prog_inverse H1_H3_idempotent Healthy_def')

lemmas Abs_prog_Rep_prog_Ncarrier= 
  Abs_prog_Rep_prog_ndesign[folded Ncarrier_ndesigns]  
         
end
