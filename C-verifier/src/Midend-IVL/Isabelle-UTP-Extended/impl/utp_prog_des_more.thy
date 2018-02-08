(*****************************************************************************************)
(* Orca: A Functional Correctness Verifier for Imperative Programs Based on Isabelle/UTP *)
(*                                                                                       *)
(* Copyright (c) 2016-2018 Virginia Tech, USA                                            *)
(* This software may be distributed and modified according to the terms of               *)
(* the GNU Lesser General Public License version 3.0 or any later version.               *)
(* Note that NO WARRANTY is provided.                                                    *)
(* See CONTRIBUTORS, LICENSE and CITATION files for details.                             *)
(*****************************************************************************************)

section {* Imperative Programs *}
  
theory utp_prog_des_more
  imports 
    "../../Isabelle-UTP/impl/utp_prog"
begin

section {*More Operators *}

subsection{*Conditional*}
 
lift_definition pcond_prog :: "'\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" ("IF (_)/ THEN (_) ELSE (_) FI") 
  is "IfD" 
  by (simp add: H1_H3_impl_H2 H3_unrest_out_alpha if_d_H1_H3_intro)
    
declare pcond_prog.rep_eq [prog_rep_eq]
  
subsection{*assert and assume*}

abbreviation passume_prog :: "'\<alpha> cond \<Rightarrow> '\<alpha> prog" ("_\<^sup>\<top>\<^sup>P")  
  where "passume_prog c \<equiv> (IF c THEN SKIP ELSE magic FI)"

abbreviation passert_prog :: "'\<alpha> upred \<Rightarrow> '\<alpha> prog" ("_\<^sub>\<bottom>\<^sub>P")
  where "passert_prog c \<equiv> (IF c THEN SKIP ELSE abort FI)"
    
subsection{*Scoping*}
 
lift_definition pblock_prog ::
  "'\<alpha> prog \<Rightarrow> '\<alpha> prog \<Rightarrow> ('\<alpha> des  \<times> '\<alpha>  des \<Rightarrow> '\<alpha> des \<times> '\<alpha> des  \<Rightarrow> '\<alpha> prog) \<Rightarrow>
      ('\<alpha> des  \<times> '\<alpha> des  \<Rightarrow> '\<alpha> des  \<times> '\<alpha> des \<Rightarrow> '\<alpha> prog) \<Rightarrow> '\<alpha> prog" 
is blockD oops

subsection{*Recursion*}    
 
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
 
subsection{*Rep Abs and normal designs*}   

lemma Abs_prog_Rep_prog_ndesign:"\<lbrakk>Abs_prog (\<^bold>N P)\<rbrakk>\<^sub>p = (\<^bold>N P)" 
  by (simp add: Abs_prog_inverse H1_H3_idempotent Healthy_def')

lemmas Abs_prog_Rep_prog_Ncarrier= 
  Abs_prog_Rep_prog_ndesign[folded Ncarrier_ndesigns]  
         
end
