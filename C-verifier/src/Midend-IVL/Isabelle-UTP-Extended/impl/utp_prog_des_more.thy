section {* Imperative Programs *}
  
theory utp_prog_des_more
  imports 
    "../../Isabelle-UTP/impl/utp_prog"
begin

section {*More Operators *}

subsection{*Conditional*}
 
lift_definition pcond_prog :: "'\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" ("IF (_)/ THEN (_) ELSE (_) FI") 
  is "IfD" by (metis ndesign_H1_H3 ndesign_dcond ndesign_form)
    
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
    
lift_definition pwhile_prog :: "'\<alpha> cond \<Rightarrow>  '\<alpha> prog \<Rightarrow> '\<alpha> prog " ("WHILE (_)/ DO (_) OD")
  is "While_bot_ndes" unfolding While_lfp_ndes_def
  by simp

definition pwhile_inv_prog :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog " ("INVR (_)/ WHILE (_)/ DO (_) OD")   
where "INVR I WHILE b DO P OD = WHILE b DO P OD"  

definition pwhile_inv_vrt_prog :: "'\<alpha> cond \<Rightarrow>  ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> cond  \<Rightarrow>'\<alpha> prog \<Rightarrow> '\<alpha> prog " ("INVR (_)/ VRT (_)/ WHILE (_)/ DO (_) OD")   
  where "INVR I VRT E WHILE b DO P OD = WHILE b DO P OD"
    
declare pwhile_prog.rep_eq [prog_rep_eq]
declare pwhile_inv_prog_def [prog_rep_eq]
declare pwhile_inv_vrt_prog_def [prog_rep_eq]



lemma Abs_prog_Rep_prog_ndesign:"\<lbrakk>Abs_prog (\<^bold>N P)\<rbrakk>\<^sub>p = (\<^bold>N P)" 
  by (simp add: Abs_prog_inverse H1_H3_idempotent Healthy_def')

lemmas Abs_prog_Rep_prog_Ncarrier= 
  Abs_prog_Rep_prog_ndesign[folded Ncarrier_ndesigns]   
end