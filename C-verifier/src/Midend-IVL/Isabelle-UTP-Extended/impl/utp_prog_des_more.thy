section {* Imperative Programs *}
  
theory utp_prog_des_more
  imports 
    "../../Isabelle-UTP/impl/utp_prog"
begin

section {*More Operators *}

subsection{*Conditional*}
 
lift_definition pcond_des :: "'\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" ("bif (_)/ then (_) else (_) eif") is 
 "IfD" by (metis ndesign_H1_H3 ndesign_dcond ndesign_form)
    
declare pcond_des.rep_eq [prog_rep_eq]
  
subsection{*assert and assume*}

abbreviation passume_des :: "'\<alpha> cond \<Rightarrow> '\<alpha> prog"  
  where "passume_des c \<equiv> (bif c then skip else magic eif)"

abbreviation passert_des :: "'\<alpha> upred \<Rightarrow> '\<alpha> prog" 
  where "passert_des c \<equiv> (bif c then skip else abort eif)"
    
subsection{*Scoping*}
 
lift_definition pblock_des ::
  "'\<alpha> prog \<Rightarrow> '\<alpha> prog \<Rightarrow> ('\<alpha> des  \<times> '\<alpha>  des \<Rightarrow> '\<alpha> des \<times> '\<alpha> des  \<Rightarrow> '\<alpha> prog) \<Rightarrow>
      ('\<alpha> des  \<times> '\<alpha> des  \<Rightarrow> '\<alpha> des  \<times> '\<alpha> des \<Rightarrow> '\<alpha> prog) \<Rightarrow> '\<alpha> prog" 
is blockD oops
  
subsection{*Iterations*}    
    
lift_definition pwhile_inv_des :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog " is 
  "While_inv_ndes" unfolding While_inv_ndes_def While_lfp_ndes_def
  by simp
    
declare pwhile_inv_des.rep_eq [prog_rep_eq]
 
end