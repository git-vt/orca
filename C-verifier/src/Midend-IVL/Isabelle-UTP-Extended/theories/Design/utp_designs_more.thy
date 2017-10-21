theory utp_designs_more
imports   "../../../Isabelle-UTP/theories/utp_designs"
          "../../hoare/AlgebraicLaws/Rel&Des/Algebraic_Laws_AUX"
begin

section {*Syntax setup*}
syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>D")
translations
  "_svid_st_alpha" => "CONST des_vars_child_lens"
 
section {*Type projections and injections*}

subsection {*Substitution lift and drop*}

abbreviation lift_rel_usubst_des ("\<lceil>_\<rceil>\<^sub>S\<^sub>D")
where "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<equiv> \<sigma> \<oplus>\<^sub>s (\<Sigma>\<^sub>D \<times>\<^sub>L \<Sigma>\<^sub>D)"

abbreviation lift_usubst_des ("\<lceil>_\<rceil>\<^sub>s\<^sub>D")
where "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>D \<equiv> \<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s\<rceil>\<^sub>S\<^sub>D"

abbreviation drop_rel_usubst_des ("\<lfloor>_\<rfloor>\<^sub>S\<^sub>D")
where "\<lfloor>\<sigma>\<rfloor>\<^sub>S\<^sub>D \<equiv> \<sigma> \<restriction>\<^sub>s (\<Sigma>\<^sub>D \<times>\<^sub>L \<Sigma>\<^sub>D)"

abbreviation drop_usubst_des ("\<lfloor>_\<rfloor>\<^sub>s\<^sub>D")
where "\<lfloor>\<sigma>\<rfloor>\<^sub>s\<^sub>D \<equiv> \<lfloor>\<lfloor>\<sigma>\<rfloor>\<^sub>S\<^sub>D\<rfloor>\<^sub>s"

subsection {*UTP-Relations drop*}

abbreviation drop_pre_uexpr_des ("\<lfloor>_\<rfloor>\<^sub><\<^sub>D")
where "\<lfloor>P\<rfloor>\<^sub><\<^sub>D \<equiv> \<lfloor>\<lfloor>P\<rfloor>\<^sub>D\<rfloor>\<^sub><"

abbreviation drop_post_uexpr_des ("\<lfloor>_\<rfloor>\<^sub>>\<^sub>D")
where "\<lfloor>P\<rfloor>\<^sub>>\<^sub>D \<equiv> \<lfloor>\<lfloor>P\<rfloor>\<^sub>D\<rfloor>\<^sub>>"    

section {*Normal Design setup*}

abbreviation ndesign_lfp :: "('\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des) \<Rightarrow> '\<alpha> hrel_des" ("\<mu>\<^sub>N") where
"\<mu>\<^sub>N F \<equiv> \<^bold>\<mu>\<^bsub>NDES\<^esub> F"

abbreviation ndesign_gfp :: "('\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des) \<Rightarrow> '\<alpha> hrel_des" ("\<nu>\<^sub>N") where
"\<nu>\<^sub>N F \<equiv> \<^bold>\<nu>\<^bsub>NDES\<^esub> F"

syntax
  "_ndmu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu>\<^sub>N _ \<bullet> _" [0, 10] 10)
  "_ndnu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<nu>\<^sub>N _ \<bullet> _" [0, 10] 10)

translations
  "\<mu>\<^sub>N X \<bullet> P" == "\<^bold>\<mu>\<^bsub>CONST NDES\<^esub> (\<lambda> X. P)"
  "\<nu>\<^sub>N X \<bullet> P" == "\<^bold>\<nu>\<^bsub>CONST NDES\<^esub> (\<lambda> X. P)"
  
section{*Control flow statements*}    
  
subsection{*SKIP design*}  

abbreviation skip_des :: "('\<alpha>) hrel_des" ("SKIP\<^sub>D")
where "SKIP\<^sub>D \<equiv> skip_d"

subsection{*assign design*}
  
term "x :=\<^sub>D s"

subsection{*Conditional design*}

abbreviation IfD :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_des \<Rightarrow> ('\<alpha>) hrel_des \<Rightarrow> ('\<alpha>) hrel_des" ("bif\<^sub>D (_)/ then (_) else (_) eif")
where "bif\<^sub>D b then P else Q eif \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>D\<^sub>< \<triangleright> Q)"

subsection{*assert and assume*}

definition assume_des :: "'\<alpha> upred \<Rightarrow> ('\<alpha>) hrel_des" ("_\<^sup>\<top>\<^sup>D" [999] 999) 
where [urel_defs]: "assume_des c \<equiv> (bif\<^sub>D c then SKIP\<^sub>D else \<top>\<^sub>D eif)"

definition assert_des :: "'\<alpha> upred \<Rightarrow> ('\<alpha>) hrel_des" ("_\<^sub>\<bottom>\<^sub>D" [999] 999) 
where [urel_defs]: "assert_des c \<equiv> (bif\<^sub>D c then SKIP\<^sub>D else \<bottom>\<^sub>D eif)"

subsection{*Scoping*}

definition blockD ("bob\<^sub>D INIT (_) BODY /(_) RESTORE /(_) RETURN/(_) eob") 
where [urel_defs]:
  "bob\<^sub>D INIT init BODY body RESTORE restore RETURN return eob= 
    Abs_uexpr (\<lambda>(s, s'). 
        \<lbrakk>init ;; body ;; 
         Abs_uexpr (\<lambda>(t, t').\<lbrakk>restore (s, s') (t, t');; return(s, s') (t, t')\<rbrakk>\<^sub>e (t, t'))\<rbrakk>\<^sub>e (s, s'))" 
 
subsection{*Design Iterations*}
  
definition While_gfp_des :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sup>\<top>\<^sup>D _ do _ od")
where "while\<^sup>\<top>\<^sup>D b do B od = (\<nu>\<^sub>D X \<bullet> bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)"

definition While_lfp_des :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sub>\<bottom>\<^sub>D _ do _ od") 
where "while\<^sub>\<bottom>\<^sub>D b do B od =  (\<mu>\<^sub>D X \<bullet> bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)"

purge_notation while_top ("while _ do _ od")

abbreviation While_bot_des :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sub>D _ do _ od") 
where "while\<^sub>D b do B od \<equiv> while\<^sub>\<bottom>\<^sub>D b do B od"

subsection{*While-loop inv*}
text {*While loops with invariant decoration*}

purge_notation while_inv ("while _ invr _ do _ od" 71)

definition While_inv_des :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sub>D _ invr _ do _ od") 
where "while\<^sub>D b invr p do S od = while\<^sub>D b do S od"

declare While_gfp_des_def [urel_defs]
declare While_inv_des_def [urel_defs]
declare While_lfp_des_def [urel_defs]

subsection{*Normal Design Iterations*}   

  
definition While_gfp_ndes :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sup>\<top>\<^sup>N _ do _ od")
where "while\<^sup>\<top>\<^sup>N b do B od = (\<nu>\<^sub>N X \<bullet> bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)"

definition While_lfp_ndes :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sub>\<bottom>\<^sub>N _ do _ od") 
where "while\<^sub>\<bottom>\<^sub>N b do B od =  (\<mu>\<^sub>N X \<bullet> bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)"

abbreviation While_bot_ndes :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sub>N _ do _ od") 
where "while\<^sub>N b do B od \<equiv> while\<^sub>\<bottom>\<^sub>N b do B od"

subsection{*While-loop inv*}
text {*While loops with invariant decoration*}

purge_notation while_inv ("while _ invr _ do _ od" 71)

definition While_inv_ndes :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sub>N _ invr _ do _ od") 
where "while\<^sub>N b invr p do S od = while\<^sub>N b do S od"

declare While_gfp_ndes_def [urel_defs]
declare While_inv_ndes_def [urel_defs]
declare While_lfp_ndes_def [urel_defs]

end