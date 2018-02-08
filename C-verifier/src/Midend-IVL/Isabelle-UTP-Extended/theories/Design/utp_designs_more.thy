(*****************************************************************************************)
(* Orca: A Functional Correctness Verifier for Imperative Programs Based on Isabelle/UTP *)
(*                                                                                       *)
(* Copyright (c) 2016-2018 Virginia Tech, USA                                            *)
(*               2016-2018 Technische Universität München, Germany                       *)
(*               2016-2018 University of York, UK                                        *)
(*               2016-2018 Université Paris-Saclay, Univ. Paris-Sud, France              *)
(* This software may be distributed and modified according to the terms of               *)
(* the GNU Lesser General Public License version 3.0 or any later version.               *)
(* Note that NO WARRANTY is provided.                                                    *)
(* See CONTRIBUTORS, LICENSE and CITATION files for details.                             *)
(*****************************************************************************************)

theory utp_designs_more
imports   "../../AlgebraicLaws/Algebraic_Laws_aux"
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

subsection {*Syntax directed laws on operators of designs*}

lemma lift_pre_des_uconj_distribute[simp]:
  "(\<lceil>p\<rceil>\<^sub>D\<^sub>< \<and> \<lceil>q\<rceil>\<^sub>D\<^sub><) = \<lceil>p \<and> q\<rceil>\<^sub>D\<^sub><"
  by rel_simp

lemma lift_post_des_uconj_distribute[simp]:
  "(\<lceil>p\<rceil>\<^sub>D\<^sub>> \<and> \<lceil>q\<rceil>\<^sub>D\<^sub>>) = \<lceil>p \<and> q\<rceil>\<^sub>D\<^sub>>"
  by rel_simp

lemma lift_pre_des_udisj_distribute[simp]:
  "(\<lceil>p\<rceil>\<^sub>D\<^sub>< \<or> \<lceil>q\<rceil>\<^sub>D\<^sub><) = \<lceil>p \<or> q\<rceil>\<^sub>D\<^sub><"
  by rel_simp

lemma lift_post_des_udisj_distribute[simp]:
  "(\<lceil>p\<rceil>\<^sub>D\<^sub>> \<or> \<lceil>q\<rceil>\<^sub>D\<^sub>>) = \<lceil>p \<or> q\<rceil>\<^sub>D\<^sub>>"
  by rel_simp

lemma lift_pre_des_uimpl_distribute[simp]:
  "(\<lceil>p\<rceil>\<^sub>D\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>D\<^sub><) = \<lceil>p \<Rightarrow> q\<rceil>\<^sub>D\<^sub><"
  by rel_simp

lemma lift_post_des_uimpl_distribute[simp]:
  "(\<lceil>p\<rceil>\<^sub>D\<^sub>> \<Rightarrow> \<lceil>q\<rceil>\<^sub>D\<^sub>>) = \<lceil>p \<Rightarrow> q\<rceil>\<^sub>D\<^sub>>"
  by rel_simp
    
lemma lift_pre_des_uiff_distribute[simp]:
  "(\<lceil>p\<rceil>\<^sub>D\<^sub>< \<Leftrightarrow> \<lceil>q\<rceil>\<^sub>D\<^sub><) = \<lceil>p \<Leftrightarrow> q\<rceil>\<^sub>D\<^sub><"
  by rel_simp

lemma lift_post_des_uiff_distribute[simp]:
  "(\<lceil>p\<rceil>\<^sub>D\<^sub>> \<Leftrightarrow> \<lceil>q\<rceil>\<^sub>D\<^sub>>) = \<lceil>p \<Leftrightarrow> q\<rceil>\<^sub>D\<^sub>>"
  by rel_simp    

lemma lift_pre_des_ueq_distribute[simp]:
  "(\<lceil>p\<rceil>\<^sub>D\<^sub>< =\<^sub>u \<lceil>q\<rceil>\<^sub>D\<^sub><) = \<lceil>p =\<^sub>u q\<rceil>\<^sub>D\<^sub><"
  by rel_simp

lemma lift_post_des_ueq_distribute[simp]:
  "(\<lceil>p\<rceil>\<^sub>D\<^sub>> =\<^sub>u \<lceil>q\<rceil>\<^sub>D\<^sub>>) = \<lceil>p =\<^sub>u q\<rceil>\<^sub>D\<^sub>>"
  by rel_simp 

subsection {*Syntax directed laws on drop operators of designs*}

lemma drop_pre_des_uconj_distribute[simp]:
  "(\<lfloor>p\<rfloor>\<^sub><\<^sub>D \<and> \<lfloor>q\<rfloor>\<^sub><\<^sub>D) = \<lfloor>p \<and> q\<rfloor>\<^sub><\<^sub>D"
  by rel_simp

lemma drop_post_des_uconj_distribute[simp]:
  "(\<lfloor>p\<rfloor>\<^sub>>\<^sub>D \<and> \<lfloor>q\<rfloor>\<^sub>>\<^sub>D) = \<lfloor>p \<and> q\<rfloor>\<^sub>>\<^sub>D"
  by rel_simp

lemma drop_pre_des_udisj_distribute[simp]:
  "(\<lfloor>p\<rfloor>\<^sub><\<^sub>D \<or> \<lfloor>q\<rfloor>\<^sub><\<^sub>D) = \<lfloor>p \<or> q\<rfloor>\<^sub><\<^sub>D "
  by rel_simp

lemma drop_post_des_udisj_distribute[simp]:
  "(\<lfloor>p\<rfloor>\<^sub>>\<^sub>D \<or> \<lfloor>q\<rfloor>\<^sub>>\<^sub>D) = \<lfloor>p \<or> q\<rfloor>\<^sub>>\<^sub>D"
  by rel_simp

lemma drop_pre_des_uimpl_distribute[simp]:
  "(\<lfloor>p\<rfloor>\<^sub><\<^sub>D \<Rightarrow> \<lfloor>q\<rfloor>\<^sub><\<^sub>D) = \<lfloor>p \<Rightarrow> q\<rfloor>\<^sub><\<^sub>D "
  by rel_simp

lemma drop_post_des_uimpl_distribute[simp]:
  "(\<lfloor>p\<rfloor>\<^sub>>\<^sub>D \<Rightarrow> \<lfloor>q\<rfloor>\<^sub>>\<^sub>D) = \<lfloor>p \<Rightarrow> q\<rfloor>\<^sub>>\<^sub>D"
  by rel_simp
    
lemma drop_pre_des_uiff_distribute[simp]:
  "(\<lfloor>p\<rfloor>\<^sub><\<^sub>D \<Leftrightarrow> \<lfloor>q\<rfloor>\<^sub><\<^sub>D) = \<lfloor>p \<Leftrightarrow> q\<rfloor>\<^sub><\<^sub>D"
  by rel_simp

lemma drop_post_des_uiff_distribute[simp]:
  "(\<lfloor>p\<rfloor>\<^sub>>\<^sub>D \<Leftrightarrow> \<lfloor>q\<rfloor>\<^sub>>\<^sub>D) = \<lfloor>p \<Leftrightarrow> q\<rfloor>\<^sub>>\<^sub>D"
  by rel_simp    

lemma drop_pre_des_ueq_distribute[simp]:
  "(\<lfloor>p\<rfloor>\<^sub><\<^sub>D =\<^sub>u \<lfloor>q\<rfloor>\<^sub><\<^sub>D) = \<lfloor>p =\<^sub>u q\<rfloor>\<^sub><\<^sub>D"
  by rel_simp

lemma drop_post_des_ueq_distribute[simp]:
  "(\<lfloor>p\<rfloor>\<^sub>>\<^sub>D =\<^sub>u \<lfloor>q\<rfloor>\<^sub>>\<^sub>D) = \<lfloor>p =\<^sub>u q\<rfloor>\<^sub>>\<^sub>D"
  by rel_simp 
    
section {*Normal design syntax setup*}

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
 
subsection{*Design iterations*}

(*The generic from_until_loop definition is from the paper called :
  Loop invariants: analysis, classification, and examples*)
  
definition from_until_gfp_des :: 
  "'\<alpha> hrel_des \<Rightarrow>'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("from\<^sup>\<top>\<^sup>D _ until _ do _ od") 
where "from\<^sup>\<top>\<^sup>D init until exit do body od =  
       init ;; (\<nu>\<^sub>D X \<bullet> bif\<^sub>D \<not> exit then (body ;; X) else SKIP\<^sub>D eif)" 
    
definition from_until_lfp_des :: 
  "'\<alpha> hrel_des \<Rightarrow>'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("from\<^sub>\<bottom>\<^sub>D _ until _ do _ od") 
where "from\<^sub>\<bottom>\<^sub>D init until exit do body od =  
       init ;; (\<mu>\<^sub>D X \<bullet> bif\<^sub>D \<not> exit then (body ;; X) else SKIP\<^sub>D eif)" 
    
definition while_gfp_des :: 
  "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sup>\<top>\<^sup>D _ do _ od")
where "while\<^sup>\<top>\<^sup>D b do body od = from\<^sup>\<top>\<^sup>D SKIP\<^sub>D until \<not> b do body od"

definition while_lfp_des :: 
  "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sub>\<bottom>\<^sub>D _ do _ od") 
where "while\<^sub>\<bottom>\<^sub>D b do body od = from\<^sub>\<bottom>\<^sub>D SKIP\<^sub>D until \<not> b do body od"

definition do_while_gfp_des :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des" ("do _ while\<^sup>\<top>\<^sup>D _ od")
where "do body while\<^sup>\<top>\<^sup>D b od = from\<^sup>\<top>\<^sup>D body until \<not> b do body od"

definition do_while_lfp_des :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow>  '\<alpha> hrel_des" ("do _ while\<^sub>\<bottom>\<^sub>D _ od") 
  where "do body while\<^sub>\<bottom>\<^sub>D b od = from\<^sub>\<bottom>\<^sub>D body until \<not> b do body od"
    
definition for_gfp_des :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("for\<^sup>\<top>\<^sup>D '(_,_,_') do _ od")
where "for\<^sup>\<top>\<^sup>D (init, b, incr) do body od = from\<^sup>\<top>\<^sup>D init until \<not> b do body ;; incr od"

definition for_lfp_des :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("for\<^sub>\<bottom>\<^sub>D '(_,_,_') do _ od")
where "for\<^sub>\<bottom>\<^sub>D (init, b, incr) do body od = from\<^sub>\<bottom>\<^sub>D init until \<not> b do body ;; incr od"
  
text {*Iterations with invariant decoration*}

definition from_until_lfp_invr_des :: 
  "'\<alpha> hrel_des \<Rightarrow>'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("from\<^sub>\<bottom>\<^sub>D _ invr _ until _ do _ od") 
where "from\<^sub>\<bottom>\<^sub>D init invr invar until exit do body od = from\<^sub>\<bottom>\<^sub>D init until exit do body od"  

definition from_until_gfp_invr_des :: 
  "'\<alpha> hrel_des \<Rightarrow>'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("from\<^sup>\<top>\<^sup>D _ invr _ until _ do _ od") 
where "from\<^sup>\<top>\<^sup>D init invr invar until exit do body od =  from\<^sup>\<top>\<^sup>D init until exit do body od"  

definition while_lfp_invr_des :: 
  "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sub>\<bottom>\<^sub>D _ invr _ do _ od") 
where "while\<^sub>\<bottom>\<^sub>D b invr invar do body od = while\<^sub>\<bottom>\<^sub>D b do body od"

definition while_gfp_invr_des :: 
  "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sup>\<top>\<^sup>D _ invr _ do _ od") 
where "while\<^sup>\<top>\<^sup>D b invr invar do body od = while\<^sup>\<top>\<^sup>D b do body od"

definition do_while_gfp_invr_des :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des" ("do _ while\<^sup>\<top>\<^sup>D _ invr _ od")
where "do body while\<^sup>\<top>\<^sup>D b invr invar od = from\<^sup>\<top>\<^sup>D body until \<not> b do body od"

definition do_while_lfp_invr_des :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des" ("do _ while\<^sub>\<bottom>\<^sub>D _ invr _ od") 
where "do body while\<^sub>\<bottom>\<^sub>D b invr invar od = from\<^sub>\<bottom>\<^sub>D body until \<not> b do body od"
    
definition for_gfp_invr_des :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow>  '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("for\<^sup>\<top>\<^sup>D '(_,_,_') invr _ do _ od")
where "for\<^sup>\<top>\<^sup>D (init, b, incr) invr invar do body od = from\<^sup>\<top>\<^sup>D init until \<not> b do body ;; incr od"

definition for_lfp_invr_des :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow>  '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("for\<^sub>\<bottom>\<^sub>D '(_,_,_') invr _ do _ od")
where "for\<^sub>\<bottom>\<^sub>D (init, b, incr) invr invar do body od = from\<^sub>\<bottom>\<^sub>D init until \<not> b do body ;; incr od"

text {*Iterations with invariant and variant decoration*}
  
definition from_until_lfp_invr_vrt_des :: 
  "'\<alpha> hrel_des \<Rightarrow>'\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("from\<^sub>\<bottom>\<^sub>D _ invr _ vrt _ until _ do _ od") 
where "from\<^sub>\<bottom>\<^sub>D init invr invar vrt vari until exit do body od = from\<^sub>\<bottom>\<^sub>D init until exit do body od"

definition from_until_gfp_invr_vrt_des :: 
  "'\<alpha> hrel_des \<Rightarrow>'\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("from\<^sup>\<top>\<^sup>D _ invr _ vrt _ until _ do _ od") 
where "from\<^sup>\<top>\<^sup>D init invr invar vrt vari until exit do body od = from\<^sup>\<top>\<^sup>D init until exit do body od"
    
definition while_lfp_invr_vrt_des :: 
  "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow>'\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sub>\<bottom>\<^sub>D _ invr _ vrt _ do _ od") 
where "while\<^sub>\<bottom>\<^sub>D b invr invar vrt vari do S od = while\<^sub>\<bottom>\<^sub>D b do S od"

definition while_gfp_invr_vrt_des :: 
  "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow>'\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sup>\<top>\<^sup>D _ invr _ vrt _ do _ od") 
where "while\<^sup>\<top>\<^sup>D b invr invar vrt vari do S od = while\<^sup>\<top>\<^sup>D b do S od"

definition do_while_gfp_invr_vrt_des :: 
   "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel_des" ("do _ while\<^sup>\<top>\<^sup>D _ invr _ vrt _ od")
where "do body while\<^sup>\<top>\<^sup>D b invr invar vrt vari od = from\<^sup>\<top>\<^sup>D body until \<not> b do body od"

definition do_while_lfp_invr_vrt_des :: 
   "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel_des" ("do _ while\<^sub>\<bottom>\<^sub>D _ invr _ vrt _ od") 
where "do body while\<^sub>\<bottom>\<^sub>D b invr invar vrt vari od = from\<^sub>\<bottom>\<^sub>D body until \<not> b do body od"

definition for_gfp_invr_vrt_des :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("for\<^sup>\<top>\<^sup>D '(_,_,_') invr _ vrt_ do _ od")
where "for\<^sup>\<top>\<^sup>D (init, b, incr) invr invar vrt vari do body od = from\<^sup>\<top>\<^sup>D init until \<not> b do body ;; incr od"

definition for_lfp_invr_vrt_des :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("for\<^sub>\<bottom>\<^sub>D '(_,_,_') invr _ vrt _ do _ od")
where "for\<^sub>\<bottom>\<^sub>D (init, b, incr) invr invar vrt vari do body od = from\<^sub>\<bottom>\<^sub>D init until \<not> b do body ;; incr od"
  
subsection{*Normal design iterations*}   

(*The generic from_until_loop definition is from the paper called :
  Loop invariants: analysis, classification, and examples*)
  
definition from_until_gfp_ndes :: "'\<alpha> hrel_des \<Rightarrow>'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("from\<^sup>\<top>\<^sup>N _ until _ do _ od") 
  where "from\<^sup>\<top>\<^sup>N init until exit do body od =  
         init ;; (\<nu>\<^sub>N X \<bullet> bif\<^sub>D \<not> exit then (body ;; X) else SKIP\<^sub>D eif)" 
  
definition from_until_lfp_ndes :: "'\<alpha> hrel_des \<Rightarrow>'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("from\<^sub>\<bottom>\<^sub>N _ until _ do _ od") 
  where "from\<^sub>\<bottom>\<^sub>N init until exit do body od =  
         init ;; (\<mu>\<^sub>N X \<bullet> bif\<^sub>D \<not> exit then (body ;; X) else SKIP\<^sub>D eif)" 

definition while_gfp_ndes :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sup>\<top>\<^sup>N _ do _ od")
where "while\<^sup>\<top>\<^sup>N b do body od = from\<^sup>\<top>\<^sup>N SKIP\<^sub>D  until \<not> b do body od"

definition while_lfp_ndes :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sub>\<bottom>\<^sub>N _ do _ od") 
  where "while\<^sub>\<bottom>\<^sub>N b do body od =  from\<^sub>\<bottom>\<^sub>N SKIP\<^sub>D  until \<not> b do body od"
    
definition do_while_gfp_ndes :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des" ("do _ while\<^sup>\<top>\<^sup>N _ od")
where "do body while\<^sup>\<top>\<^sup>N b od = from\<^sup>\<top>\<^sup>N body until \<not> b do body od"

definition do_while_lfp_ndes :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow>  '\<alpha> hrel_des" ("do _ while\<^sub>\<bottom>\<^sub>N _ od") 
  where "do body while\<^sub>\<bottom>\<^sub>N b od = from\<^sub>\<bottom>\<^sub>N body until \<not> b do body od"
    
definition for_gfp_ndes :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("for\<^sup>\<top>\<^sup>N '(_,_,_') do _ od")
where "for\<^sup>\<top>\<^sup>N (init, b, incr) do body od = from\<^sup>\<top>\<^sup>N init until \<not> b do body ;; incr od"

definition for_lfp_ndes :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("for\<^sub>\<bottom>\<^sub>N '(_,_,_') do _ od")
where "for\<^sub>\<bottom>\<^sub>N (init, b, incr) do body od = from\<^sub>\<bottom>\<^sub>N init until \<not> b do body ;; incr od"
    
text {*Iterations with invariant decoration*}

definition from_until_lfp_invr_ndes :: "'\<alpha> hrel_des \<Rightarrow>'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("from\<^sub>\<bottom>\<^sub>N _ invr _ until _ do _ od") 
  where "from\<^sub>\<bottom>\<^sub>N init invr invar until exit do body od =  from\<^sub>\<bottom>\<^sub>N init until exit do body od"

definition from_until_gfp_invr_ndes :: "'\<alpha> hrel_des \<Rightarrow>'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("from\<^sup>\<top>\<^sup>N _ invr _ until _ do _ od") 
  where "from\<^sup>\<top>\<^sup>N init invr invar until exit do body od =  from\<^sup>\<top>\<^sup>N init until exit do body od"

definition while_lfp_invr_ndes :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sub>\<bottom>\<^sub>N _ invr _ do _ od") 
where "while\<^sub>\<bottom>\<^sub>N b invr invar do body od = while\<^sub>\<bottom>\<^sub>N b do body od"

definition while_gfp_invr_ndes :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sup>\<top>\<^sup>N _ invr _ do _ od") 
where "while\<^sup>\<top>\<^sup>N b invr invar do body od = while\<^sup>\<top>\<^sup>N b do body od"

definition do_while_gfp_invr_ndes :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des" ("do _ while\<^sup>\<top>\<^sup>N _ invr _ od")
where "do body while\<^sup>\<top>\<^sup>N b invr invar od = from\<^sup>\<top>\<^sup>N body until \<not> b do body od"

definition do_while_lfp_invr_ndes :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des" ("do _ while\<^sub>\<bottom>\<^sub>N _ invr _ od") 
where "do body while\<^sub>\<bottom>\<^sub>N b invr invar od = from\<^sub>\<bottom>\<^sub>N body until \<not> b do body od"  
  
definition for_gfp_invr_ndes :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow>  '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("for\<^sup>\<top>\<^sup>N '(_,_,_') invr _ do _ od")
where "for\<^sup>\<top>\<^sup>N (init, b, incr) invr invar do body od = from\<^sup>\<top>\<^sup>N init until \<not> b do body ;; incr od"

definition for_lfp_invr_ndes :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow>  '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("for\<^sub>\<bottom>\<^sub>N '(_,_,_') invr _ do _ od")
where "for\<^sub>\<bottom>\<^sub>N (init, b, incr) invr invar do body od = from\<^sub>\<bottom>\<^sub>N init until \<not> b do body ;; incr od"
  
text {*Iterations with invariant and variant decoration*}
  
definition from_until_lfp_invr_vrt_ndes :: 
  "'\<alpha> hrel_des \<Rightarrow>'\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("from\<^sub>\<bottom>\<^sub>N _ invr _ vrt _ until _ do _ od") 
  where "from\<^sub>\<bottom>\<^sub>N init invr invar vrt vari until exit do body od =  from\<^sub>\<bottom>\<^sub>N init until exit do body od"

definition from_until_gfp_invr_vrt_ndes :: 
  "'\<alpha> hrel_des \<Rightarrow>'\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("from\<^sup>\<top>\<^sup>N _ invr _ vrt _ until _ do _ od") 
  where "from\<^sup>\<top>\<^sup>N init invr invar vrt vari until exit do body od =  from\<^sup>\<top>\<^sup>N init until exit do body od"
    
definition while_lfp_invr_vrt_ndes :: 
  "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sub>\<bottom>\<^sub>N _ invr _ vrt _ do _ od") 
where "while\<^sub>\<bottom>\<^sub>N b invr invar vrt vari do body od = while\<^sub>\<bottom>\<^sub>N b do body od"

definition while_gfp_invr_vrt_ndes :: 
  "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("while\<^sup>\<top>\<^sup>N _ invr _ vrt _ do _ od") 
where "while\<^sup>\<top>\<^sup>N b invr invar vrt vari do body od = while\<^sup>\<top>\<^sup>N b do body od"

definition do_while_gfp_invr_vrt_ndes :: 
   "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel_des" ("do _ while\<^sup>\<top>\<^sup>N _ invr _ vrt _ od")
where "do body while\<^sup>\<top>\<^sup>N b invr invar vrt vari od = from\<^sup>\<top>\<^sup>N body until \<not> b do body od"

definition do_while_lfp_invr_vrt_ndes :: 
   "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel_des" ("do _ while\<^sub>\<bottom>\<^sub>N _ invr _ vrt _ od") 
   where "do body while\<^sub>\<bottom>\<^sub>N b invr invar vrt vari od = from\<^sub>\<bottom>\<^sub>N body until \<not> b do body od"
     
definition for_gfp_invr_vrt_ndes :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("for\<^sup>\<top>\<^sup>N '(_,_,_') invr _ vrt_ do _ od")
where "for\<^sup>\<top>\<^sup>N (init, b, incr) invr invar vrt vari do body od = from\<^sup>\<top>\<^sup>N init until \<not> b do body ;; incr od"

definition for_lfp_invr_vrt_ndes :: 
  "'\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" ("for\<^sub>\<bottom>\<^sub>N '(_,_,_') invr _ vrt _ do _ od")
where "for\<^sub>\<bottom>\<^sub>N (init, b, incr) invr invar vrt vari do body od = from\<^sub>\<bottom>\<^sub>N init until \<not> b do body ;; incr od"
  
subsection {*Design frame and anti-frame*}

definition frame\<^sub>D :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" where
[urel_defs]: "frame\<^sub>D a P = (true \<turnstile> (\<^bold>\<exists> st \<bullet> P\<lbrakk>\<guillemotleft>st\<guillemotright>/$\<Sigma>\<^sub>D\<acute>\<rbrakk> \<and> $\<Sigma>\<^sub>D\<acute> =\<^sub>u \<guillemotleft>st\<guillemotright> \<oplus> $\<Sigma>\<^sub>D on &a))"

definition antiframe\<^sub>D :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des" where
[urel_defs]: "antiframe\<^sub>D a P = (true \<turnstile> (\<^bold>\<exists> st \<bullet> P\<lbrakk>\<guillemotleft>st\<guillemotright>/$\<Sigma>\<^sub>D\<acute>\<rbrakk> \<and> $\<Sigma>\<^sub>D\<acute> =\<^sub>u $\<Sigma>\<^sub>D \<oplus> \<guillemotleft>st\<guillemotright> on &a))"  

end

