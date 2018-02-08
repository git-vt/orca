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
  
theory utp_prog_abrupt_more
  imports 
    "../hoare/HoareLogic/TotalCorrectness/IMP_Prog/utp_hoare_ndes_prog"
begin

section {*Abrupt*}
subsection {*Sequential C-program alphabet*}

text 
{* In order to capture exceptions, we extend the alphabet of UTP by an additional global 
   state variables:
   \begin{itemize}   
      \<^item> abrupt: a boolean variable used to specify if the program is in an abrupt state or not.
   \end{itemize}
*}

alphabet abr_vars = 
  abrupt :: bool

declare  abr_vars.splits [alpha_splits]
  
subsubsection {*Alphabet proofs*}
text {*
  The two locale interpretations below are a technicality to improve automatic
  proof support via the predicate and relational tactics. This is to enable the
  (re-)interpretation of state spaces to remove any occurrences of lens types
  after the proof tactics @{method pred_simp} and @{method rel_simp}, or any
  of their derivatives have been applied. Eventually, it would be desirable to
  automate both interpretations as part of a custom outer command for defining
  alphabets.
*}

interpretation cp_abr:
  lens_interp "\<lambda> (ok, r) . (ok, abrupt\<^sub>v r, more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation cp_abr_rel: lens_interp "\<lambda>(ok, ok', r, r').
  (ok, ok', abrupt\<^sub>v r, abrupt\<^sub>v r', more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

subsubsection {*Type lifting*}

type_synonym '\<alpha> hrel_abr_des  = "'\<alpha> abr_vars_scheme prog"

subsubsection {*Syntactic type setup*}

notation abr_vars_child_lens ("\<Sigma>\<^sub>A\<^sub>B\<^sub>R")

syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>A\<^sub>B\<^sub>R")
translations
  "_svid_st_alpha" => "CONST abr_vars_child_lens"

subsection {*Substitution lift and drop*}

abbreviation lift_rel_usubst_cpa ("\<lceil>_\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R")
where "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<equiv> \<sigma> \<oplus>\<^sub>s (\<Sigma>\<^sub>A\<^sub>B\<^sub>R \<times>\<^sub>L \<Sigma>\<^sub>A\<^sub>B\<^sub>R)"

abbreviation lift_usubst_cpa ("\<lceil>_\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R")
where "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<equiv> \<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R"

abbreviation drop_cpa_rel_usubst ("\<lfloor>_\<rfloor>\<^sub>S\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>\<sigma>\<rfloor>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<equiv> \<sigma> \<restriction>\<^sub>s (\<Sigma>\<^sub>A\<^sub>B\<^sub>R \<times>\<^sub>L \<Sigma>\<^sub>A\<^sub>B\<^sub>R)"

abbreviation drop_cpa_usubst ("\<lfloor>_\<rfloor>\<^sub>s\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>\<sigma>\<rfloor>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<equiv> \<lfloor>\<lfloor>\<sigma>\<rfloor>\<^sub>S\<^sub>A\<^sub>B\<^sub>R\<rfloor>\<^sub>s"

subsection {*UTP-Relations lift and drop*}

abbreviation lift_rel_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>A\<^sub>B\<^sub>R")
where "\<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>A\<^sub>B\<^sub>R \<times>\<^sub>L \<Sigma>\<^sub>A\<^sub>B\<^sub>R)"

abbreviation lift_pre_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><")
where "\<lceil>p\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub><\<rceil>\<^sub>A\<^sub>B\<^sub>R"

abbreviation lift_post_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>>")
where "\<lceil>p\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>> \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub>>\<rceil>\<^sub>A\<^sub>B\<^sub>R"

abbreviation drop_cpa_rel_uexpr ("\<lfloor>_\<rfloor>\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>P\<rfloor>\<^sub>A\<^sub>B\<^sub>R \<equiv> P \<restriction>\<^sub>p (\<Sigma>\<^sub>A\<^sub>B\<^sub>R \<times>\<^sub>L \<Sigma>\<^sub>A\<^sub>B\<^sub>R)"

abbreviation drop_cpa_pre_uexpr ("\<lfloor>_\<rfloor>\<^sub><\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>P\<rfloor>\<^sub><\<^sub>A\<^sub>B\<^sub>R \<equiv> \<lfloor>\<lfloor>P\<rfloor>\<^sub>A\<^sub>B\<^sub>R\<rfloor>\<^sub><"

abbreviation drop_cpa_post_uexpr ("\<lfloor>_\<rfloor>\<^sub>>\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>P\<rfloor>\<^sub>>\<^sub>A\<^sub>B\<^sub>R \<equiv> \<lfloor>\<lfloor>P\<rfloor>\<^sub>A\<^sub>B\<^sub>R\<rfloor>\<^sub>>"

subsection {* Reactive lemmas *}


subsection{*Healthiness conditions*}
  
definition abrh_def [upred_defs]: 
  "abrh(P) = (IF &abrupt THEN SKIP ELSE  P FI)"

section{*Control flow statements*}

subsection{*SKIP*}
definition  
skip_abr_def [urel_defs]: "skip_abr=  abrh(SKIP)"

subsection{*Assign*}

definition  
assigns_abr_def [urel_defs]: "assigns_abr \<sigma> =  abrh(\<langle>\<sigma>\<rangle>\<^sub>p)"

subsection{*Throw*}

definition  
throw_abr_def [urel_defs]: "throw_abr  =  assigns_abr [&abrupt \<mapsto>\<^sub>s true]"

subsection{*Sequential composition*}
text {*It does not need a definition. We get it by type inference.*}  
term "(throw_abr) ; (p )"  
subsection{*Conditional composition*}

definition  
if_abr_def [urel_defs]: "if_abr b P Q  =  IF (b \<oplus>\<^sub>p \<Sigma>\<^sub>A\<^sub>B\<^sub>R) THEN P ELSE Q FI"

subsection{*Iterations*}

definition  
while_abr_def [urel_defs]: "while_abr b I C  = INVR I  WHILE (b \<oplus>\<^sub>p \<Sigma>\<^sub>A\<^sub>B\<^sub>R) \<and> \<not>&abrupt DO C OD"

subsection{*Recursion*}
(*TODO @Yakoub*)

definition mu_abr_def [urel_defs]:
  "mu_abr P = (\<mu>\<^sub>p X \<bullet> P (abrh X))"
  
subsection {*Try catch*}

definition  try_catch_abr_def [urel_defs]:
  "try_catch_abr P Q = 
   abrh (P ;  IF &abrupt THEN (abrupt:== (\<not> &abrupt) ; abrh(Q)) ELSE skip_abr FI)"

section {*algebraic laws*} 

lemma [algebraic_laws_prog]:"IF b THEN P ELSE P FI = P"
  by (simp add: prog_rep_eq Algebraic_Laws.cond_idem)

lemma [algebraic_laws_prog]:"skip_abr ;  P =  P" "P ; skip_abr = P"
  unfolding skip_abr_def abrh_def
  by (simp add: algebraic_laws_prog)+  

lemma [algebraic_laws_prog]:"throw_abr ;  (abrh P) = throw_abr"     
  unfolding throw_abr_def abrh_def assigns_abr_def skip_abr_def
  apply (simp add: prog_rep_eq) 
   apply rel_auto
  done

lemma "abrh(\<langle>a\<rangle>\<^sub>p) ; abrh (throw_abr ;  IF &abrupt THEN (abrupt:== (\<not> &abrupt) ; abrh(\<langle>b\<rangle>\<^sub>p)) ELSE skip_abr FI) = 
         (abrh(\<langle>a\<rangle>\<^sub>p); abrh(\<langle>b\<rangle>\<^sub>p))"
  unfolding throw_abr_def abrh_def assigns_abr_def skip_abr_def
    apply (simp add: prog_rep_eq) 
  apply rel_auto
  apply (smt abr_vars.ext_inject abr_vars_ext_def)+
  done  
 
lemma "abrh(P) ; abrh (throw_abr ;  IF &abrupt THEN (abrupt:== (\<not> &abrupt) ; abrh(Q)) ELSE skip_abr FI) = 
         (abrh(P); abrh(Q))"
  unfolding throw_abr_def abrh_def assigns_abr_def skip_abr_def
    apply (simp add: prog_rep_eq) 
  apply rel_auto
  apply transfer
  unfolding Healthy_def H1_def H3_def
    apply rel_simp
         apply blast
      apply transfer
    unfolding Healthy_def H1_def H3_def
    apply rel_simp
          apply blast
      apply transfer
    unfolding Healthy_def H1_def H3_def
    apply rel_simp
         apply blast
      apply transfer
    unfolding Healthy_def H1_def H3_def
    apply rel_simp
    apply metis
   apply transfer
    unfolding Healthy_def H1_def H3_def
    apply rel_simp
       apply metis
      apply transfer
    unfolding Healthy_def H1_def H3_def
    apply rel_simp
      apply metis
      apply transfer
    unfolding Healthy_def H1_def H3_def
    apply rel_simp
     apply metis
    apply (smt abr_vars.select_convs(2))
done 
end
