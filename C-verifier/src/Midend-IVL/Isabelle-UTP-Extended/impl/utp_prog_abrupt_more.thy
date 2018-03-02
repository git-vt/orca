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

section \<open>Imperative Programs\<close>
  
theory utp_prog_abrupt_more
  imports 
    "../HoareLogic/TotalCorrectness/utp_hoare_ndes_prog"
begin

section \<open>Abrupt\<close>
subsection \<open>Sequential C-program alphabet\<close>

text 
\<open>In order to capture exceptions, we extend the alphabet of UTP by an additional global 
   state variables:
   \begin{itemize}   
      \<^item> abrupt: a boolean variable used to specify if the program is in an abrupt state or not.
   \end{itemize}\<close>

alphabet abr_vars = 
  abrupt :: bool

declare  abr_vars.splits [alpha_splits]
  
subsubsection \<open>Alphabet proofs\<close>
text \<open>
  The two locale interpretations below are a technicality to improve automatic
  proof support via the predicate and relational tactics. This is to enable the
  (re-)interpretation of state spaces to remove any occurrences of lens types
  after the proof tactics @{method pred_simp} and @{method rel_simp}, or any
  of their derivatives have been applied. Eventually, it would be desirable to
  automate both interpretations as part of a custom outer command for defining
  alphabets.\<close>

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

subsubsection \<open>Type lifting\<close>

type_synonym '\<alpha> abr_prog  = "'\<alpha> abr_vars_scheme prog"
type_synonym '\<alpha> abr  = "'\<alpha> abr_vars_scheme"

translations
  (type) "'\<alpha> abr" <= (type) "'\<alpha> abr_vars_scheme"
  (type) "'\<alpha> abr" <= (type) "'\<alpha> abr_vars_ext"
  (type) "'\<alpha> abr_prog" <= (type) "'\<alpha> abr_vars_scheme prog"
  (type) "'\<alpha> abr_prog" <= (type) "'\<alpha> abr_vars_ext prog"

(*type_synonym '\<alpha> des  = "'\<alpha> des_vars_scheme"
type_synonym ('\<alpha>, '\<beta>) rel_des = "('\<alpha> des, '\<beta> des) rel"
type_synonym '\<alpha> hrel_des = "('\<alpha> des) hrel"

translations
  (type) "'\<alpha> des" <= (type) "'\<alpha> des_vars_scheme"
  (type) "'\<alpha> des" <= (type) "'\<alpha> des_vars_ext"
  (type) "('\<alpha>, '\<beta>) rel_des" <= (type) "('\<alpha> des, '\<beta> des) rel"
  (type) "'\<alpha> hrel_des" <= (type) "'\<alpha> des hrel"*)
  
subsubsection \<open>Syntactic type setup\<close>

notation abr_vars_child_lens ("\<Sigma>\<^sub>A\<^sub>B\<^sub>R")

syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>A\<^sub>B\<^sub>R")
translations
  "_svid_st_alpha" => "CONST abr_vars_child_lens"

subsection \<open>Substitution lift and drop\<close>
  
abbreviation lift_rel_usubst_cpa ("\<lceil>_\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R")
where "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<equiv> \<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>A\<^sub>B\<^sub>R "

abbreviation lift_usubst_cpa ("\<lceil>_\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R")
  where "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<equiv> \<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R"
    
abbreviation drop_cpa_rel_usubst ("\<lfloor>_\<rfloor>\<^sub>S\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>\<sigma>\<rfloor>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<equiv> \<sigma> \<restriction>\<^sub>s \<Sigma>\<^sub>A\<^sub>B\<^sub>R "

abbreviation drop_cpa_usubst ("\<lfloor>_\<rfloor>\<^sub>s\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>\<sigma>\<rfloor>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<equiv> \<lfloor>\<lfloor>\<sigma>\<rfloor>\<^sub>S\<^sub>A\<^sub>B\<^sub>R\<rfloor>\<^sub>s"

subsection \<open>UTP-Relations lift and drop\<close>

abbreviation lift_rel_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>A\<^sub>B\<^sub>R")
where "\<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R \<equiv> P \<oplus>\<^sub>p \<Sigma>\<^sub>A\<^sub>B\<^sub>R "

abbreviation lift_pre_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><")
where "\<lceil>p\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub><\<rceil>\<^sub>A\<^sub>B\<^sub>R"

abbreviation lift_post_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>>")
where "\<lceil>p\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>> \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub>>\<rceil>\<^sub>A\<^sub>B\<^sub>R"

abbreviation drop_cpa_rel_uexpr ("\<lfloor>_\<rfloor>\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>P\<rfloor>\<^sub>A\<^sub>B\<^sub>R \<equiv> P \<restriction>\<^sub>p \<Sigma>\<^sub>A\<^sub>B\<^sub>R"

abbreviation drop_cpa_pre_uexpr ("\<lfloor>_\<rfloor>\<^sub><\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>P\<rfloor>\<^sub><\<^sub>A\<^sub>B\<^sub>R \<equiv> \<lfloor>\<lfloor>P\<rfloor>\<^sub>A\<^sub>B\<^sub>R\<rfloor>\<^sub><"

abbreviation drop_cpa_post_uexpr ("\<lfloor>_\<rfloor>\<^sub>>\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>P\<rfloor>\<^sub>>\<^sub>A\<^sub>B\<^sub>R \<equiv> \<lfloor>\<lfloor>P\<rfloor>\<^sub>A\<^sub>B\<^sub>R\<rfloor>\<^sub>>"


subsection \<open>Healthiness conditions\<close>
  
definition abrh_def [upred_defs]: 
  "abrh(P) = (IF &abrupt THEN SKIP ELSE  P FI)"

section \<open>Control flow statements\<close>
  
subsection \<open>SKIP\<close>
  
text \<open>For the below reason we do not re-define skip\<close>
  
lemma abrh_skipe[simp]:
  "abrh(SKIP) = SKIP"
  unfolding abrh_def
  by (simp add: if_prog_idem)

subsection \<open>Assign\<close>
  
definition  
assigns_abr_def [urel_defs]: "assigns_abr \<sigma> =  abrh(\<langle>\<sigma>  \<oplus>\<^sub>s \<Sigma>\<^sub>A\<^sub>B\<^sub>R\<rangle>\<^sub>p)"

adhoc_overloading
  uassigns assigns_abr

translations
  "_assignment xs vs" => "CONST assigns_abr (_mk_usubst (CONST id) xs vs)"
  "x :== v" <= "CONST assigns_abr (CONST subst_upd (CONST id) (CONST svar x) v)"

subsection \<open>Throw\<close>

definition  throw_abr:: "'a abr_prog" ("THROW")
where [urel_defs]: "throw_abr  =  passigns (subst_upd id abrupt true)"

subsection \<open>Sequential composition\<close>
  
text  \<open>It does not need a definition. We get it by type inference.\<close>  
  
subsection \<open>Conditional composition\<close>
  
no_notation pcond_prog ("IF (_)/ THEN (_) ELSE (_) FI") 
  
definition if_abr :: "'a upred \<Rightarrow> 'a abr_prog \<Rightarrow> 'a abr_prog \<Rightarrow> 'a abr_prog" ("IF (_)/ THEN (_) ELSE (_) FI")
where [urel_defs]: "if_abr b P Q = pcond_prog (b \<oplus>\<^sub>p \<Sigma>\<^sub>A\<^sub>B\<^sub>R) P Q"

subsection \<open>Recursion\<close>

definition mu_abr:: "('a abr_prog \<Rightarrow> 'a abr_prog) \<Rightarrow> 'a abr_prog"
where [urel_defs]: "mu_abr P = (\<mu>\<^sub>p X \<bullet> P (abrh X))"
  
syntax
  "_amu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu>\<^sub>a _ \<bullet> _" [0, 10] 10)

notation mu_abr ("\<mu>\<^sub>a")

translations
  "\<mu>\<^sub>a X \<bullet> P" == "CONST mu_abr (\<lambda> X. P)"
term "mu_abr F"
term "\<forall>x. abrh x = x"  
thm normal_design_theory_continuous.LFP_healthy_comp  
lemma abrh_idem[simp]:"(abrh (abrh X)) = (abrh X)"  
  unfolding abrh_def
  by (simp add: if_prog_L6)

lemma lfp_abr_healthy_comp:
  "\<mu>\<^sub>a F = \<mu>\<^sub>a (F \<circ> abrh)" 
  unfolding mu_abr_def
  by simp
lemma "(abrh (\<mu>\<^sub>a fun1) = (\<mu>\<^sub>a fun1))"
  unfolding mu_abr_def abrh_def
     apply (simp only: prog_rep_eq)
  oops 
  term "\<Sqinter>\<^bsub>L\<^esub> {u \<in> carrier L. f u \<sqsubseteq>\<^bsub>L\<^esub> u}"    
 (*I need to re-define LFP such that LFP F = \<Sqinter> {u \<in> {P. abrh P = P}. F u \<sqsubseteq> u}
   To have such a definition I need to lift \<Sqinter> to prog*)   
lemma "mono_prog F \<Longrightarrow> F \<in> {P. abrh P = P} \<rightarrow> {P. abrh P = P} \<Longrightarrow> LFP_def = (\<mu>\<^sub>p X \<bullet> P (abrh X))"
  oops
lemma "\<And>fun1 fun2. (\<And>x. abrh x = x \<Longrightarrow> (abrh (fun1 x) = (fun1 x)) \<and> fun1 x = fun2 x) \<Longrightarrow> (abrh (\<mu>\<^sub>a fun1) = (\<mu>\<^sub>a fun1)) \<and> \<mu>\<^sub>a fun1 = \<mu>\<^sub>a fun2"
 oops 
lemma "mono_prog F \<Longrightarrow> \<mu>\<^sub>a F = F(\<mu>\<^sub>a F)" 
  apply  mu_abr_def 
  apply (subst lfp_prog_unfold)
    
    thm lfp_prog_unfold[THEN ext]
       
subsection \<open>Iterations\<close>
  
definition  
while_abr_def [urel_defs]: "while_abr b I C  = INVR I  WHILE (b \<oplus>\<^sub>p \<Sigma>\<^sub>A\<^sub>B\<^sub>R) \<and> \<not>&abrupt DO C OD"
  
subsection {*Try catch*}
term "passigns (subst_upd id abrupt (\<not> &abrupt))"
definition  try_catch_abr_def [urel_defs]:
  "try_catch_abr P Q = 
   abrh (P ;  IF &abrupt THEN (passigns (subst_upd id abrupt (\<not> &abrupt)) ; abrh(Q)) ELSE SKIP FI)"

section {*algebraic laws*} 

lemma [algebraic_laws_prog]:"IF b THEN P ELSE P FI = P"
  by (simp add: prog_rep_eq Algebraic_Laws.cond_idem)

lemma [algebraic_laws_prog]:"SKIP ;  P =  P" "P ; SKIP = P"
  unfolding  abrh_def
  by (simp_all)  

lemma [algebraic_laws_prog]:"throw_abr ;  (abrh P) = throw_abr"     
  unfolding throw_abr_def abrh_def assigns_abr_def 
  apply (simp add: prog_rep_eq) 
   apply rel_auto
  done

lemma "abrh(\<langle>a\<rangle>\<^sub>p) ; abrh (throw_abr ;  IF &abrupt THEN (passigns (subst_upd id abrupt (\<not> &abrupt)) ; abrh(\<langle>b\<rangle>\<^sub>p)) ELSE SKIP FI) = 
         (abrh(\<langle>a\<rangle>\<^sub>p); abrh(\<langle>b\<rangle>\<^sub>p))"
  unfolding throw_abr_def abrh_def assigns_abr_def 
    apply (simp add: prog_rep_eq) 
  apply rel_auto
  apply (smt abr_vars.ext_inject abr_vars_ext_def)+
  done  
 
lemma "abrh(P) ; abrh (throw_abr ;  IF &abrupt THEN (passigns (subst_upd id abrupt (\<not> &abrupt)) ; abrh(Q)) ELSE SKIP FI) = 
         (abrh(P); abrh(Q))"
  unfolding throw_abr_def abrh_def assigns_abr_def 
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
