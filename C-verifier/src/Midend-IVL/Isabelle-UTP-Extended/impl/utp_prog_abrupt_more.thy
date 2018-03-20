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
where [urel_defs]: "throw_abr  =  abrh (passigns (subst_upd id abrupt (\<not>(&abrupt))))"

subsection \<open>Sequential composition\<close>
  
text  \<open>It does not need a definition. We get it by type inference.\<close>  
  
subsection \<open>Conditional composition\<close>
find_theorems "(_ \<triangleleft> _ \<triangleright>\<^sub>D _)"  
    
no_notation pcond_prog ("IF (_)/ THEN (_) ELSE (_) FI") 
  
definition if_abr :: "'a upred \<Rightarrow> 'a abr_prog \<Rightarrow> 'a abr_prog \<Rightarrow> 'a abr_prog" ("IF (_)/ THEN (_) ELSE (_) FI")
where [urel_defs]: "if_abr b P Q = pcond_prog (b \<oplus>\<^sub>p \<Sigma>\<^sub>A\<^sub>B\<^sub>R) P Q"

subsection \<open>Recursion\<close>

definition mu_abr:: "('a abr_prog \<Rightarrow> 'a abr_prog) \<Rightarrow> 'a abr_prog"
where [urel_defs]: "mu_abr P = (\<mu>\<^sub>p X \<bullet> P (abrh X))"
  


lemma abrh_idem[simp]:"(abrh (abrh X)) = (abrh X)"  
  unfolding abrh_def
  by (simp add: if_prog_L6)

definition                                                            
  "greatest_abr g A \<longleftrightarrow> A \<subseteq> {P. abrh P = P} \<and> greatest_prog g A"  

lemma greatest_abr_alt_def: 
 "greatest_abr g A =  (A \<subseteq> {P. abrh P = P} \<and>  g \<in> A \<and> (ALL x : A. x \<sqsubseteq> g))"
  unfolding greatest_abr_def  prog_rep_eq greatest_def image_def Ball_def
  by (auto simp add: Rep_prog_inject Rep_prog_H1_H3_closed is_Ncarrier_is_ndesigns)

definition
  "Lower_abr A = ((Lower_prog (A\<inter> {P. abrh P = P})) \<inter> {P. abrh P = P})  "
sledgehammer_params[stop_on_first,parallel_subgoals, join_subgoals, timeout = 60]
  
lemma Lower_abr_alt_def: 
  "Lower_abr A = {l. (ALL x. x \<in> (A \<inter> {P. abrh P = P}) --> l \<sqsubseteq> x)} \<inter> {P. abrh P = P}"  
  unfolding Lower_abr_def  prog_rep_eq Lower_def image_def Ball_def Lower_prog_def
  apply (simp only: Int_Collect)
  apply auto
   apply (metis (mono_tags, lifting) Abs_prog_Rep_prog_Ncarrier Healthy_if Int_Collect Rep_prog_H1_H3_closed is_Ncarrier_is_ndesigns)
  apply (smt IntE IntI Rep_prog Rep_prog_inverse is_Ncarrier_is_ndesigns mem_Collect_eq)
  done

    
lemma inf_prog_is_abrh:
  "(\<And>x. x \<in> A \<Longrightarrow> abrh x = x) \<Longrightarrow> 
     \<Sqinter>\<^sub>p(A\<inter> {P. abrh P = P}) = \<Sqinter>\<^sub>p A"
  apply (simp add: prog_rep_eq)
  unfolding inf_def  image_def Ball_def 
  apply (rule someI2_ex)
   apply (rule exI[where x="(\<^bold>\<Sqinter>\<^bsub>NDES\<^esub>{y. \<exists>x\<in>A. y = \<lbrakk>x\<rbrakk>\<^sub>p})"])
   apply (smt CollectD Collect_mono Rep_prog normal_design_theory_continuous.inf_glb)
  apply (rule ndes_utp_theory.greatest_unique)
    defer
   apply auto[1]
  apply (smt Collect_cong Int_Collect tfl_some)
  done

lemma abrh_image_subset:
  "abrh ` A \<subseteq> {P. abrh P = P}"
  by (simp add: image_subsetI)
    
thm normal_design_theory_continuous.inf_closed    

lemma abr_abrh_closed: 
  "(abrh P) \<in> {P. abrh P = P}"
  by simp
    
lemma inf_abrh_greatest:
  "(\<And>x. x \<in> A \<Longrightarrow> abrh z \<sqsubseteq> abrh x) \<Longrightarrow>  abrh z \<sqsubseteq> \<Sqinter>\<^sub>p (abrh ` A)" 
  by (metis (mono_tags, lifting) imageE inf_prog_greatest)

lemma inf_abrh_lower:
  "x \<in>  A \<Longrightarrow> \<Sqinter>\<^sub>p (abrh ` A) \<sqsubseteq> abrh x"
  by (simp add: inf_prog_lower)  
lemma 
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow> abrh (\<Sqinter>\<^sub>p A) = \<Sqinter>\<^sub>p(abrh ` A)"
  
  thm mem_Collect_eq
  thm subsetI    
  oops 
  find_theorems "_ \<sqsubseteq> _ \<Longrightarrow> _ \<sqsubseteq> _ \<Longrightarrow> _ = _"  
lemma "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y" 
oops  
thm HOL.no_atp(10)  
lemma 
  "(\<And>x. x \<in> A \<Longrightarrow> abrh x = x) \<Longrightarrow> A \<noteq> {} \<Longrightarrow>
     (\<Sqinter>\<^sub>p (abrh ` A)) = abrh (\<Sqinter>\<^sub>p (abrh ` A))"
  (*TODO: see healthy_inf*)
  
  unfolding inf_prog_alt_def
  apply (rule someI2_ex)

  using inf_prog_is_greatest_Lower_prog apply auto[1]
  apply (rule someI2_ex)
    
    using inf_prog_is_greatest_Lower_prog apply auto[1]
  unfolding Lower_prog_alt_def greatest_prog_alt_def
   apply auto
  apply (rule HOL.no_atp(10))
   thm normal_design_theory_continuous.inf_closed
   thm greatest_prog_alt_def 
  oops
    
 lemma inf_abrh_in_Lower:
  "(\<And>x. x \<in> A \<Longrightarrow> abrh x = x ) \<Longrightarrow>  
   (\<Sqinter>\<^sub>p (abrh ` A)) \<in> ((Lower_prog (abrh ` (A \<inter> {P. abrh P = P}))) \<inter> {P. abrh P = P})"
   unfolding Lower_prog_alt_def
   apply auto
    
   using inf_abrh_lower apply force
     apply ()
     (*see the extensionality proofs*)
     
  oops
   
thm inf_prog.rep_eq
lemma "(\<And>x. x \<in> A \<Longrightarrow> (\<^bold>N x) = x) \<Longrightarrow> \<^bold>N (\<^bold>\<Sqinter>\<^bsub>NDES\<^esub>A) =  (\<^bold>\<Sqinter>\<^bsub>NDES\<^esub> A)"
  by (metis (no_types, lifting) Healthy_def mem_Collect_eq normal_design_theory_continuous.inf_closed subsetI)

    
lemma inf_abr_lower:
  "x \<in> A \<Longrightarrow> \<Sqinter>\<^sub>p A \<sqsubseteq> x" 
  apply (simp only: prog_rep_eq) 
  apply (meson Rep_prog image_eqI image_subsetI normal_design_theory_continuous.inf_lower)
  done
    
lemma inf_prog_abrh_in_Lower_abr:
  "(\<And>x. x \<in> A \<Longrightarrow> abrh x = x) \<Longrightarrow> (\<Sqinter>\<^sub>a A) \<in> Lower_prog A" 
  unfolding Lower_prog_alt_def inf_abr_def 
  apply auto
    thm inf_prog_lower
     apply (rule inf_prog_lower)  
     apply simp
                
        oops
          thm is_Ncarrier_is_ndesigns
 term "Rep_prog (Abs_prog c)"      
lemma inf_abrh_is_greatest_Lower_abr:
  "(\<And>x. x \<in> A \<Longrightarrow> abrh x = x) \<Longrightarrow> greatest_abr (\<Sqinter>\<^sub>p A) (Lower_abr A)" 
  unfolding greatest_abr_def   
  apply auto
      apply (simp add: prog_rep_eq greatest_def)
  apply auto
    apply (simp add: Rep_prog_H1_H3_closed is_Ncarrier_is_ndesigns)
    
    apply (simp add: Lower_abr_alt_def)
    
  oops
lemma inf_prog_is_greatest_Lower_prog:
  "(\<And>x. x \<in> A \<Longrightarrow> abrh x = x) \<Longrightarrow> greatest_abr (\<Sqinter>\<^sub>a A) (Lower_abr A)" 
  unfolding greatest_abr_alt_def  Lower_abr_alt_def
  apply auto
  oops
    
lemma 
  "(\<And>x. x \<in> A \<Longrightarrow> abrh x = x) \<Longrightarrow> abrh (\<Sqinter>\<^sub>aA ) = \<Sqinter>\<^sub>a A"
  unfolding inf_abr_def greatest_abr_def Lower_abr_def
  apply auto
     apply (rule someI2_ex)
    defer apply (metis (mono_tags, lifting) Int_Collect greatest_abr_alt_def greatest_abr_def semilattice_inf_class.inf_le2)
  apply (rule exI[where x= "\<Sqinter>\<^sub>p (Lower_prog (A \<inter> {P. abrh P = P}) \<inter> {P. abrh P = P})"])
    
  unfolding  abrh_def  
    
oops  
  
lemma inf_abr_alt_def:
  "(\<And>x. x \<in> A \<Longrightarrow> abrh x = x) \<Longrightarrow> 
   \<Sqinter>\<^sub>a A = \<Sqinter>\<^sub>p (abrh ` A )"
  unfolding inf_abr_def inf_prog_alt_def  Lower_abr_def  greatest_abr_def
  apply (auto )
      apply (rule someI2_ex)
  using inf_prog_is_greatest_Lower_prog apply auto[1]
     
  apply (rule someI2_ex)
   
    
   apply (rule exI[where x="(\<Sqinter>\<^sub>p (abrh ` A))"])
   
  unfolding inf_def prog_rep_eq Lower_def image_def Ball_def Lower_prog_def greatest_def
   apply auto
   
     apply (simp add: Rep_prog_H1_H3_closed is_Ncarrier_is_ndesigns)  
    apply (rule someI2_ex)
     apply auto
    

  oops
definition LFP_abr :: " ('a abr_prog \<Rightarrow> 'a abr_prog) \<Rightarrow> 'a abr_prog" 
  where "LFP_abr F = \<Sqinter>\<^sub>a {x. F x \<sqsubseteq> x}" 
    
syntax
  "_amu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu>\<^sub>a _ \<bullet> _" [0, 10] 10)

notation LFP_abr ("\<mu>\<^sub>a")

translations
  "\<mu>\<^sub>a X \<bullet> P" == "CONST LFP_abr (\<lambda> X. P)"


lemma inf_abr_lower:
  "(\<And>x. x \<in> A \<Longrightarrow> abrh x = x) \<Longrightarrow> x \<in> A \<Longrightarrow> \<Sqinter>\<^sub>aA \<sqsubseteq> x"  
  unfolding inf_abr_def   greatest_abr_def Lower_abr_def
  
  oops  

lemma lfp_abr_healthy_comp:
  "\<mu>\<^sub>a F = \<mu>\<^sub>a (F \<circ> abrh)" 
  
  unfolding LFP_abr_def inf_abr_def comp_def
  apply (rule someI2_ex)
      using inf_prog_is_greatest_Lower_prog apply auto[1]


  by simp
    
lemma "(abrh (\<mu>\<^sub>a fun1) = (\<mu>\<^sub>a fun1))"
  unfolding mu_abr_def abrh_def
     apply (simp only: prog_rep_eq)
  oops     
thm LFP_def
  term "LFP"
term "Order.le"    
term "a \<sqsubseteq> s"    
term "{u \<in> carrier L. f u \<sqsubseteq>\<^bsub>L\<^esub> u}"    
 (*I need to re-define LFP such that LFP F = \<Sqinter> {u \<in> {P. abrh P = P \<or> P = throw_abr}. F u \<sqsubseteq> u}
   To have such a definition I need to lift \<Sqinter> to prog*)   
lemma "mono_prog F \<Longrightarrow> F \<in> {P. abrh P = P} \<rightarrow> {P. abrh P = P} \<Longrightarrow> 
  LFP_abr F = (\<mu>\<^sub>p X \<bullet> F (abrh X))"
  unfolding LFP_abr_def inf_abr_def mu_abr_def lfp_prog_alt_def inf_prog_alt_def greatest_abr_def Lower_abr_def
  apply auto
  apply (rule someI2_ex)
  using inf_prog_is_greatest_Lower_prog apply auto[1]
  apply (rule someI2_ex)
   
                                                                          
   apply (rule exI[where x = "\<Sqinter>\<^sub>p(({x. F x \<sqsubseteq> x} \<inter> {P. abrh P = P}) \<inter> {P. abrh P = P})"])
   defer
   apply (rule greatest_prog_unique)
    apply auto
   apply (drule Pi_mem)
    apply auto
    thm Pi_I
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
