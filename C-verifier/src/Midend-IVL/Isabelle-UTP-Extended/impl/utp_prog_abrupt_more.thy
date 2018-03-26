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

lemma abrh_idem[simp]:"(abrh (abrh X)) = (abrh X)"  
  unfolding abrh_def
  by (simp add: if_prog_L6)
    
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
    
no_notation pcond_prog ("IF (_)/ THEN (_) ELSE (_) FI") 
  
definition if_abr :: "'a upred \<Rightarrow> 'a abr_prog \<Rightarrow> 'a abr_prog \<Rightarrow> 'a abr_prog" 
  where [urel_defs]: "if_abr b P Q = pcond_prog (b \<oplus>\<^sub>p \<Sigma>\<^sub>A\<^sub>B\<^sub>R) P Q"
    
definition try_catch_abr:
  "try_catch_abr P Q = 
   abrh (P ;  if_abr (&abrupt) (passigns (subst_upd id abrupt (\<not> &abrupt)) ; abrh(Q)) SKIP )"

subsection \<open>Lattices\<close>

definition                                                            
  "greatest_abr g A \<longleftrightarrow> A \<subseteq> {P. abrh P = P} \<and> greatest_prog g A"  
  
definition                                                            
  "least_abr g A \<longleftrightarrow> A \<subseteq> {P. abrh P = P} \<and> least_prog g A" 

definition
  "Lower_abr A = ((Lower_prog (A\<inter> {P. abrh P = P})) \<inter> {P. abrh P = P})"

definition
  "Upper_abr A = ((Upper_prog (A \<inter> {P. abrh P = P})) \<inter> {P. abrh P = P})"
  
definition inf_abr :: "'a abr_prog set \<Rightarrow> 'a abr_prog" ("\<^bold>\<Sqinter>\<^sub>a_" [900] 900)
where "inf_abr A = (SOME x. greatest_abr x (Lower_abr A))"  

definition sup_abr :: "'a abr_prog set \<Rightarrow> 'a abr_prog" ("\<^bold>\<Squnion>\<^sub>a_" [900] 900)
where "sup_abr A = (SOME x. least_abr x (Upper_abr A))"  
    
lemma abrh_below_top_abr:
  "x \<in> {P. abrh P = P} \<Longrightarrow> x \<sqsubseteq> abrh MAGIC"  
  apply (simp add: abrh_def  prog_rep_eq   )
  apply (metis H1_below_top Healthy_def Rep_prog_H1_H3_closed cond_mono order_refl)
  done
    
lemma bottom_abrh_lower:
  "x \<in> {P. abrh P = P} \<Longrightarrow> abrh (ABORT) \<sqsubseteq> x"
  apply (simp add: abrh_def  prog_rep_eq   )
  apply (metis cond_mono order_refl utp_pred_laws.top_greatest)
  done  
   
lemma greatest_abr_alt_def: 
 "greatest_abr g A = (A \<subseteq> {P. abrh P = P} \<and> g \<in> A \<and> (ALL x : A. x \<sqsubseteq> g))"
  unfolding greatest_abr_def  prog_rep_eq greatest_def image_def Ball_def
  by (auto simp add: Rep_prog_inject Rep_prog_H1_H3_closed is_Ncarrier_is_ndesigns)

lemma least_abr_alt_def: 
 "least_abr l A = (A \<subseteq> {P. abrh P = P} \<and> l \<in> A \<and> (ALL x : A. l \<sqsubseteq> x))"
  unfolding least_abr_def  prog_rep_eq least_def image_def Ball_def
  by (auto simp add: Rep_prog_inject Rep_prog_H1_H3_closed is_Ncarrier_is_ndesigns)
  
sledgehammer_params[stop_on_first, parallel_subgoals, join_subgoals, timeout = 60]
  
lemma Lower_abr_alt_def: 
  "Lower_abr A = {l. (ALL x. x \<in> (A \<inter> {P. abrh P = P}) \<longrightarrow> l \<sqsubseteq> x)} \<inter> {P. abrh P = P}"  
  unfolding Lower_abr_def  prog_rep_eq Lower_def image_def Ball_def Lower_prog_def
  apply (simp only: Int_Collect)
  apply auto
   apply (metis (mono_tags, lifting) Abs_prog_Rep_prog_Ncarrier Healthy_if Int_Collect Rep_prog_H1_H3_closed is_Ncarrier_is_ndesigns)
  apply (smt IntE IntI Rep_prog Rep_prog_inverse is_Ncarrier_is_ndesigns mem_Collect_eq)
  done
    
lemma Upper_abr_alt_def:
  "Upper_abr A = {u. (ALL x. x \<in> (A \<inter> {P. abrh P = P}) \<longrightarrow> x \<sqsubseteq> u)} \<inter> {P. abrh P = P}"  
  unfolding Upper_abr_def prog_rep_eq Upper_def image_def Ball_def Upper_prog_def
  apply (simp only: Int_Collect)
  apply auto
   apply (metis (mono_tags, lifting) Abs_prog_Rep_prog_Ncarrier Healthy_if Int_Collect 
                                     Rep_prog_H1_H3_closed is_Ncarrier_is_ndesigns)
  apply (smt IntE IntI Rep_prog Rep_prog_inverse is_Ncarrier_is_ndesigns mem_Collect_eq)
  done
    
lemma inf_prog_Int_abrh:
  "(\<And>x. x \<in> A \<Longrightarrow> abrh x = x) \<Longrightarrow> 
     \<Sqinter>\<^sub>p(A \<inter> {P. abrh P = P}) = \<Sqinter>\<^sub>p A"
  apply (simp add: prog_rep_eq)
  unfolding inf_def image_def Ball_def 
  apply (rule someI2_ex)
   apply (rule exI[where x="(\<^bold>\<Sqinter>\<^bsub>NDES\<^esub>{y. \<exists>x\<in>A. y = \<lbrakk>x\<rbrakk>\<^sub>p})"])
   apply (smt CollectD Collect_mono Rep_prog normal_design_theory_continuous.inf_glb)
  apply (rule ndes_utp_theory.greatest_unique)
    defer
   apply auto[1]
  apply (smt Collect_cong Int_Collect tfl_some)
  done
    
lemma abrh_subset_member: 
  "\<lbrakk>A \<subseteq> {P. abrh P = P}; P \<in> A \<rbrakk> \<Longrightarrow> abrh(P) = P"
  by (meson Ball_Collect ) 
    
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
    
lemma inf_abrh_image_lower:
  "x \<in> A \<Longrightarrow> \<Sqinter>\<^sub>p (abrh ` A) \<sqsubseteq> abrh x"
  by (simp add: inf_prog_Lower)   

lemma inf_prog_abrh_in_Lower_prog_Int_abrh:
  "abrh (\<Sqinter>\<^sub>pA) \<in> Lower_prog (A \<inter> {P. abrh P = P})" 
   unfolding inf_prog_alt_def 
    apply (rule someI2_ex)    
   using inf_prog_is_greatest_Lower_prog 
    apply blast
    apply (simp only: greatest_prog_alt_def Lower_prog_alt_def)
    apply auto
    apply (metis (no_types, lifting) Rep_prog_refine abrh_def cond_mono order_refl pcond_prog.rep_eq)
  done

lemma Lower_abr_subset_Lower_prog:
  "Lower_abr (A \<inter> {P. abrh P = P}) \<subseteq> Lower_prog (A \<inter> {P. abrh P = P})"
  by (simp add: Lower_abr_def)
    
lemma inf_abr_in_Lower_abr:
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow> 
  (\<^bold>\<Sqinter>\<^sub>aA) \<in> Lower_abr (A \<inter> {P. abrh P = P})"
   unfolding greatest_abr_def inf_abr_def
   apply (subst Lower_abr_def)
      apply (subst Lower_abr_def)
  apply auto
  apply (rule someI2_ex)    
   apply (rule exI[where x = "abrh (\<Sqinter>\<^sub>pA)"]) 
   apply (simp add:prog_rep_eq image_def greatest_def Bex_def)
   apply auto
     apply (metis Healthy_def Rep_prog_H1_H3_closed ndes_hcond_def)
    apply (rule exI[where x = "abrh (\<Sqinter>\<^sub>pA)"])
    apply auto[]
    apply (metis (mono_tags, lifting) Collect_cong Rep_prog_eq inf_prog_abrh_in_Lower_prog_Int_abrh)
   apply (simp only:inf_prog_alt_def Bex_def)
   apply (rule someI2_ex)   
  using inf_prog_is_greatest_Lower_prog apply blast
   apply (metis (no_types, lifting) Rep_prog_inject abrh_def cond_mono greatest_def 
                                    greatest_prog.rep_eq image_eqI order_refl 
                                    pcond_prog.rep_eq semilattice_inf_class.inf.orderE utp_order_le)
   apply (simp add:Lower_abr_def greatest_prog_alt_def)
  done

lemma inf_abr_in_Lower_prog:
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow> 
  (\<^bold>\<Sqinter>\<^sub>aA) \<in> Lower_prog (A \<inter> {P. abrh P = P})"
  by (metis (mono_tags) Int_iff Lower_abr_def inf_abr_in_Lower_abr semilattice_inf_class.inf.right_idem)

lemma inf_abr_greatest:
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow> abrh z = z \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x) \<Longrightarrow>  
   z \<sqsubseteq> (\<^bold>\<Sqinter>\<^sub>aA)"
  (*The KEY proof for the rest of the theory*)
  unfolding greatest_abr_def Lower_abr_def inf_abr_def
  apply auto
  apply (rule someI2_ex)    
   apply (rule exI[where x = "abrh (\<Sqinter>\<^sub>pA)"])    
   apply (simp add: prog_rep_eq image_def greatest_def Bex_def)
   apply auto
     apply (metis Healthy_def Rep_prog_H1_H3_closed ndes_hcond_def)
    apply (rule exI[where x = "abrh (\<Sqinter>\<^sub>pA)"])
    apply auto[]   
      apply (metis (mono_tags, lifting) Collect_cong Rep_prog_eq inf_prog_abrh_in_Lower_prog_Int_abrh)
  unfolding inf_prog_alt_def 
   defer
   apply (simp only: greatest_prog_alt_def Lower_prog_alt_def)
   apply auto
  apply (rule someI2_ex)
  using inf_prog_is_greatest_Lower_prog 
   apply auto[1]
  apply (metis (no_types, lifting) Rep_prog_eq Rep_prog_refine abrh_def cond_mono 
                                   greatest_prog_alt_def order_refl pcond_prog.rep_eq 
                                   semilattice_inf_class.inf.orderE)
  done 
  
lemma inf_prog_abrh_is_greatest_lower:
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow> 
   greatest_prog (abrh (\<Sqinter>\<^sub>pA)) (Lower_prog (A \<inter> {P. abrh P = P}) \<inter> {P. abrh P = P})"
  unfolding inf_prog_alt_def 
  apply (rule someI2_ex)    
  using inf_prog_is_greatest_Lower_prog 
   apply blast
  apply (simp only: greatest_prog_alt_def Lower_prog_alt_def)
  apply auto
   apply (metis (no_types, lifting) Rep_prog_refine abrh_def cond_mono order_refl pcond_prog.rep_eq)
  unfolding abrh_def
  apply (metis (mono_tags, lifting) if_prog_monoI mem_Collect_eq order_refl subsetCE)
  done 
     
lemma inf_abr_lower:
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow>  x \<in> A \<Longrightarrow>
    (\<^bold>\<Sqinter>\<^sub>aA) \<sqsubseteq> x" 
  unfolding greatest_abr_def Lower_abr_def inf_abr_def
  apply auto
  apply (rule someI2_ex)    
   apply (rule exI[where x = "abrh (\<Sqinter>\<^sub>pA)"])    
   apply (simp add: inf_prog_abrh_is_greatest_lower)
  apply (metis (no_types, lifting) Int_lower1 dual_order.trans greatest_prog_alt_def 
                                   inf_prog_is_greatest_Lower_prog inf_prog_Lower 
                                   semilattice_inf_class.inf.orderE subsetCE)
  done
     
lemma inf_abr_is_abrh:
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow>  
   abrh (\<^bold>\<Sqinter>\<^sub>aA) = (\<^bold>\<Sqinter>\<^sub>aA)"
  using Lower_abr_def inf_abr_in_Lower_abr 
  by blast    
    
lemma inf_abr_empty:
  "(\<^bold>\<Sqinter>\<^sub>a {}) = abrh (MAGIC)"
  unfolding inf_abr_def
  apply (rule someI2_ex)    
   apply (metis (no_types, lifting) Ball_Collect Lower_abr_def empty_iff greatest_abr_def inf_prog_abrh_is_greatest_lower semilattice_inf_class.inf_le2)
  apply (metis (no_types, lifting) Lower_abr_def greatest_abr_def greatest_prog_unique inf_prog_abrh_is_greatest_lower inf_prog_empty order_bot_class.bot.extremum)
  done 
    
lemma inf_abr_is_greatest_abr_Lower_abr:
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow> greatest_abr (\<^bold>\<Sqinter>\<^sub>a A) (Lower_abr A)"
  unfolding greatest_abr_def 
  apply auto
   apply (simp add: Lower_abr_def)
  unfolding  greatest_prog_alt_def
  apply auto
   apply (metis (mono_tags, lifting) inf_abr_in_Lower_abr semilattice_inf_class.inf.orderE)
  apply (rule inf_abr_greatest)
    apply auto   
  using Lower_abr_def apply auto[1]
  using Lower_abr_alt_def apply auto
  done
 
lemma inf_abr_univ:
  "(\<^bold>\<Sqinter>\<^sub>a {P. abrh P = P}) = abrh (ABORT)"
  unfolding inf_abr_def
  apply (rule someI2_ex)    
   apply (rule exI[where x = "(\<^bold>\<Sqinter>\<^sub>a {P. abrh P = P})"])
   apply (rule inf_abr_is_greatest_abr_Lower_abr)
   apply simp
  unfolding greatest_abr_alt_def Lower_abr_alt_def
  apply auto
  apply (simp add: bottom_abrh_lower dual_order.antisym)
  done
    
lemma sup_prog_abrh_in_Upper_prog_Int_abrh:
  "abrh (\<Squnion>\<^sub>pA) \<in> Upper_prog (A \<inter> {P. abrh P = P})" 
  unfolding sup_prog_alt_def 
  apply (rule someI2_ex)
  using sup_prog_is_least_Upper_prog 
   apply auto[1]
  apply (simp only: least_prog_alt_def Upper_prog_alt_def)
  apply auto
  apply (metis (no_types, lifting) Rep_prog_refine abrh_def cond_mono order_refl pcond_prog.rep_eq)
  done

lemma Upper_abr_subset_Upper_prog:
  "Upper_abr (A \<inter> {P. abrh P = P}) \<subseteq> Upper_prog (A \<inter> {P. abrh P = P})"
  by (simp add: Upper_abr_def)
  
lemma sup_abr_in_Upper_abr:
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow> 
  (\<^bold>\<Squnion>\<^sub>a A) \<in> Upper_abr (A \<inter> {P. abrh P = P})"
   unfolding least_abr_def sup_abr_def
   apply (subst Upper_abr_def)
      apply (subst Upper_abr_def)
  apply auto
  apply (rule someI2_ex)    
   apply (rule exI[where x = "abrh (\<Squnion>\<^sub>pA)"]) 
   apply (simp add:  prog_rep_eq image_def least_def Bex_def)
   apply auto
     apply (metis Healthy_def Rep_prog_H1_H3_closed ndes_hcond_def)
    apply (rule exI[where x = "abrh (\<Squnion>\<^sub>pA)"])
    apply auto[]
    apply (metis (mono_tags, lifting) Collect_cong Rep_prog_eq sup_prog_abrh_in_Upper_prog_Int_abrh)
   apply (simp only: sup_prog_alt_def Bex_def)
   apply (rule someI2_ex)   
   using sup_prog_is_least_Upper_prog 
     apply blast
   apply (metis (no_types, lifting) Rep_prog_inject abrh_def cond_mono least_def 
                                    least_prog.rep_eq image_eqI order_refl 
                                    pcond_prog.rep_eq semilattice_inf_class.inf.orderE utp_order_le)
   apply (simp add: Upper_abr_def least_prog_alt_def)
  done

lemma sup_abr_in_Upper_prog:
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow> 
  \<^bold>\<Squnion>\<^sub>a A \<in> Upper_prog (A \<inter> {P. abrh P = P})"
  by (metis (mono_tags) Int_iff Upper_abr_def sup_abr_in_Upper_abr semilattice_inf_class.inf.right_idem)

lemma sup_abr_least:
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow> abrh z = z \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow>  x \<sqsubseteq> z ) \<Longrightarrow>  
   \<^bold>\<Squnion>\<^sub>a A \<sqsubseteq> z"
  unfolding least_abr_def Upper_abr_def sup_abr_def
  apply auto
  apply (rule someI2_ex)    
   apply (rule exI[where x = "abrh (\<Squnion>\<^sub>pA)"])    
   apply (simp add:  prog_rep_eq image_def least_def Bex_def)
   apply auto
     apply (metis Healthy_def Rep_prog_H1_H3_closed ndes_hcond_def)
    apply (rule exI[where x = "abrh (\<Squnion>\<^sub>pA)"])
    apply auto[]   
      apply (metis (mono_tags, lifting) Collect_cong Rep_prog_eq sup_prog_abrh_in_Upper_prog_Int_abrh)
  unfolding sup_prog_alt_def 
   defer
   apply (simp only: least_prog_alt_def Upper_prog_alt_def)
   apply auto
  apply (rule someI2_ex)
  using sup_prog_is_least_Upper_prog 
    apply auto[1]
  apply (metis (no_types, lifting) Rep_prog_eq Rep_prog_refine abrh_def cond_mono 
                                   least_prog_alt_def order_refl pcond_prog.rep_eq 
                                   semilattice_inf_class.inf.orderE)
  done 
  
lemma sup_prog_abrh_is_least_Upper:
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow> 
   least_prog (abrh (\<Squnion>\<^sub>pA)) (Upper_prog (A \<inter> {P. abrh P = P}) \<inter> {P. abrh P = P})"
  unfolding sup_prog_alt_def 
  apply (rule someI2_ex)    
  using sup_prog_is_least_Upper_prog 
   apply blast
  apply (simp only: least_prog_alt_def Upper_prog_alt_def)
  apply auto
   apply (metis (no_types, lifting) Rep_prog_refine abrh_def cond_mono order_refl pcond_prog.rep_eq)
  unfolding abrh_def
  apply (metis (mono_tags, lifting) if_prog_monoI mem_Collect_eq order_refl subsetCE)
  done

lemma sup_abr_Upper:
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow>  x \<in> A \<Longrightarrow>
    x \<sqsubseteq> \<^bold>\<Squnion>\<^sub>a A" 
  unfolding least_abr_def Upper_abr_def sup_abr_def
  apply auto
  apply (rule someI2_ex)    
   apply (rule exI[where x = "abrh (\<Squnion>\<^sub>pA)"])    
   apply (simp add: sup_prog_abrh_is_least_Upper)
  apply (metis (no_types, lifting) Int_lower1 dual_order.trans least_prog_alt_def 
                                   sup_prog_is_least_Upper_prog sup_prog_Upper 
                                   semilattice_inf_class.inf.orderE subsetCE)
  done
     
lemma sup_abr_is_abrh:
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow>  
   abrh (\<^bold>\<Squnion>\<^sub>a A) = \<^bold>\<Squnion>\<^sub>a A"
  using Upper_abr_def sup_abr_in_Upper_abr 
  by blast       
    
lemma sup_prog_empty:
  "\<^bold>\<Squnion>\<^sub>a {} = abrh ABORT"
  unfolding sup_abr_def
  apply (rule someI2_ex)    
   apply (rule exI[where x = "abrh ABORT"])
   apply (metis (no_types, lifting) Upper_abr_def empty_subsetI least_abr_def semilattice_inf_class.inf_le2 sup_prog_abrh_is_least_Upper sup_prog_empty)
  apply (metis (no_types, lifting) Upper_abr_def empty_subsetI least_abr_def least_prog_unique sup_prog_abrh_is_least_Upper sup_prog_empty)
  done
    
lemma sup_abr_univ:
  "\<^bold>\<Squnion>\<^sub>a {P. abrh P = P} = abrh MAGIC"
  unfolding sup_abr_def
  apply (rule someI2_ex)    
   apply (rule exI[where x = "abrh MAGIC"])
   apply(simp_all add: least_abr_alt_def Upper_abr_alt_def)
   apply (metis UNIV_I abrh_def cond_mono dual_order.refl less_eq_prog.rep_eq  
                pcond_prog.rep_eq skip.rep_eq sup_prog_Upper sup_prog_univ)
  unfolding least_abr_def Upper_abr_def
  apply auto
    apply (simp add: abrh_below_top_abr dual_order.antisym)
  done

lemma sup_abr_is_least_abr_Upper_abr:
  "A \<subseteq> {P. abrh P = P} \<Longrightarrow> least_abr (\<^bold>\<Squnion>\<^sub>a A) (Upper_abr A)"
  unfolding least_abr_def 
  apply auto
   apply (simp add: Upper_abr_def)
  unfolding least_prog_alt_def
  apply auto
    apply (metis (mono_tags) semilattice_inf_class.inf.orderE sup_abr_in_Upper_abr)
    apply (rule sup_abr_least)
    apply (auto simp: Upper_abr_alt_def)  
  done
    
subsection \<open>Fixed points\<close>

definition LFP_abr :: " ('a abr_prog \<Rightarrow> 'a abr_prog) \<Rightarrow> 'a abr_prog" 
  where "LFP_abr F = \<^bold>\<Sqinter>\<^sub>a {x \<in> {P. abrh P = P} . F x \<sqsubseteq> x}" 
    
definition GFP_abr :: " ('a abr_prog \<Rightarrow> 'a abr_prog) \<Rightarrow> 'a abr_prog" 
  where "GFP_abr F = \<^bold>\<Squnion>\<^sub>a {x \<in> {P. abrh P = P} . x \<sqsubseteq> F x}"
    
syntax
  "_amu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>\<mu>\<^sub>a _ \<bullet> _" [0, 10] 10)
  "_anu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>\<nu>\<^sub>a _ \<bullet> _" [0, 10] 10)

notation LFP_abr ("\<^bold>\<mu>\<^sub>a")

notation GFP_abr ("\<^bold>\<nu>\<^sub>a")
  
translations
  "\<^bold>\<mu>\<^sub>a X \<bullet> P" == "CONST LFP_abr (\<lambda> X. P)"
  
translations
  "\<^bold>\<nu>\<^sub>a X \<bullet> P" == "CONST GFP_abr (\<lambda> X. P)"
  
lemma lfp_abr_healthy_comp:
  "\<^bold>\<mu>\<^sub>a F = \<^bold>\<mu>\<^sub>a (F \<circ> abrh)" 
proof -
  have "{P. (abrh P = P) \<and> F P \<sqsubseteq> P} = {P. (abrh P = P) \<and> F (abrh P) \<sqsubseteq> P}"
    by auto
  thus ?thesis
    unfolding LFP_abr_def  
    by simp
qed
  
lemma gfp_abr_healthy_comp:
  "\<^bold>\<nu>\<^sub>a F = \<^bold>\<nu>\<^sub>a (F \<circ> abrh)" 
proof -
  have "{P. (abrh P = P) \<and> P \<sqsubseteq> F P } = {P. (abrh P = P) \<and>  P \<sqsubseteq> F (abrh P) }"
    by auto
  thus ?thesis
    unfolding GFP_abr_def  
    by simp
qed
  
type_synonym '\<alpha> prog_health = "'\<alpha> prog \<Rightarrow> '\<alpha> prog"
  
consts
  prog_hcond :: "('\<T>, '\<alpha>) uthy \<Rightarrow> '\<alpha> prog_health" ("\<H>\<P>\<index>")  
  
definition prog_order :: "'\<alpha> prog_health \<Rightarrow> '\<alpha> prog gorder" where
"prog_order H = \<lparr> carrier = {P. P = H P}, eq = (op =), le = op \<sqsubseteq> \<rparr>"


typedecl ABRH

abbreviation "ABRH \<equiv> UTHY(ABRH,  '\<alpha> abr)"  

  definition abrh_hcond :: "(ABRH, '\<alpha> abr) uthy \<Rightarrow> ('\<alpha> abr) prog_health" where
             "abrh_hcond t = abrh"
  definition abrh_unit :: "(ABRH, '\<alpha> abr) uthy \<Rightarrow> '\<alpha> abr_prog" where
  [upred_defs]: "abrh_unit t = abrh SKIP"  

definition
  "mono_abr_prog F = Mono\<^bsub>(prog_order (abrh_hcond ABRH))\<^esub> F"  

lemma mono_abr_prog_alt_def: 
  "Mono\<^bsub>(prog_order (abrh_hcond ABRH))\<^esub> F = 
   mono_prog (F o abrh) \<and> weak_partial_order (prog_order (abrh_hcond ABRH))"
  apply (simp only : isotone_def prog_rep_eq prog_order_def weak_partial_order_def abrh_hcond_def)
  apply auto
  using ndes_utp_theory.equivalence_axioms apply auto[1]
  using ndes_utp_theory.weak_partial_order_axioms weak_partial_order_def apply auto[1]
           apply (simp add: ndes_utp_theory.equivalence_axioms)
  using ndes_utp_theory.weak_partial_order_axioms weak_partial_order_def apply blast
         apply (metis (no_types, lifting) Abs_prog_Rep_prog_Ncarrier Healthy_if abrh_def abrh_idem cond_mono eq_iff pcond_prog.rep_eq)
        apply (rule equivalence.intro)
          prefer 3
          apply (subst (asm) equivalence.intro)
            prefer 5
            apply (subst (asm) equivalence.intro)
               prefer 7
               apply (subst (asm) weak_partial_order_axioms.intro)
                   prefer 9   
                   apply auto
      apply (subst weak_partial_order_axioms.intro)
          apply auto
      apply (subst (asm) equivalence.intro)
         apply auto
      apply (subst (asm) weak_partial_order_axioms.intro)
          apply auto
      defer
      apply (subst equivalence.intro)
         apply auto
     apply (subst (asm) equivalence.intro)
        apply auto
     apply (subst (asm) weak_partial_order_axioms.intro)
         apply auto
     defer 
     apply (subst equivalence.intro)
        apply auto
    apply (subst weak_partial_order_axioms.intro)
        apply auto
    apply (simp add: Rep_prog_eq)
   apply (simp add: Rep_prog_inject)
  apply (metis Rep_prog_H1_H3_closed Rep_prog_inverse is_Ncarrier_is_ndesigns)
  done

lemma lfp_abr_unfold:
   assumes M:"mono_abr_prog F"
   assumes H: "F \<in> {P. abrh P = P} \<rightarrow> {P. abrh P = P}"
   shows " F (\<^bold>\<mu>\<^sub>a F) = \<^bold>\<mu>\<^sub>a F"
     thm lfp_abr_healthy_comp
     apply (subst lfp_abr_healthy_comp) 
       apply (subst (2) lfp_abr_healthy_comp) 
  unfolding LFP_abr_def
    
  apply (rule order_antisym)
   apply (rule inf_abr_lower)
    apply auto[1]
  thm Pi_mem[OF H]
    apply (insert H)
   apply (subst (asm) Pi_I)
    apply auto

  using H apply auto[1]
    apply (smt CollectI Collect_mono H PiE abrh_subset_member inf_abr_is_abrh)
  defer
       apply (rule inf_abr_greatest)

oops                   
lemma lfp_abrupt_unfold: 
  assumes M:"mono_abr_prog F"
  assumes H: "F \<in> {P. abrh P = P} \<rightarrow> {P. abrh P = P}"  
  shows "\<^bold>\<mu>\<^sub>a F = F (\<^bold>\<mu>\<^sub>a F)"  
    thm lfp_unfold
oops     

  
definition Idempotent :: "'\<alpha> prog_health \<Rightarrow> bool" where
  "Idempotent(H) \<longleftrightarrow> (\<forall> P. H(H(P)) = H(P))"

abbreviation Monotonic :: "'\<alpha> prog_health \<Rightarrow> bool" where
  "Monotonic(H) \<equiv> mono H"
    
locale prog_theory =
  fixes \<T> :: "('\<T>, '\<alpha>) uthy" (structure)
  assumes PHCond_Idem: " \<H>\<P>( \<H>\<P>(P)) =  \<H>\<P>(P)"
begin

  lemma uthy_simp:
    "uthy = \<T>"
    by blast

  text {* A UTP theory fixes @{term "\<T>"}, the structural element denoting the UTP theory. All
    constants associated with UTP theories can then be resolved by the type system. *}

  lemma HCond_Idempotent [closure,intro]: "Idempotent  \<H>\<P>"
    by (simp add: Idempotent_def PHCond_Idem)

  sublocale partial_order "prog_thy_order \<T>"
    by (unfold_locales, simp_all add: prog_order_def)
end
  
interpretation ndes_utp_theory: prog_theory ABRH
  apply (simp add:   abrh_hcond_def utp_theory.intro)


(*interpretation ndes_unital: utp_theory_unital NDES
  apply (unfold_locales, simp_all add: ndes_hcond_def ndes_unit_def)
  using seq_r_H1_H3_closed apply blast
  apply (metis H1_rdesign H3_def Healthy_def' design_skip_idem skip_d_def)
  apply (metis H1_idem H1_left_unit Healthy_def')
  apply (metis H1_H3_commute H3_def H3_idem Healthy_def')
done



interpretation normal_design_theory_continuous: utp_theory_continuous NDES
  rewrites "\<And> P. P \<in> carrier (uthy_order NDES) \<longleftrightarrow> P is \<^bold>N"
  and "carrier (uthy_order NDES) \<rightarrow> carrier (uthy_order NDES) \<equiv> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  and "le (uthy_order NDES) = op \<sqsubseteq>"
  and "A \<subseteq> carrier (uthy_order NDES) \<longleftrightarrow> A \<subseteq> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"  
  and "eq (uthy_order NDES) = op ="  
  by (unfold_locales, simp_all add: ndes_hcond_def H1_H3_Continuous utp_order_def)*)

  
     
(*section {*algebraic laws*} 

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
done *)
    
end
