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

theory vcg

  imports "../../Midend-IVL/Isabelle-UTP-Extended/HoareLogic/TotalCorrectness/utp_hoare_ndes_prog"
          "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

section \<open>VCG\<close> 
  
subsection \<open>VCG General Purpose Tactics\<close>      
text \<open>Automating premises insertion\<close>  
method_setup insert_assms = \<open>Scan.succeed (fn _ => CONTEXT_METHOD (fn facts => fn (ctxt,st) => let
   val tac = HEADGOAL (Method.insert_tac ctxt facts)
   val ctxt = Method.set_facts [] ctxt
 in Method.CONTEXT ctxt (tac st)
 end))\<close>                      
                       
text \<open>The defer processing and the thin_tac processing in the sequel was inspired by tutorial5.thy in Peter Lammich course
        \url{https://bitbucket.org/plammich/certprog_public/downloads/}\<close>
 
subsection \<open>Deterministic Repeated Elimination Rule\<close>
text \<open>Attention: Slightly different semantics than @{method elim}: repeats the 
  rule as long as possible, but only on the first subgoal.\<close>

method_setup vcg_elim_determ = \<open>
  Attrib.thms >> (fn thms => fn ctxt => 
    SIMPLE_METHOD (REPEAT_DETERM1 (HEADGOAL (ematch_tac ctxt thms))))\<close>
text \<open>The \<open>DETERM\<close> combinator on method level\<close>
  
method_setup determ = \<open>
  Method.text_closure >>
    (fn (text) => fn ctxt => fn using => fn st =>
      Seq.DETERM (Method.evaluate_runtime text ctxt using) st
    )
\<close>        
(*method insert_assms =  tactic \<open>@{context} |>  Assumption.all_prems_of |> (@{context} |>  Method.insert_tac) |> FIRSTGOAL\<close>*)

text \<open>vcg_can_defer is a tactic that succeed if the conclusion of a goal is not Hoare triple
       or if it has no DEFERRED markup\<close>  
  
definition DEFERRED :: "bool \<Rightarrow> bool" where "DEFERRED P = P"
lemma DEFERREDD: "DEFERRED P \<Longrightarrow> P" by (auto simp: DEFERRED_def)

method vcg_can_defer =
  (match conclusion 
      in "DEFERRED _" \<Rightarrow> fail  -- \<open>Refuse to defer already deferred goals\<close>
       \<bar>
         "\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>P" \<Rightarrow> fail  -- \<open>Refuse to defer Hoare triples (They are no VCs!)\<close>
       \<bar> 
         "_" \<Rightarrow> succeed)
       
method vcg_defer = (vcg_can_defer, rule DEFERREDD, tactic \<open>FIRSTGOAL defer_tac\<close>)    
  
subsection \<open>VCG Post Processing Tactics\<close> 
  
text \<open>Tactics and methods in this section are used to do Post-Processing on the generated VCs.
      Namely, The application of symbolic execution laws from the theory usubst
      to the VCs in a very controlled way.\<close>  
  
lemma vwb_lens_weak[simp]: 
  "vwb_lens x \<Longrightarrow> weak_lens x"
  by simp    

text \<open>substitution simplifier for debugging mode\<close>  
  
definition "ZERO_SUBST_TAG expr = True" 
definition "ONE_SUBST_TAG expr = True"
definition "LIT_SUBST_TAG expr = True"
definition "VAR_SUBST_TAG expr = True"  
definition "UOP_SUBST_TAG expr = True"    
definition "BOP_SUBST_TAG expr = True"
definition "TROP_SUBST_TAG expr= True"
definition "QTOP_SUBST_TAG expr = True"
  
lemma ZERO_SUBST_DEBUG: 
  "(ZERO_SUBST_TAG 0 \<Longrightarrow> thesis) \<Longrightarrow> thesis" 
  unfolding ZERO_SUBST_TAG_def 
  by blast 

lemma ONE_SUBST_DEBUG: 
  "(ONE_SUBST_TAG 1 \<Longrightarrow> thesis) \<Longrightarrow> thesis" 
  unfolding ONE_SUBST_TAG_def 
  by blast 
    
lemma LIT_SUBST_DEBUG: 
  "(LIT_SUBST_TAG (lit v) \<Longrightarrow> thesis) \<Longrightarrow> thesis" 
  unfolding LIT_SUBST_TAG_def 
  by blast  

lemma VAR_SUBST_DEBUG: 
  "(VAR_SUBST_TAG (utp_expr.var x) \<Longrightarrow> thesis) \<Longrightarrow> thesis" 
  unfolding VAR_SUBST_TAG_def 
  by blast
    
lemma UOP_SUBST_DEBUG: 
  "(UOP_SUBST_TAG (uop f a) \<Longrightarrow> thesis) \<Longrightarrow> thesis" 
  unfolding UOP_SUBST_TAG_def 
  by blast
    
lemma BOP_SUBST_DEBUG: 
  "(BOP_SUBST_TAG (bop f a b) \<Longrightarrow> thesis) \<Longrightarrow> thesis" 
  unfolding BOP_SUBST_TAG_def 
  by blast     
    
lemma EQ_UPRED_SUBST_DEBUG: 
  "(BOP_SUBST_TAG (eq_upred a b) \<Longrightarrow> thesis) \<Longrightarrow> thesis" 
  unfolding BOP_SUBST_TAG_def 
  by blast
    
lemma TROP_SUBST_DEBUG: 
  "(TROP_SUBST_TAG (trop f a b c) \<Longrightarrow> thesis) \<Longrightarrow> thesis" 
  unfolding TROP_SUBST_TAG_def 
  by blast     
    
lemma QTOP_SUBST_DEBUG: 
  "(QTOP_SUBST_TAG (qtop f a b c d) \<Longrightarrow> thesis) \<Longrightarrow> thesis" 
  unfolding QTOP_SUBST_TAG_def 
  by blast 
    
method subst_debugger = 
    (*Zero*)
   (match conclusion in  
    "_ (\<lambda> _. subst _ 0)"  \<Rightarrow>
     \<open>rule ZERO_SUBST_DEBUG , (simp only:subst_zero)\<close>)
    (*Zero*)   
    | (match conclusion in   
    "_ (\<lambda> _. subst _ 1)"  \<Rightarrow>
     \<open>rule ONE_SUBST_DEBUG , (simp only:subst_one)\<close>)
    (*UTP vars*) 
    |(match conclusion in 
    "_ (\<lambda> _. (subst _ (utp_expr.var x)))" for x \<Rightarrow>
     \<open>rule VAR_SUBST_DEBUG[where x= x], (simp only:subst_var)\<close>)
   (*UTP Literals*)
    |(match conclusion in 
    "_ (\<lambda> _ . (subst _ (lit v)))" for v \<Rightarrow>
     \<open>rule LIT_SUBST_DEBUG[where v= v], (simp only:subst_lit)\<close>)
    (*UTP Unary operation*)
    | (match conclusion in 
    "_ (\<lambda> _ .(subst _ (uop f a)))" for f a \<Rightarrow>
     \<open>rule UOP_SUBST_DEBUG[where f= f and a = a], simp only: subst_uop\<close>) 
    (*Derived UOP for UTP Logical Operators*)
    | (match conclusion in 
    "_ (\<lambda> _ .(subst _ (\<not> a)))" for  a \<Rightarrow>
     \<open>rule UOP_SUBST_DEBUG[where f= "Not" and a = a], simp only: subst_uop\<close>)
   | (match conclusion in 
    "_ (\<lambda> _. (subst _ (\<^bold>\<forall>x \<bullet> P x)))" for P \<Rightarrow>
     \<open>rule UOP_SUBST_DEBUG[where f= "All" and a= "(\<lambda>x \<bullet> P x)" ] , simp only: utp_pred.subst_shAll\<close>) 
   | (match conclusion in 
    "_ (\<lambda> _. (subst _ (\<^bold>\<exists>x \<bullet> P x)))" for P \<Rightarrow>
     \<open>rule UOP_SUBST_DEBUG[where f= "Ex" and a= "(\<lambda>x \<bullet> P x)" ] , simp only: utp_pred.subst_shEx\<close>)
   (*UTP Binary operation*)
    | (match conclusion in 
    "_ (\<lambda> _ . (subst _ (bop f a b)))" for f a b \<Rightarrow>
     \<open> rule BOP_SUBST_DEBUG[where f= f and a= a and b = b], simp only:subst_bop\<close>) 
   (*Derived BOP for UTP Arith Operators*)
   | (match conclusion in 
    "_ (\<lambda> _. (subst _ (a =\<^sub>u b)))" for a b \<Rightarrow>
     \<open>rule EQ_UPRED_SUBST_DEBUG[where a= a and b = b], simp only:subst_eq_upred\<close>)
   | (match conclusion in 
    "_ (\<lambda> _. (subst _ (a + b)))" for a b \<Rightarrow>
     \<open>rule BOP_SUBST_DEBUG[where f= "(op +)" and a= a and b = b], simp only:subst_plus\<close>)
   | (match conclusion in 
    "_ (\<lambda> _. (subst _ (a - b)))" for a b \<Rightarrow>
     \<open> rule BOP_SUBST_DEBUG[where f= "(op -)" and a= a and b = b], simp only:subst_minus\<close>)
    | (match conclusion in 
    "_ (\<lambda> _. (subst _ (a * b)))" for a b \<Rightarrow>
     \<open>rule BOP_SUBST_DEBUG[where f= "(op *)" and a= a and b = b],simp only:subst_times \<close>)
    | (match conclusion in 
    "_ (\<lambda> _. (subst _ (a div b)))" for a b \<Rightarrow>
     \<open>rule BOP_SUBST_DEBUG[where f= "(op div)" and a= a and b = b], simp only:subst_div\<close>)
    (*Derived BOP Logical Operators*)
    | (match conclusion in 
    "_ (\<lambda> _. (subst _ (a \<and> b)))" for a b \<Rightarrow>
     \<open>rule BOP_SUBST_DEBUG[where f= "(op \<and>)" and a= a and b = b] , simp only: utp_pred.subst_conj\<close>)
    | (match conclusion in 
    "_ (\<lambda> _. (subst _ (a \<or> b)))" for a b \<Rightarrow>
     \<open>rule BOP_SUBST_DEBUG[where f= "(op \<or>)" and a= a and b = b] , simp only: utp_pred.subst_disj\<close>)
    | (match conclusion in 
    "_ (\<lambda> _. (subst _ (a \<Rightarrow> b)))" for a b \<Rightarrow>
     \<open>rule BOP_SUBST_DEBUG[where f= "(op \<longrightarrow>)" and a= a and b = b] , simp only: utp_pred.subst_impl\<close>)     
   | (match conclusion in 
    "_ (\<lambda> _. (subst _ (a \<Leftrightarrow> b)))" for a b \<Rightarrow>
     \<open>rule BOP_SUBST_DEBUG[where f= "(op \<longleftrightarrow>)" and a= a and b = b] , simp only: utp_pred.subst_iff\<close>)
   | (match conclusion in 
    "_ (\<lambda> _. (subst _ (a \<sqinter> b)))" for a b \<Rightarrow>
     \<open>rule BOP_SUBST_DEBUG[where f= "(op \<sqinter>)" and a= a and b = b] , simp only: utp_pred.subst_sup\<close>)
    | (match conclusion in 
    "_ (\<lambda> _. (subst _ (a \<squnion> b)))" for a b \<Rightarrow>
     \<open>rule BOP_SUBST_DEBUG[where f= "(op \<squnion>)" and a= a and b = b] , simp only: utp_pred.subst_inf\<close>)
   (*UTP Ternary operation*)
    | (match conclusion in 
    "_ (\<lambda> _. (subst _ (trop f a b c)))" for f a b c\<Rightarrow>
     \<open>rule TROP_SUBST_DEBUG[where f=f and a=a and b=b and c=c] , simp only:subst_trop\<close>)
    (*UTP Quaternary operation*)
    | (match conclusion in 
    "_ (\<lambda> _. (subst _ (qtop f a b c d)))" for f a b c d\<Rightarrow>
     \<open>rule QTOP_SUBST_DEBUG[where f=f and a=a and b=b and c=c and d=d],  simp only:subst_qtop\<close>)


definition "SUBST_ID_LOOKUP_TAG \<sigma> x = True"  
definition "SUBST_UPD_LOOKUP_TAG \<sigma> x y = True" 
definition "UEX_BOUNDED x = x" 

lemma SUBST_UPD_LOOKUP_DEBUG: 
  "(SUBST_UPD_LOOKUP_TAG \<sigma> (UEX_BOUNDED x) y \<Longrightarrow> thesis) \<Longrightarrow> thesis" 
  unfolding SUBST_UPD_LOOKUP_TAG_def 
  by blast 

lemma SUBST_ID_LOOKUP_DEBUG: 
  "(SUBST_ID_LOOKUP_TAG id y \<Longrightarrow> thesis) \<Longrightarrow> thesis" 
  unfolding SUBST_ID_LOOKUP_TAG_def 
  by blast 
    
method subst_lookup_debugger = 
     (match conclusion in  
     "_ (\<lambda> _. (usubst_lookup id y))" for  y  \<Rightarrow>
      \<open>rule SUBST_ID_LOOKUP_DEBUG[where y=y], 
       (simp only: usubst_lookup_id)\<close>)
    |
     (match conclusion in  
      "_ (\<lambda> _. (usubst_lookup (subst_upd \<sigma> x  _) y))" for \<sigma> x y  \<Rightarrow>
       \<open>rule SUBST_UPD_LOOKUP_DEBUG[where \<sigma>=\<sigma> and x=x and y=y], 
        (simp only: usubst_lookup_upd_indep usubst_lookup_ovar_unrest
                    usubst_lookup_ivar_unrest usubst_lookup_upd 
                    vwb_lens_mwb vwb_lens_wb lens_indep_sym)\<close>) 
       
text \<open>very well behaved lens simplifier for debugging mode\<close>  
 
definition "VWB_VAR_TAG x = True"
definition "WB_VAR_TAG x = True"
definition "WEAK_VAR_TAG x = True"
definition "MWB_VAR_TAG x = True"  

lemma VWB_VAR_DEBUG: 
  obtains e where "e = vwb_lens x " "VWB_VAR_TAG x" 
  unfolding VWB_VAR_TAG_def 
  by blast

lemma MWB_VAR_DEBUG: 
  obtains e where "e = mwb_lens x " "MWB_VAR_TAG x" 
  unfolding MWB_VAR_TAG_def 
  by blast   
    
lemma WB_VAR_DEBUG: 
  obtains e where "e = wb_lens x " "WB_VAR_TAG x" 
  unfolding WB_VAR_TAG_def 
  by blast  
    
lemma WEAK_VAR_DEBUG: 
  obtains e where "e = wb_lens x " "WEAK_VAR_TAG x" 
  unfolding WEAK_VAR_TAG_def 
  by blast  

method_setup print_VWB_VAR_DEBUG  = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (print_tac ctxt "VWB_VAR_DEBUG is not applied"))\<close>  

method vwb_lens_debugger =
  (match conclusion in 
   "vwb_lens x" for x \<Rightarrow>
   \<open>(rule VWB_VAR_DEBUG[where x= x],assumption) (*if this fails add a debug message here*)\<close>)
  |(match conclusion in 
   "wb_lens x" for x \<Rightarrow>
   \<open>rule WB_VAR_DEBUG[where x= x],(simp only: vwb_lens_wb)(*if this fails add a debug message here*)\<close>)
  |(match conclusion in 
   "mwb_lens x" for x \<Rightarrow>
   \<open>rule MWB_VAR_DEBUG[where x= x],(simp only: vwb_lens_mwb)(*if this fails add a debug message here*)\<close>)
  |(match conclusion in 
   "mwb_lens x" for x \<Rightarrow>
   \<open>rule WEAK_VAR_DEBUG[where x= x],(simp only: vwb_lens_weak)(*if this fails add a debug message here*)\<close>)

definition "WF_TAG expr = True"
   
lemma WF_DEBUG:
 "(WF_TAG expr \<Longrightarrow> thesis) \<Longrightarrow> thesis" 
  unfolding WF_TAG_def by simp

method wf_debugger =
  (match conclusion in 
   "wf expr" for expr \<Rightarrow>
   \<open>rule WF_DEBUG[where expr = expr], simp\<close>) 
 
text \<open>Post processing for debugging mode\<close>  
          
method vcg_upreds_post_processing_debugger = 
       (vwb_lens_debugger(*TODO: if this fails add a debug message here*)
        |wf_debugger(*TODO: if this fails add a debug message here*)
        |subst_debugger(*TODO: if this fails add a debug message here*)
        |subst_lookup_debugger(*TODO: if this fails add a debug message here*))
        
text \<open>substitution simplifier for non debugging mode\<close>

named_theorems usubst_simplifier 
declare usubst[usubst_simplifier] 
declare vwb_lens_weak[usubst_simplifier]
declare vwb_lens_mwb[usubst_simplifier] 
declare vwb_lens_wb[usubst_simplifier] 
declare lens_indep_sym[usubst_simplifier] 

text \<open>very well behaved lens simplifier for non-debugging mode\<close>
  
named_theorems vwb_simplifier
declare vwb_lens_wb[vwb_simplifier]
declare vwb_lens_mwb[vwb_simplifier]
declare vwb_lens_weak[vwb_simplifier]
declare bij_lens_vwb[vwb_simplifier]
declare Lens_Algebra.id_bij_lens[vwb_simplifier] 
 
text \<open>Post processing for non debugging mode\<close>  

method vcg_upreds_post_processing = 
        (assumption|simp only: vwb_simplifier)
        |simp
        |(simp only:usubst_simplifier)
  
subsection \<open>VCG Goal Beautify Tactics\<close>    

text \<open>Tactics and methods in this section are used to beautify the goals before presenting them to the user.
      Namely, after the application of post-processing a lot of semantic machinery and debugging information
      remains existing in the different proof goals. The methods below clean it up since these 
      assumptions are useless at this point.\<close>
  
definition "LVAR L x = True"  
  
lemma GET_REMOVER: obtains x where "lens_get L s = x" "LVAR L x" unfolding LVAR_def by blast
 
(*Prototype by Peter for variable renaming*)
  
method_setup get_disambiguator = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (fn i => fn st => 
  if i > Thm.nprems_of st then all_tac st
  else
    let 
      fun cnv (Const (@{const_name Trueprop},_)$ (Const (@{const_name LVAR},_) $(Free (name,_)) $ Bound i)) = SOME (name,i)
        | cnv _ = NONE
      val (_, _, Bi, _) = Thm.dest_state (st, i)
      val free_names = Term.fold_aterms (fn Free (x, _) => insert (op =) x | _ => I) Bi [];
      val newnames = Logic.get_goal (Thm.prop_of st) i 
        |> Logic.strip_assums_hyp 
        |> map_filter cnv
        |> sort (apply2 snd #> int_ord #> rev_order)
        |> (fn newnames =>
             fold_map (fn (name, i) => fn free_names =>
                         let fun aux n =
                               if List.exists (fn n0 => n0 = n) free_names then aux (n ^ "'") else n
                             val name = aux name
                         in ((name, i), name :: free_names) end)
                      newnames
                      free_names)
        |> #1
        |> map fst
    in 
      rename_tac newnames i st 
    end))\<close>  
    
(*Frederic's method for removing get functions from the goal*)    
method get_remover =
   (match conclusion in 
          "_ (put\<^bsub>x\<^esub> A (get\<^bsub>x\<^esub> _))" for x A \<Rightarrow> \<open>fail\<close>  --{*In case that a proof engineer forget to specify LENS WELL BEHAVED assumptions*}
         \<bar>"_ (put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> A _ ) _)" for x A \<Rightarrow> \<open>fail\<close>  --{*In case that a proof engineer forget to specify LENS WELL BEHAVED assumptions*}
         \<bar>"_ (get\<^bsub>_\<^esub> (put\<^bsub>x\<^esub> A _))" for x A \<Rightarrow> \<open>fail\<close>  --{*In case that a proof engineer forget to specify LENS INDEP assumptions*}
         \<bar>"_ (get\<^bsub>x\<^esub> (put\<^bsub>_\<^esub> A _))" for x A \<Rightarrow> \<open>fail\<close> --{*In case that a proof engineer forget to specify LENS INDEP assumptions*}
         \<bar>"_ (get\<^bsub>x\<^esub> A)" for x A \<Rightarrow> \<open>rule GET_REMOVER[where L= x and s= A], simp only:\<close>)+,
  get_disambiguator,
  vcg_elim_determ thin_rl[of "lens_get _ _ = _"] thin_rl[of "LVAR _ _"]
 
method get_remover_auto = get_remover, (auto simp: gcd_diff1_nat) []
method get_remover_metis = get_remover, metis gcd.commute gcd_diff1_nat not_le
        
named_theorems beautify_thms     
lemma thin_vwb_lens[beautify_thms]: "vwb_lens l \<Longrightarrow> P \<Longrightarrow> P" . 
lemma thin_weak_lens[beautify_thms]: "weak_lens l \<Longrightarrow> P \<Longrightarrow> P" .    
lemma [beautify_thms]: "\<not> ief_lens i \<Longrightarrow> P \<Longrightarrow> P" .  
lemma [beautify_thms]: "i\<bowtie>j \<Longrightarrow> P \<Longrightarrow> P" .  
lemma [beautify_thms]: "i\<noteq>(j::_\<Longrightarrow>_) \<Longrightarrow> P \<Longrightarrow> P" .
lemma [beautify_thms]: "i\<noteq>(j::_\<Longrightarrow>_) \<longrightarrow> i \<bowtie> j \<Longrightarrow> P \<Longrightarrow> P" .    
lemma [beautify_thms]: "get\<^bsub>i\<^esub> A = x \<Longrightarrow> P \<Longrightarrow> P" .
    
subsection \<open>Custom UTP tactics for VCG\<close>
  
text \<open>For debugging purpose we re-construct utp tactics. It allows  controlled  execution 
       of these tactics.\<close> 
 (*TODO: Debugging version of these tactics*)

text \<open>a generic UTP tactic inspired by @{method gen_rel_tac} and @{method gen_pred_tac}\<close>
  
method utp_tac_control methods utp_defs utp_transfer utp_rewrites utp_solve utp_interp =
  utp_defs? ; utp_transfer, utp_rewrites?, utp_interp?, utp_solve
                                                   
text \<open>For UTP transfer tactics see @{method slow_uexpr_transfer} and @{method fast_uexpr_transfer}\<close>

text \<open>For UTP interp tactics see @{method uexpr_interp_tac}\<close>  

text \<open>For UTP solve tactics see @{method utp_simp_tac}\<close>  
  
subsubsection \<open> UTP predicates tactics\<close>

method upreds_defs = (unfold upred_defs)[1] 
method upreds_rewrites =  (simp add: fun_eq_iff lens_defs upred_defs alpha_splits Product_Type.split_beta)
  
method upreds_simp       = utp_tac_control upreds_defs fast_uexpr_transfer upreds_rewrites uexpr_interp_tac utp_simp_tac
method upreds_simp_slow  = utp_tac_control upreds_defs slow_uexpr_transfer upreds_rewrites uexpr_interp_tac utp_simp_tac
method upreds_auto       = utp_tac_control upreds_defs fast_uexpr_transfer upreds_rewrites uexpr_interp_tac utp_auto_tac
method upreds_auto_slow  = utp_tac_control upreds_defs slow_uexpr_transfer upreds_rewrites uexpr_interp_tac utp_auto_tac
method upreds_blast      = utp_tac_control upreds_defs fast_uexpr_transfer upreds_rewrites uexpr_interp_tac utp_blast_tac
method upreds_blast_slow = utp_tac_control upreds_defs slow_uexpr_transfer upreds_rewrites uexpr_interp_tac utp_blast_tac

subsubsection \<open> UTP relations tactics\<close>

method urels_defs = (unfold upred_defs urel_defs)[1] 
method urels_rewrites = (simp add: fun_eq_iff relcomp_unfold OO_def
    lens_defs upred_defs alpha_splits Product_Type.split_beta)  
method urels_simp       = utp_tac_control urels_defs fast_uexpr_transfer urels_rewrites uexpr_interp_tac utp_simp_tac
method urels_simp_slow  = utp_tac_control urels_defs slow_uexpr_transfer urels_rewrites uexpr_interp_tac utp_simp_tac
method urels_auto       = utp_tac_control urels_defs fast_uexpr_transfer urels_rewrites uexpr_interp_tac utp_auto_tac
method urels_auto_slow  = utp_tac_control urels_defs slow_uexpr_transfer urels_rewrites uexpr_interp_tac utp_auto_tac
method urels_blast      = utp_tac_control urels_defs fast_uexpr_transfer urels_rewrites uexpr_interp_tac utp_blast_tac
method urels_blast_slow = utp_tac_control urels_defs slow_uexpr_transfer urels_rewrites uexpr_interp_tac utp_blast_tac
 
subsection \<open>VCG Core Tactics\<close> 
  
text \<open>In this section we define the core tactics for the VCG. Namely, tactics for the computational mode
such as weakest pre-condition and strongest post_condition rules. Also tactics for symbolic execution
on the generated verification conditions are defined.\<close>  
    
method hoare_sp_vcg_pre = (simp only: seqr_assoc[symmetric])?, rule post_weak_prog_hoare  

method hoare_wp_vcg_pre = (simp only: seqr_assoc[symmetric])?, rule pre_str_prog_hoare  

method hoare_sp_rule_apply = rule hoare_sp_rules
  
method hoare_wp_rule_apply = rule hoare_wp_rules

method vcg_step methods vcg_reasoning_method = 
       (vcg_reasoning_method | vcg_defer)

text \<open>A one step vcg without post processing nor debugging information. The output of this
      method is: for the goal, on which it is applied to, a upred.\<close>
  
method hoare_sp_vcg_step = vcg_step hoare_sp_rule_apply 
  
method hoare_wp_vcg_step = vcg_step hoare_wp_rule_apply
  
text \<open>A multiple step vcg without post processing nor debugging information. The output of this
      method is proof goals of the form of upreds.\<close>  
  
method sp = hoare_sp_vcg_pre, hoare_sp_vcg_step+ , (unfold DEFERRED_def)

method wp = hoare_wp_vcg_pre, hoare_wp_vcg_step+ , (unfold DEFERRED_def)  
  
named_theorems lens_laws_vcg_simps

lemmas [lens_laws_vcg_simps] =
  lens_indep.lens_put_irr1
  lens_indep.lens_put_irr2
  
method vcg_hol_post_processing_debugger = 
   (upreds_simp)?, (simp only: lens_laws_vcg_simps)?
  
named_theorems lens_get_lens_put_simplifer
declare lens_laws_vcg_simps[lens_get_lens_put_simplifer]  
declare vwb_simplifier[lens_get_lens_put_simplifer]
declare mwb_lens.put_put[lens_get_lens_put_simplifer] 
declare weak_lens.put_get[lens_get_lens_put_simplifer]
declare wb_lens.get_put[lens_get_lens_put_simplifer]
declare bij_lens.strong_get_put[lens_get_lens_put_simplifer]
  
method vcg_hol_post_processing = 
   (upreds_simp)?, (auto simp only: lens_get_lens_put_simplifer)?

text \<open>Lens indep all simplifier for non debugging mode\<close>
  
named_theorems lens_indep_all_simplifier
declare distinct.simps[lens_indep_all_simplifier]
declare HOL.conj_assoc[lens_indep_all_simplifier]
declare HOL.simp_thms[lens_indep_all_simplifier]
declare List.list.set[lens_indep_all_simplifier]
declare Set.ball_simps[lens_indep_all_simplifier]  
declare Set.insert_iff[lens_indep_all_simplifier] 
declare Set.empty_iff [lens_indep_all_simplifier]
               
method hoare_sp_vcg_steps_pp_debugger = 
    (sp; ((unfold pr_var_def in_var_def out_var_def)?, (unfold lens_indep_all_alt)?,
                               ((simp only: lens_indep_all_simplifier)+ (*TODO: Substitute with a debug mode version*))?,
                                 clarsimp?, 
                                 (vcg_upreds_post_processing_debugger+)?,
                                 vcg_hol_post_processing_debugger))

method symbolic_execution =
  ((unfold pr_var_def in_var_def out_var_def)?, (unfold lens_indep_all_alt)?,
                               ((simp only: lens_indep_all_simplifier)+)?,
                                 clarsimp?,
                                 (vcg_upreds_post_processing+)?,
                                  vcg_hol_post_processing(*TODO: ADD SOLVING STEP HERE*))
                                
(*method hoare_sp_vcg_steps_pp = 
    (sp; symbolic_execution)  

method vcg_hoare_sp_steps_pp_beautify = 
  (hoare_sp_vcg_steps_pp; get_remover?; (vcg_elim_determ beautify_thms)?)*)

    
method vcg methods vcg_reasoning_method =
  (vcg_reasoning_method ; symbolic_execution); get_remover?; (vcg_elim_determ beautify_thms)?
    
end

