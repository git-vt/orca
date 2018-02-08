(*****************************************************************************************)
(* Orca: A Functional Correctness Verifier for Imperative Programs Based on Isabelle/UTP *)
(*                                                                                       *)
(* Copyright (c) 2016-2018 Virginia Tech, USA                                            *)
(* This software may be distributed and modified according to the terms of               *)
(* the GNU Lesser General Public License version 3.0 or any later version.               *)
(* Note that NO WARRANTY is provided.                                                    *)
(* See CONTRIBUTORS, LICENSE and CITATION files for details.                             *)
(*****************************************************************************************)

theory utp_heap
imports   "../../../Isabelle-UTP/utp/utp" 
          "../../../Isabelle-UTP/theories/utp_designs"  
          "../../umm_heap/TypHeap"
          "../../hoare/AlgebraicLaws/Rel&Des/Algebraic_Laws_aux"
begin
subsection {*UTP heap alphabet*}

text {*
*}

alphabet cp_hp = des_vars +
  heap_raw:: "heap_raw_state"
term "heap_raw"

declare cp_hp.splits [alpha_splits]

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

interpretation cp_hp:
  lens_interp "\<lambda> (ok, r) . (ok, heap_raw\<^sub>v r, more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done
interpretation cp_hp_rel: lens_interp "\<lambda>(ok, ok', r, r').
  (ok, ok', heap_raw\<^sub>v r, heap_raw\<^sub>v r', more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

subsubsection {*Type lifting*}

type_synonym  ('\<alpha>) cphp = "('\<alpha>) cp_hp_scheme des"
type_synonym ('\<alpha>,'\<beta>) rel_cphp  = "(('\<alpha>) cphp, ('\<beta>) cphp) rel"
type_synonym ('\<alpha>) hrel_cphp  = "(('\<alpha>) cphp) hrel"

subsubsection {*Syntactic type setup*}

translations
  (type) "('\<alpha>) cphp" <= (type) " ('\<alpha>) cp_hp_scheme des"
  (type) "('\<alpha>) cphp" <= (type) " ('\<alpha>) cp_hp_ext des"
  (type) "('\<alpha>,'\<beta>) rel_cphp" <= (type) "(('\<alpha>) cphp, ('\<beta>) cphp) rel"

notation cp_hp_child_lens\<^sub>a ("\<Sigma>\<^sub>h\<^sub>p")
notation cp_hp_child_lens ("\<Sigma>\<^sub>H\<^sub>P")

syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>H\<^sub>P")
  "_svid_st_a"  :: "svid" ("\<Sigma>\<^sub>h\<^sub>p")
translations
  "_svid_st_alpha" => "CONST cp_hp_child_lens"
   "_svid_st_a" => "CONST cp_hp_child_lens\<^sub>a"

syntax
  "_top_abr" :: "logic" ("\<top>\<^sub>H\<^sub>P")
  "_bot_abr" :: "logic" ("\<bottom>\<^sub>H\<^sub>P")

translations
  "\<top>\<^sub>H\<^sub>P" => "(CONST not_upred (CONST utp_expr.var (CONST ivar CONST ok)))"
  "\<bottom>\<^sub>H\<^sub>P" => "true"
  

subsection {*Substitution lift and drop*}

abbreviation lift_rel_usubst_cpa ("\<lceil>_\<rceil>\<^sub>S\<^sub>H\<^sub>P")
where "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>H\<^sub>P \<equiv> \<sigma> \<oplus>\<^sub>s (\<Sigma>\<^sub>H\<^sub>P \<times>\<^sub>L \<Sigma>\<^sub>H\<^sub>P)"

abbreviation lift_usubst_cpa ("\<lceil>_\<rceil>\<^sub>s\<^sub>H\<^sub>P")
where "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>H\<^sub>P \<equiv> \<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s\<rceil>\<^sub>S\<^sub>H\<^sub>P"

abbreviation drop_cpa_rel_usubst ("\<lfloor>_\<rfloor>\<^sub>S\<^sub>H\<^sub>P")
where "\<lfloor>\<sigma>\<rfloor>\<^sub>S\<^sub>H\<^sub>P \<equiv> \<sigma> \<restriction>\<^sub>s (\<Sigma>\<^sub>H\<^sub>P \<times>\<^sub>L \<Sigma>\<^sub>H\<^sub>P)"

abbreviation drop_cpa_usubst ("\<lfloor>_\<rfloor>\<^sub>s\<^sub>H\<^sub>P")
where "\<lfloor>\<sigma>\<rfloor>\<^sub>s\<^sub>H\<^sub>P \<equiv> \<lfloor>\<lfloor>\<sigma>\<rfloor>\<^sub>S\<^sub>H\<^sub>P\<rfloor>\<^sub>s"

subsection {*UTP-Relations lift and drop*}

abbreviation lift_rel_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>H\<^sub>P")
where "\<lceil>P\<rceil>\<^sub>H\<^sub>P \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>H\<^sub>P \<times>\<^sub>L \<Sigma>\<^sub>H\<^sub>P)"

abbreviation lift_pre_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>H\<^sub>P\<^sub><")
where "\<lceil>p\<rceil>\<^sub>H\<^sub>P\<^sub>< \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub><\<rceil>\<^sub>H\<^sub>P"

abbreviation lift_post_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>H\<^sub>P\<^sub>>")
where "\<lceil>p\<rceil>\<^sub>H\<^sub>P\<^sub>> \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub>>\<rceil>\<^sub>H\<^sub>P"

abbreviation drop_cpa_rel_uexpr ("\<lfloor>_\<rfloor>\<^sub>H\<^sub>P")
where "\<lfloor>P\<rfloor>\<^sub>H\<^sub>P \<equiv> P \<restriction>\<^sub>p (\<Sigma>\<^sub>H\<^sub>P \<times>\<^sub>L \<Sigma>\<^sub>H\<^sub>P)"

abbreviation drop_cpa_pre_uexpr ("\<lfloor>_\<rfloor>\<^sub><\<^sub>H\<^sub>P")
where "\<lfloor>P\<rfloor>\<^sub><\<^sub>H\<^sub>P \<equiv> \<lfloor>\<lfloor>P\<rfloor>\<^sub>H\<^sub>P\<rfloor>\<^sub><"

abbreviation drop_cpa_post_uexpr ("\<lfloor>_\<rfloor>\<^sub>>\<^sub>H\<^sub>P")
where "\<lfloor>P\<rfloor>\<^sub>>\<^sub>H\<^sub>P \<equiv> \<lfloor>\<lfloor>P\<rfloor>\<^sub>H\<^sub>P\<rfloor>\<^sub>>"

subsection{*Healthiness conditions*}

subsection{*Control flow statements*}
text
{**}

definition skip_hp :: "('\<alpha>) hrel_cphp" ("SKIP\<^sub>H\<^sub>P")
where [urel_defs]:
  "SKIP\<^sub>H\<^sub>P = (\<lceil>true\<rceil>\<^sub>H\<^sub>P \<turnstile> \<lceil>II\<rceil>\<^sub>H\<^sub>P)"

definition assigns_hp :: " '\<alpha> usubst \<Rightarrow> ('\<alpha>) hrel_cphp" ("\<langle>_\<rangle>\<^sub>H\<^sub>P")
where [urel_defs]: 
  "assigns_hp \<sigma> =(\<lceil>true\<rceil>\<^sub>H\<^sub>P \<turnstile> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>H\<^sub>P)"

syntax
  "_assignmentabr" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr "\<Midarrow>" 72)

translations
  "_assignmentabr xs vs" => "CONST assigns_hp (_mk_usubst (CONST id) xs vs)"
  "x \<Midarrow> v" <= "CONST assigns_hp (CONST subst_upd (CONST id) (CONST svar x) v)"
  "x \<Midarrow> v" <= "CONST assigns_hp (CONST subst_upd (CONST id) x v)"
  "x,y \<Midarrow> u,v" <= "CONST assigns_hp (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"

subsection{*Conditional*}

abbreviation If_hp :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_cphp \<Rightarrow> ('\<alpha>) hrel_cphp \<Rightarrow> ('\<alpha>) hrel_cphp" ("bif (_)/ then (_) else (_) eif")
where "bif b then P else Q eif \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>H\<^sub>P\<^sub>< \<triangleright> Q)"

subsection{*assert and assume*}

definition rassume_hp :: "'\<alpha> upred \<Rightarrow> ('\<alpha>) hrel_cphp" ("_\<^sup>\<top>\<^sub>H\<^sub>P" [999] 999) where
[urel_defs]: "rassume_hp c = (bif c then SKIP\<^sub>H\<^sub>P else \<top>\<^sub>H\<^sub>P eif)"

definition rassert_hp :: "'\<alpha> upred \<Rightarrow> ('\<alpha>) hrel_cphp" ("_\<^sub>\<bottom>\<^sub>H\<^sub>P" [999] 999) where
[urel_defs]: "rassert_hp c = (bif c then SKIP\<^sub>H\<^sub>P else \<bottom>\<^sub>H\<^sub>P eif)"

subsection{*store and load*}
  
definition ustore:: 
  "('b::mem_type ptr \<Longrightarrow> 'a cphp) \<Rightarrow> ('b, 'a cphp) uexpr \<Rightarrow>  ('a) hrel_cphp" ("(*_ :=\<^sub>h\<^sub>p/ _)"[73, 73] 72)
where [urel_defs]:
  "ustore p v = (heap_raw :== (bop hrs_mem_update (bop heap_update (utp_expr.var p) v) (&heap_raw)))"

definition ustore':: "'b::mem_type ptr \<Rightarrow> ('b, 'a) uexpr \<Rightarrow>  ('a) hrel_cphp" ("(*_ :=\<^sub>H\<^sub>P/ _)"[73, 73] 72)where 
  [urel_defs]:"ustore' p v = (heap_raw :== (bop hrs_mem_update (bop heap_update \<guillemotleft>p\<guillemotright> (v\<oplus>\<^sub>p \<Sigma>\<^sub>H\<^sub>P)) (&heap_raw)))"
  
definition uload:: "'b::mem_type ptr \<Rightarrow> ('b, 'a cphp) uexpr" ( "*\<^sub>h\<^sub>p")where 
  [urel_defs]:"uload p = (bop h_val (uop hrs_mem (&heap_raw)) \<guillemotleft>p\<guillemotright>)"
  
definition uderef:: "('b \<Longrightarrow> 'a cphp)  \<Rightarrow>('b::mem_type ptr \<Longrightarrow> 'a cphp) \<Rightarrow>  ('a) hrel_cphp " ("(/_ :=\<^sub>h\<^sub>p/*_)"[73, 73] 72)
where [urel_defs]: "uderef x p  = (x :== (bop h_val (uop hrs_mem (&heap_raw)) (utp_expr.var p)))"

definition uderef':: "('b \<Longrightarrow> 'a)  \<Rightarrow>'b::mem_type ptr \<Rightarrow>  ('a) hrel_cphp " ("(/_ :=\<^sub>s\<^sub>t\<^sub>k/*_)"[73, 73] 72)
where [urel_defs]:
  "uderef' x p = (\<^bold>\<exists> v \<bullet> x \<Midarrow> \<guillemotleft>v\<guillemotright> \<and>\<^sub>p \<lceil>(\<guillemotleft>v\<guillemotright> =\<^sub>u (bop h_val (uop hrs_mem (&heap_raw)) \<guillemotleft>p\<guillemotright>))\<rceil>\<^sub><)"
term "\<Sigma>\<^sub>H\<^sub>P"
term "(v\<oplus>\<^sub>p \<Sigma>\<^sub>H\<^sub>P)"  
  
lemma [simp]: 
  "(h_val (hrs_mem (hrs_mem_update (heap_update (p::'b::mem_type ptr) v) (h,tt))) p) = v" 
  unfolding hrs_mem_def hrs_mem_update_def
  by (simp add: h_val_heap_update)

lemma "
   ( *p :=\<^sub>h\<^sub>p \<guillemotleft>v\<guillemotright> ;; x :=\<^sub>h\<^sub>p *p)  = ( *p :=\<^sub>h\<^sub>p \<guillemotleft>v\<guillemotright> ;; x:== \<guillemotleft>v\<guillemotright>)"
  unfolding lens_indep_def
  apply rel_simp

lemma " heap_raw \<sharp> v \<Longrightarrow>
   ( *p :=\<^sub>h\<^sub>p v ;; x :=\<^sub>h\<^sub>p *p)  = ( *p :=\<^sub>h\<^sub>p v ;; x:== v)"
  unfolding lens_indep_def
  apply pred_simp apply rel_simp
  by (metis (no_types)  prod.exhaust_sel)

lemma "( *p :=\<^sub>h\<^sub>p \<guillemotleft>v\<guillemotright> ;; x :=\<^sub>s\<^sub>t\<^sub>k *p)  = ( *p :=\<^sub>h\<^sub>p \<guillemotleft>v\<guillemotright> ;; x \<Midarrow> \<guillemotleft>v\<guillemotright>)"
  unfolding lens_indep_def
  by rel_simp

lemma "( *p :=\<^sub>H\<^sub>P v  ;; x :=\<^sub>s\<^sub>t\<^sub>k *p)  = ( *p :=\<^sub>H\<^sub>P v  ;; x \<Midarrow> v)"
  unfolding lens_indep_def
  by rel_simp   

lemma "( *p :=\<^sub>H\<^sub>P (y + 1)  ;; x :=\<^sub>s\<^sub>t\<^sub>k *p)  = (  x \<Midarrow> (y + 1))"
  unfolding lens_indep_def
  by rel_simp 

lemma "( *p :=\<^sub>h\<^sub>p (v\<oplus>\<^sub>p \<Sigma>\<^sub>H\<^sub>P)  ;; x :=\<^sub>s\<^sub>t\<^sub>k *p)  = ( *p :=\<^sub>h\<^sub>p (v\<oplus>\<^sub>p \<Sigma>\<^sub>H\<^sub>P)  ;; x \<Midarrow> v)"
  unfolding lens_indep_def
  by rel_simp     

subsection{*Loops*}

end

