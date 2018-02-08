(*****************************************************************************************)
(* Orca: A Functional Correctness Verifier for Imperative Programs Based on Isabelle/UTP *)
(*                                                                                       *)
(* Copyright (c) 2016-2018 Virginia Tech, USA                                            *)
(* This software may be distributed and modified according to the terms of               *)
(* the GNU Lesser General Public License version 3.0 or any later version.               *)
(* Note that NO WARRANTY is provided.                                                    *)
(* See CONTRIBUTORS, LICENSE and CITATION files for details.                             *)
(*****************************************************************************************)

theory utp_heap_scratch
imports   "../../../Isabelle-UTP/utp/utp" 
          "../../../Isabelle-UTP/theories/utp_designs"  
          "../../AlgebraicLaws/Algebraic_Laws_aux"
begin
subsection {*UTP heap alphabet*}

text {*
*}

alphabet ('hval, 'haddr) hp_vars = des_vars +
  heap_raw:: "'haddr \<rightharpoonup> 'hval"

declare hp_vars.splits [alpha_splits]

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

type_synonym  ('hval, 'haddr, '\<alpha>) cphp = "('hval, 'haddr, '\<alpha>) hp_vars_scheme des"
type_synonym ('hval, 'haddr, '\<alpha>,'\<beta>) rel_cphp  = "(('hval, 'haddr,'\<alpha>) cphp, ('hval, 'haddr,'\<beta>) cphp) rel"
type_synonym ('hval, 'haddr, '\<alpha>) hrel_cphp  = "(('hval, 'haddr, '\<alpha>) cphp) hrel"

subsubsection {*Syntactic type setup*}

translations
  (type) "('hval, 'haddr, '\<alpha>) cphp" <= (type) " ('hval, 'haddr, '\<alpha>) hp_vars_scheme des"
  (type) "('hval, 'haddr, '\<alpha>) cphp" <= (type) "('hval, 'haddr, '\<alpha>) hp_vars_ext des"
  (type) "('hval, 'haddr, '\<alpha>,'\<beta>) rel_cphp" <= 
         (type) "(('hval, 'haddr,'\<alpha>) cphp, (_, _,'\<beta>) cphp) rel"

notation hp_vars_child_lens\<^sub>a ("\<Sigma>\<^sub>h\<^sub>p")
notation hp_vars_child_lens ("\<Sigma>\<^sub>H\<^sub>P")

syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>H\<^sub>P")
  "_svid_st_a"  :: "svid" ("\<Sigma>\<^sub>h\<^sub>p")
translations
  "_svid_st_alpha" => "CONST hp_vars_child_lens"
   "_svid_st_a" => "CONST hp_vars_child_lens\<^sub>a"

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
text {**}
subsection{*Loops*}
subsection{*Experiments*}
term "map_lens k"

term "&heap_raw"
term "fun_upd f 0 (Some 1)"
term "(trop fun_upd (&heap_raw) \<guillemotleft>add::nat\<guillemotright> (uop Some \<guillemotleft>v::int\<guillemotright>))"
term "\<lbrakk>trop fun_upd (&heap_raw) \<guillemotleft>add\<guillemotright> (uop Some \<guillemotleft>v\<guillemotright>)\<rbrakk>\<^sub>e s add = Some v"
  
lemma "(trop fun_upd (&heap_raw) \<guillemotleft>add::nat\<guillemotright> (uop Some \<guillemotleft>v::int\<guillemotright>)) = mem \<Longrightarrow>
      \<exists>s. \<lbrakk>mem\<rbrakk>\<^sub>e s add =  Some v"  
  apply rel_simp
  apply (auto  split: if_splits)
  done 
term "store ptr v = (trop fun_upd (&heap_raw) ptr (uop Some v))" 
 term "(trop fun_upd (&heap_raw) ptr (uop Some v))" 

term "restricted_load ptr = utp_expr.var (map_lens ptr ;\<^sub>L heap_raw)"
term "uop (\<lambda>ptr. get\<^bsub>map_lens ptr ;\<^sub>L heap_raw\<^esub>)"

term "load ptru = (\<lambda>ptr \<bullet> utp_expr.var (map_lens ptr ;\<^sub>L heap_raw))(ptru)\<^sub>a"
term "\<lambda>ptru. (\<lambda>ptr \<bullet> utp_expr.var (map_lens ptr ;\<^sub>L heap_raw))(ptru)\<^sub>a"  
  
datatype block =  available| freed   
term "(utp_expr.var (map_lens ptr ;\<^sub>L heap_raw))"  
term "get\<^bsub>(heap_raw)\<^esub> s"  
term "&heap_raw"
term "ulambda"
lift_definition ulambda_rev :: "('a \<Rightarrow> 'b, '\<alpha>) uexpr \<Rightarrow> ('a \<Rightarrow> ('b, '\<alpha>) uexpr)"
is "\<lambda> f x A. f A x" .
term "ulambda_rev (utp_expr.var (map_lens ptr ;\<^sub>L heap_raw))"  


term "uop (ulambda_rev (&heap_raw)) p " 
term "((&heap_raw) s)"
term "(&heap_raw)"
term "utp_expr.var ( map_lens ptr ;\<^sub>L heap_raw)"
term "(map_lens ptr ;\<^sub>L heap_raw)"  
find_consts  "('a \<Rightarrow> 'b, 'c) uexpr \<Rightarrow> ('a \<Rightarrow> ('b, 'c) uexpr) "
term "\<lambda>x\<bullet> \<guillemotleft>(x::int)\<guillemotright>"  
datatype ('n,'a) Ptr = pt:ptr | nm: Numeral (selctn:'n) 
find_theorems name:".Ptr."
term "ptr"  
term "pt"  
term "\<lparr> lens_get = (\<lambda>s. None), 
        lens_put = (\<lambda>s v. ptr) \<rparr>"

term " (case s of Numeral n \<Rightarrow> Some (Numeral v) | _ \<Rightarrow> None)"
term "Numeral "  
term "\<lparr> lens_get = (\<lambda>s. (case s of Numeral n \<Rightarrow> Some n | _ \<Rightarrow> None)), 
        lens_put = (\<lambda>s v. Numeral (the v)) \<rparr>"  
term "\<lparr>lens_get = the, lens_put = \<lambda>s. Some\<rparr>"  

 term "path P ;\<^sub>L the\<^sub>L ;\<^sub>L indx B"
 term "path P ;\<^sub>L 
       \<lparr>lens_get = the, lens_put = \<lambda>_. Some\<rparr> ;\<^sub>L 
       indx B"
  
term "\<lambda>(N) v . undefined"  
term "Pair s s"
term "\<lambda>(s, s') v . undefined"  
end

