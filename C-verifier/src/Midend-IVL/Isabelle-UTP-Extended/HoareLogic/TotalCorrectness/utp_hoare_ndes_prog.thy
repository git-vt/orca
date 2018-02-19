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

theory utp_hoare_ndes_prog
  imports "../../AlgebraicLaws/algebraic_laws_prog"
  keywords "lemmata" :: thy_goal
  and "assumes_utp" "ensures_utp" "prog_utp" :: quasi_command
begin

ML\<open>
structure Element' = struct

datatype ('typ, 'term, 'fact) ctxt_stmt =
  Shows of (Attrib.binding * ('term * 'term list) list) list |
  Obtains of ('typ, 'term) Element.obtain list |
  Fixes of (binding * 'typ option * mixfix) list |
  Constrains of (string * 'typ) list |
  Assumes of (Attrib.binding * ('term * 'term list) list) list |
  Defines of (Attrib.binding * ('term * 'term list)) list |
  Notes of string * (Attrib.binding * ('fact * Token.src list) list) list |
  Assumes_UTP of 'term |
  Ensures_UTP of 'term |
  Prog_UTP of 'term
type context = (string, string, Facts.ref) ctxt_stmt

fun to_elem_stmt l = 
  case
    ( map_filter (fn Shows l => SOME l | _ => NONE) l
    , map_filter (fn Obtains l => SOME l | _ => NONE) l)
  of (l_shows, []) =>
      Element.Shows
        let val l_shows = List.concat l_shows
            val escape = map (fn s => "(" ^ YXML.content_of s ^ ")") in
          case
            ( map_filter (fn Assumes_UTP t => SOME t | _ => NONE) l
            , map_filter (fn Ensures_UTP t => SOME t | _ => NONE) l
            , map_filter (fn Prog_UTP t => SOME t | _ => NONE) l)
          of (l_ass, l_ens, [t_prog]) =>
               (Binding.empty_atts,
                [(String.concatWith
                    " "
                    ("hoare_prog_t"
                     :: (case l_ass of [] => "utrue" | _ => String.concatWith "\<and>" (escape l_ass))
                     :: escape [t_prog]
                      @ [case l_ens of [] => "ufalse" | _ => String.concatWith "\<and>" (escape l_ens)]), [])])
               :: l_shows
           | _ => ((case l_shows of [] => warning "not yet supported" | _ => ()); l_shows)
        end
   | ([], l) => Element.Obtains (List.concat l)
   | _ => error "shows and obtains are both present"

val to_elem_context_list = 
  map_filter (fn Fixes l => SOME (Element.Fixes l)
               | Constrains l => SOME (Element.Constrains l)
               | Assumes l => SOME (Element.Assumes l)
               | Defines l => SOME (Element.Defines l)
               | Notes l => SOME (Element.Notes l)
               | _ => NONE)

val exists_assumes = List.exists (fn Assumes _ => true | _ => false)
end

structure Parse_Spec' = struct

local

val loc_element =
  Parse.$$$ "fixes" |-- Parse.!!! Parse_Spec.locale_fixes >> Element'.Fixes ||
  Parse.$$$ "constrains" |--
    Parse.!!! (Parse.and_list1 (Parse.name -- (Parse.$$$ "::" |-- Parse.typ)))
    >> Element'.Constrains ||
  Parse.$$$ "assumes" |-- Parse.!!! (Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Scan.repeat1 Parse.propp))
    >> Element'.Assumes ||
  Parse.$$$ "defines" |-- Parse.!!! (Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Parse.propp))
    >> Element'.Defines ||
  Parse.$$$ "notes" |-- Parse.!!! (Parse.and_list1 (Parse_Spec.opt_thm_name "=" -- Parse.thms1))
    >> (curry Element'.Notes "") ||
  Parse.$$$ "obtains" |-- Parse.!!! Parse_Spec.obtains >> Element'.Obtains ||
  Parse.$$$ "shows" |-- Parse.!!! Parse_Spec.statement >> Element'.Shows ||
  Parse.$$$ "assumes_utp" |-- Parse.!!! Parse.term >> Element'.Assumes_UTP ||
  Parse.$$$ "ensures_utp" |-- Parse.!!! Parse.term >> Element'.Ensures_UTP ||
  Parse.$$$ "prog_utp" |-- Parse.!!! Parse.term >> Element'.Prog_UTP;

in

val context_element = Parse.group (fn () => "context element") loc_element;

end;

val long_statement = Scan.repeat context_element;
end

local

val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec'.long_statement
    >> (fn ((binding, includes), elems) => (true, binding, includes, elems));

val _ = Outer_Syntax.commands @{command_keyword lemmata} ""
 (long_statement >> 
  (fn (long, binding, includes, elems) =>
  List.concat
    [ [(@{command_keyword lemma},
        Toplevel.local_theory_to_proof' NONE NONE
          (Specification.theorem_cmd long Thm.theoremK NONE (K I) binding includes (Element'.to_elem_context_list elems) (Element'.to_elem_stmt elems)))]
    , if Element'.exists_assumes elems then
        [(@{command_keyword apply},
          let val m = ( Method.Combinator (Method.no_combinator_info, Method.Then,
                                             [Method.Basic (fn ctxt => Method.insert (Proof_Context.get_thms ctxt "assms"))])
                      , (Position.none, Position.none)) in
          (Method.report m; Toplevel.proofs (Proof.apply m))
          end)]
      else []
    , [(@{command_keyword apply},
        let val m = ( Method.Combinator (Method.no_combinator_info, Method.Then,
                                           [Method.Source [Token.make_string ("vcg_hoare_sp_steps_pp_beautify", Position.none)]])
                    , (Position.none, Position.none)) in
        (Method.report m; Toplevel.proofs (Proof.apply m))
       end) ]]))
in end\<close>

section {*Helper*}    

text \<open>The below definition helps in asserting independence for a group of lenses, as otherwise the
number of assumptions required increases greatly. Unfortunately, it is not usable with lenses of
different types as Isabelle does not allow heterogenous lists; element types must be unifiable.\<close>

definition \<open>lens_indep_all lenses \<longleftrightarrow> (\<forall>l \<in> set lenses. vwb_lens l \<and> eff_lens l) \<and>
                                      (\<forall>i j. i < length lenses \<and> j < length lenses \<and>
                                             i \<noteq> j \<longrightarrow> lenses!i \<bowtie> lenses!j)\<close>

lemma lens_indep_all_alt:
  \<open>lens_indep_all lenses \<longleftrightarrow> (\<forall>l \<in> set lenses. vwb_lens l \<and> eff_lens l) \<and>
                              distinct lenses \<and>
                             (\<forall>a \<in> set lenses. \<forall>b \<in> set lenses. a \<noteq> b \<longrightarrow> a \<bowtie> b)\<close>
  unfolding lens_indep_all_def distinct_conv_nth
  apply (safe; simp?)
   apply (metis lens_indep_quasi_irrefl nth_mem vwb_lens_wb)
  apply (metis in_set_conv_nth)
  done

section {*Hoare logic for programs*}  

named_theorems hoare_sp_rules and hoare_wp_rules and hoare_wp_proof_annotation_rules

subsection {*Hoare triple definition*}

lift_definition hoare_prog_t :: "'\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>P") 
 is  hoare_d .

declare hoare_prog_t.rep_eq [prog_rep_eq]

lemma hoare_true_assisgns_prog_t[hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  "\<lbrace>p\<rbrace> \<langle>\<sigma>\<rangle>\<^sub>p \<lbrace>true\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma hoare_true_skip_prog_t[hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  "\<lbrace>p\<rbrace>SKIP\<lbrace>true\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma hoare_false_prog_t[hoare_sp_rules]: 
  "\<lbrace>false\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

subsection {*Precondition weakening*}

lemma pre_str_prog_hoare:
  assumes "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" and "\<lbrace>p\<^sub>2\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<^sub>1\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P" 
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Post-condition strengthening*}
  
lemma post_weak_prog_hoare:
  assumes "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>2\<rbrace>\<^sub>P" and "`q\<^sub>2 \<Rightarrow> q\<^sub>1`"
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>1\<rbrace>\<^sub>P" 
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Consequence rule*}  
  
lemma consequence_hoare_prog:
  assumes I0': "`p \<Rightarrow> p'`" 
  assumes induct_step:"\<lbrace>p'\<rbrace> C \<lbrace>q'\<rbrace>\<^sub>P" 
  assumes I0 :"`q' \<Rightarrow> q`"  
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P"
proof(rule post_weak_prog_hoare[OF _ I0], goal_cases)
  case 1
  then show ?case by (rule pre_str_prog_hoare[OF I0' induct_step ]) 
qed   
  
subsection {*Hoare and assertion logic*}

lemma hoare_prog_conj_prog_t: 
  assumes"\<lbrace>p\<rbrace>C\<lbrace>r\<rbrace>\<^sub>P" and "\<lbrace>p\<rbrace>C\<lbrace>s\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>C\<lbrace>r \<and> s\<rbrace>\<^sub>P"
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Hoare SKIP*}

lemma skip_prog_hoare_prog_t[hoare_sp_rules, hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  "\<lbrace>p\<rbrace>SKIP\<lbrace>p\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)
    
lemma skip_prog_hoare_prog_intro: 
  "`p \<Rightarrow> q`\<Longrightarrow>\<lbrace>p\<rbrace>SKIP\<lbrace>q\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)
    
subsection {*Hoare for assignment*}

lemma assigns_prog_hoare_prog_backward_t[hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  assumes"`p \<Rightarrow> \<sigma> \<dagger> q`" 
  shows  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>p\<lbrace>q\<rbrace>\<^sub>P"
  using assms  
  by (simp add: prog_rep_eq hoare_des)

lemma assigns_prog_hoare_prog_backward_t': 
  "\<lbrace>\<sigma> \<dagger> p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>p\<lbrace>p\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma assigns_prog_floyd_t[hoare_sp_rules]:
  assumes "vwb_lens x"
  shows \<open>\<lbrace>p\<rbrace>x :== e\<lbrace>\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrace>\<^sub>P\<close>
  using assms  
  by (simp add: assms prog_rep_eq hoare_des)

subsection {*Hoare for Sequential Composition*}

lemma seq_hoare_prog[hoare_sp_rules, hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  assumes"\<lbrace>p\<rbrace>C\<^sub>1\<lbrace>s\<rbrace>\<^sub>P" and "\<lbrace>s\<rbrace>C\<^sub>2\<lbrace>r\<rbrace>\<^sub>P" 
  shows"\<lbrace>p\<rbrace>C\<^sub>1 ; C\<^sub>2\<lbrace>r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)  

subsection {*Hoare for Conditional*}

lemma cond_prog_hoare_prog_t[hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  assumes "\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>P" and "\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>IF b THEN C\<^sub>1 ELSE C\<^sub>2 FI\<lbrace>q\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des) 

    
lemma cond_prog_hoare_prog_t'[hoare_sp_rules]:
  assumes \<open>\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>P\<close> and \<open>\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>s\<rbrace>\<^sub>P\<close>
  shows \<open>\<lbrace>p\<rbrace>IF b THEN C\<^sub>1 ELSE C\<^sub>2 FI\<lbrace>q \<or> s\<rbrace>\<^sub>P\<close>
  using assms
  by (simp add: prog_rep_eq hoare_des) 
    
subsection {*Hoare for recursion*}

lemma mono_Monotone_prog: (*This can be used to generate lemmas automatically*)
  assumes M:"mono F" 
  shows "Mono\<^bsub>uthy_order NDES\<^esub> (Rep_prog \<circ> F \<circ> Abs_prog \<circ> \<H>\<^bsub>NDES\<^esub>)"
  by (metis (no_types, lifting) Abs_prog_Rep_prog_Ncarrier Healthy_def M Mono_utp_orderI comp_apply less_eq_prog.rep_eq monoD)

lemma N_prog_funcset: (*This can be used to generate lemmas automatically*)
  "Rep_prog \<circ> F \<circ> Abs_prog \<circ> \<H>\<^bsub>NDES\<^esub> \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"  
  using Rep_prog by auto
   
lemma mu_prog_hoare_prog:
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<And> st P. \<lbrace>p \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace> P \<lbrace>q\<rbrace>\<^sub>P \<Longrightarrow> \<lbrace>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> F P \<lbrace>q\<rbrace>\<^sub>P"   
  shows "\<lbrace>p\<rbrace>\<mu>\<^sub>p F \<lbrace>q\<rbrace>\<^sub>P"
  apply (simp add: prog_rep_eq)
  apply (subst normal_design_theory_continuous.LFP_healthy_comp)  
  apply (rule mu_ndes_hoare_ndes[OF N_prog_funcset WF  mono_Monotone_prog[OF M] , 
                                    simplified, OF induct_step[unfolded prog_rep_eq]])
  apply (simp add: Abs_prog_Rep_prog_Ncarrier)   
  apply (simp add: Healthy_if is_Ncarrier_is_ndesigns)
  done
    
lemma mu_prog_hoare_prog':
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<And> st P. \<lbrace>p \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace> P \<lbrace>q\<rbrace>\<^sub>P \<Longrightarrow> \<lbrace>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> F P \<lbrace>q\<rbrace>\<^sub>P" 
  assumes I0: "`p' \<Rightarrow> p`"  
  shows "\<lbrace>p'\<rbrace>\<mu>\<^sub>p F \<lbrace>q\<rbrace>\<^sub>P"
  by (simp add: pre_str_prog_hoare[OF I0 mu_prog_hoare_prog[OF WF M induct_step]])

subsection {*Hoare for frames*}
  
lemma antiframe_hoare_p_t:
  assumes "vwb_lens a"
  assumes "a \<sharp> r" 
  assumes "a \<natural> q"    
  assumes "\<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>P"  
  shows "\<lbrace>p \<and> r\<rbrace>a:[P]\<lbrace>q \<and> r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)

lemma antiframe_goare_p_t_stronger:
  assumes "vwb_lens a"
  assumes "a \<sharp> r" 
  assumes "a \<natural> q"    
  assumes "\<lbrace>p \<and> r\<rbrace>P\<lbrace>q\<rbrace>\<^sub>P"  
  shows "\<lbrace>p \<and> r\<rbrace>a:[P]\<lbrace>q \<and> r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)    
    
lemma frame_hoare_p_t:
  assumes "vwb_lens a"
  assumes "a \<natural> r" 
  assumes "a \<sharp> q"    
  assumes "\<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>P"  
  shows "\<lbrace>p \<and> r\<rbrace> a:\<lbrakk>P\<rbrakk> \<lbrace>q \<and> r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)

lemma frame_hoare_p_t_stronger:
  assumes "vwb_lens a"
  assumes "a \<natural> r" 
  assumes "a \<sharp> q"    
  assumes "\<lbrace>p \<and> r\<rbrace>P\<lbrace>q\<rbrace>\<^sub>P"  
  shows "\<lbrace>p \<and> r\<rbrace> a:\<lbrakk>P\<rbrakk> \<lbrace>q \<and> r\<rbrace>\<^sub>P"
  using assms 
  by (simp add: prog_rep_eq hoare_des)
    
lemma blah1: 
  assumes "vwb_lens g'" "vwb_lens l"
  assumes  "l \<bowtie> g'" 
  shows "vwb_lens  (g' +\<^sub>L l)" 
  using assms 
  by (simp add: lens_indep_sym plus_vwb_lens) 
   
lemma
  assumes 1:"vwb_lens g" 
  assumes 2:"vwb_lens g'" 
  assumes 3:"vwb_lens l"
  assumes 4:"l \<bowtie> g" 
  assumes 8:"g' \<subseteq>\<^sub>L g"
  assumes 5:"{&g', &l}:[C] = C" 
  assumes 6:"\<lbrace>p\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P"
  assumes 7:"`r \<Rightarrow> p`"     
  shows "\<lbrace>r\<rbrace> l:\<lbrakk>C\<rbrakk> \<lbrace>(\<exists> l \<bullet> q) \<and> (\<exists>g' \<bullet> r)\<rbrace>\<^sub>P"
  using 1 2 3 4 5 6 7 unfolding lens_indep_def
  apply (simp add: prog_rep_eq )
   apply rel_auto 
  apply (metis (no_types, lifting) vwb_lens_wb wb_lens.get_put)
  apply (rule_tac x="get\<^bsub> g'\<^esub> more" in exI) using 8 4 
proof -
  fix ok\<^sub>v :: bool and more :: 'b and ok\<^sub>v' :: bool and x :: 'b
  assume a1: "\<lbrakk>r\<rbrakk>\<^sub>e more"
  assume a2: "vwb_lens g"
  assume "\<forall>\<sigma> u. get\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> \<sigma> u) = get\<^bsub>g\<^esub> \<sigma>"
  assume a3: "\<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = more\<rparr>, \<lparr>ok\<^sub>v = True, \<dots> = x\<rparr>)"
  assume a4: "\<forall>ok\<^sub>v more ok\<^sub>v' morea. (ok\<^sub>v \<longrightarrow> ok\<^sub>v' \<and> (\<exists>x. \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = more\<rparr>, \<lparr>ok\<^sub>v = ok\<^sub>v', \<dots> = x\<rparr>) \<and> morea = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> more (get\<^bsub>l\<^esub> x)) (get\<^bsub>g'\<^esub> x))) = \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = ok\<^sub>v, \<dots> = more\<rparr>, \<lparr>ok\<^sub>v = ok\<^sub>v', \<dots> = morea\<rparr>)"
  assume a5: "\<forall>\<sigma> v u. put\<^bsub>l\<^esub> (put\<^bsub>g\<^esub> \<sigma> v) u = put\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> \<sigma> u) v"
  assume a6: "vwb_lens g'"
  assume a7: "vwb_lens l"
  have f8: "wb_lens g"
    using a2 vwb_lens_wb by blast
  have f9: "\<forall>l la b a c. \<not> vwb_lens l \<or> \<not> la \<subseteq>\<^sub>L l \<or> put\<^bsub>l\<^esub> (b::'b) (put\<^bsub>la /\<^sub>L l\<^esub> (a::'a) (c::'c)) = put\<^bsub>la\<^esub> (put\<^bsub>l\<^esub> b a) c"
    by (meson lens_put_of_quotient)
  then have f10: "put\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> x (get\<^bsub>l\<^esub> more)) (put\<^bsub>g' /\<^sub>L g\<^esub> (get\<^bsub>g\<^esub> x) (get\<^bsub>g'\<^esub> more)) = put\<^bsub>g'\<^esub> (put\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> x (get\<^bsub>l\<^esub> more)) (get\<^bsub>g\<^esub> x)) (get\<^bsub>g'\<^esub> more)"
    using a2 by (metis "8") (* > 1.0 s, timed out *)
  have f11: "\<forall>b ba bb bc. (\<not> b \<or> bb \<and> (\<exists>b. \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = ba\<rparr>, \<lparr>ok\<^sub>v = bb, \<dots> = b\<rparr>) \<and> bc = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> ba (get\<^bsub>l\<^esub> b)) (get\<^bsub>g'\<^esub> b))) = \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = b, \<dots> = ba\<rparr>, \<lparr>ok\<^sub>v = bb, \<dots> = bc\<rparr>)"
    using a4 by auto
  obtain bb :: "'b \<Rightarrow> bool \<Rightarrow> 'b \<Rightarrow> 'b" where
    "\<forall>x0 x1 x2. (\<exists>v4. \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = x2\<rparr>, \<lparr>ok\<^sub>v = x1, \<dots> = v4\<rparr>) \<and> x0 = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x2 (get\<^bsub>l\<^esub> v4)) (get\<^bsub>g'\<^esub> v4)) = (\<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = x2\<rparr>, \<lparr>ok\<^sub>v = x1, \<dots> = bb x0 x1 x2\<rparr>) \<and> x0 = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x2 (get\<^bsub>l\<^esub> (bb x0 x1 x2))) (get\<^bsub>g'\<^esub> (bb x0 x1 x2)))"
    by moura
  then have "\<forall>b ba bc bd. (b \<and> (\<not> bc \<or> (\<forall>b. \<not> \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = ba\<rparr>, \<lparr>ok\<^sub>v = bc, \<dots> = b\<rparr>) \<or> \<not> bd = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> ba (get\<^bsub>l\<^esub> b)) (get\<^bsub>g'\<^esub> b))) \<or> \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = b, \<dots> = ba\<rparr>, \<lparr>ok\<^sub>v = bc, \<dots> = bd\<rparr>)) \<and> ((\<not> b \<or> bc \<and> \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = ba\<rparr>, \<lparr>ok\<^sub>v = bc, \<dots> = bb bd bc ba\<rparr>) \<and> bd = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> ba (get\<^bsub>l\<^esub> (bb bd bc ba))) (get\<^bsub>g'\<^esub> (bb bd bc ba))) \<or> \<not> \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = b, \<dots> = ba\<rparr>, \<lparr>ok\<^sub>v = bc, \<dots> = bd\<rparr>))"
    using f11 by metis (* > 1.0 s, timed out *)
  then have f12: "\<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = more\<rparr>, \<lparr>ok\<^sub>v = True, \<dots> = bb x True more\<rparr>) \<and> x = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> more (get\<^bsub>l\<^esub> (bb x True more))) (get\<^bsub>g'\<^esub> (bb x True more))"
    using a3 by (metis (no_types))
  have f13: "put\<^bsub>g\<^esub> (put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> more (get\<^bsub>l\<^esub> (bb x True more))) (get\<^bsub>g'\<^esub> (bb x True more))) (put\<^bsub>g' /\<^sub>L g\<^esub> (get\<^bsub>g\<^esub> x) (get\<^bsub>g'\<^esub> more)) = put\<^bsub>g'\<^esub> (put\<^bsub>g\<^esub> (put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> more (get\<^bsub>l\<^esub> (bb x True more))) (get\<^bsub>g'\<^esub> (bb x True more))) (get\<^bsub>g\<^esub> x)) (get\<^bsub>g'\<^esub> more)"
    using a2 f9 by (metis "8") (* > 1.0 s, timed out *)
  have f14: "put\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> more (get\<^bsub>l\<^esub> (bb x True more))) (put\<^bsub>g' /\<^sub>L g\<^esub> (get\<^bsub>g\<^esub> more) (get\<^bsub>g'\<^esub> more)) = put\<^bsub>g'\<^esub> (put\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> more (get\<^bsub>l\<^esub> (bb x True more))) (get\<^bsub>g\<^esub> more)) (get\<^bsub>g'\<^esub> more)"
    using a2 f9 by (metis "8") (* > 1.0 s, timed out *)
  have "put\<^bsub>g\<^esub> more (put\<^bsub>g' /\<^sub>L g\<^esub> (get\<^bsub>g\<^esub> more) (get\<^bsub>g'\<^esub> more)) = put\<^bsub>g'\<^esub> (put\<^bsub>g\<^esub> more (get\<^bsub>g\<^esub> more)) (get\<^bsub>g'\<^esub> more)"
    using a2 f9 by (metis "8") (* > 1.0 s, timed out *)
  then show "\<lbrakk>r\<rbrakk>\<^sub>e (put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x (get\<^bsub>l\<^esub> more)) (get\<^bsub>g'\<^esub> more))"
    using f14 f13 f12 f10 f8 a7 a6 a5 a1 by (metis mwb_lens.put_put vwb_lens_mwb vwb_lens_wb wb_lens.get_put)
qed 
  

subsection {*Hoare for while loop*}   

lemma while_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`" 
  assumes induct_step:"\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"    
  shows "\<lbrace>p\<rbrace>WHILE b DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding while_lfp_prog_mu_prog
proof (rule pre_str_prog_hoare[OF seq_step mu_prog_hoare_prog[OF WF if_prog_mono cond_prog_hoare_prog_t, of _ e] ], goal_cases)
  case (1 st X)
  assume *:"\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>X\<lbrace>\<not> b \<and> invar\<rbrace>\<^sub>P"  
  show ?case
  proof (rule seq_hoare_prog[of _ _ "invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>"], goal_cases)
    case 1
    then show ?case using induct_step[of st] by assumption 
  next
    case 2
    then show ?case using * by assumption
  qed
next
  case (2 st X)
  assume "\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>X\<lbrace>\<not> b \<and> invar\<rbrace>\<^sub>P"  
  show ?case by (rule skip_prog_hoare_prog_intro, pred_blast) 
qed 
    
lemma while_invr_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`" 
  assumes induct_step:"\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"    
  shows "\<lbrace>p\<rbrace>INVAR invar WHILE b DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding while_lfp_invr_prog_def
  using assms while_hoare_prog_minimal
  by blast  

lemma while_invr_vrt_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`" 
  assumes induct_step:"\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"    
  shows "\<lbrace>p\<rbrace>INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding while_lfp_invr_vrt_prog_def
  using assms while_hoare_prog_minimal
  by blast  
    
lemma while_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P" 
  by (rule consequence_hoare_prog[OF seq_step _ PHI, 
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF I0' induct_step I0]])

lemma while_invr_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>INVAR invar WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P" 
  unfolding while_lfp_invr_prog_def
  by (rule consequence_hoare_prog[OF seq_step _ PHI, 
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF I0' induct_step I0]])

lemma while_invr_vrt_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P" 
  unfolding while_lfp_invr_vrt_prog_def  
  by (rule consequence_hoare_prog[OF seq_step _ PHI, 
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF I0' induct_step I0]])
                              
lemma while_hoare_prog_wp:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P" 
  by (rule consequence_hoare_prog[OF seq_step _ PHI,
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF I0' induct_step uimp_refl]])

lemma while_invr_hoare_prog_wp:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>INVAR invar WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P"                              
  unfolding while_lfp_invr_prog_def
  by (rule consequence_hoare_prog[OF seq_step _ PHI,
                                 OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                 OF consequence_hoare_prog[OF I0' induct_step uimp_refl]])

lemma while_invr_vrt_hoare_prog_wp[hoare_wp_rules]:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P"                              
  unfolding while_lfp_invr_vrt_prog_def
  by (rule consequence_hoare_prog[OF seq_step _ PHI,
                                 OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                 OF consequence_hoare_prog[OF I0' induct_step uimp_refl]])
                                
lemma while_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>WHILE b DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P" 
  by (rule consequence_hoare_prog[OF seq_step _ uimp_refl, 
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF uimp_refl induct_step I0]])                              
                              
lemma while_invr_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>INVAR invar WHILE b DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P" 
  unfolding while_lfp_invr_prog_def  
  by (rule consequence_hoare_prog[OF seq_step _ uimp_refl, 
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF uimp_refl induct_step I0]])

lemma while_invr_vrt_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P" 
  unfolding while_lfp_invr_vrt_prog_def  
  by (rule consequence_hoare_prog[OF seq_step _ uimp_refl, 
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF uimp_refl induct_step I0]])
  
subsection {*Hoare for from_until_loop*}     

lemma from_until_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>FROM init UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P"
  unfolding from_until_lfp_prog_def_alt while_lfp_prog_mu_prog
  by (rule seq_hoare_prog[OF seq_step, 
                          OF mu_prog_hoare_prog[OF WF if_prog_mono cond_prog_hoare_prog_t, of _ e],
                          OF seq_hoare_prog[OF induct_step], OF _ skip_prog_hoare_prog_intro],                             
      pauto)

lemma from_until_invr_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P"
  unfolding from_until_lfp_invr_prog_def 
  using     from_until_hoare_prog_minimal [OF WF seq_step induct_step] .
    
lemma from_until_invr_vrt_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar VRT \<guillemotleft>R\<guillemotright> UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P"
  unfolding from_until_lfp_invr_vrt_prog_def 
  using     from_until_hoare_prog_minimal [OF WF seq_step induct_step] .

lemma from_until_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init UNTIL exit DO body OD\<lbrace>q\<rbrace>\<^sub>P" 
  unfolding from_until_lfp_prog_def_alt
  by (simp add: uintro PHI seq_hoare_prog[OF seq_step] 
                       while_hoare_prog_consequence[OF WF uimp_refl _ I0' induct_step I0])

lemma from_until_invr_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar UNTIL exit DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding from_until_lfp_invr_prog_def 
  using     from_until_hoare_prog_consequence [OF WF seq_step PHI I0' induct_step I0].
    
lemma from_until_invr_vrt_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar VRT \<guillemotleft>R\<guillemotright> UNTIL exit DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding from_until_lfp_invr_vrt_prog_def
  using     from_until_hoare_prog_consequence [OF WF seq_step PHI I0' induct_step I0].
 
lemma from_until_hoare_prog_wp:
  assumes WF: "wf R"
  assumes I0: "`p \<Rightarrow> p''`"  
  assumes seq_step: "\<lbrace>p''\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>FROM init UNTIL exit DO body OD\<lbrace>q\<rbrace>\<^sub>P" 
  unfolding from_until_lfp_prog_def_alt
  by (simp add: uintro PHI seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0]
                       while_hoare_prog_consequence[OF WF uimp_refl _ I0' induct_step uimp_refl])

lemma from_until_invr_hoare_prog_wp:
  assumes WF: "wf R"
  assumes I0: "`p \<Rightarrow> p''`"   
  assumes seq_step: "\<lbrace>p''\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar UNTIL exit DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding from_until_lfp_invr_prog_def
  using from_until_hoare_prog_wp [OF WF I0 seq_step PHI I0' induct_step] .
    
lemma from_until_invr_vrt_hoare_prog_wp[hoare_wp_rules]:
  assumes WF: "wf R"
  assumes I0: "`p \<Rightarrow> p''`"    
  assumes seq_step: "\<lbrace>p''\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar VRT \<guillemotleft>R\<guillemotright> UNTIL exit DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding from_until_lfp_invr_vrt_prog_def
  using from_until_hoare_prog_wp [OF WF I0 seq_step PHI I0' induct_step] .
    
lemma from_until_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0': "`q'' \<Rightarrow> invar`"    
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P" 
  unfolding from_until_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0']
                       while_hoare_prog_consequence[OF WF uimp_refl _ uimp_refl induct_step I0])

lemma from_until_invr_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P" 
  unfolding from_until_lfp_invr_prog_def
  using from_until_hoare_prog_sp[OF WF seq_step I0' induct_step I0] .  

lemma from_until_invr_vrt_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>P"
   assumes I0': "`q'' \<Rightarrow> invar`"    
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar VRT \<guillemotleft>R\<guillemotright> UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P" 
  unfolding from_until_lfp_invr_vrt_prog_def
  using from_until_hoare_prog_sp[OF WF seq_step I0' induct_step I0] .

subsection {*Hoare for do_while_loop*}     

lemma do_while_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and>  e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows" \<lbrace>p\<rbrace>DO body WHILE b OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"  
  unfolding do_while_lfp_prog_def_alt
  by (rule seq_hoare_prog[OF seq_step while_hoare_prog_minimal[OF WF uimp_refl induct_step]])  

lemma do_while_invr_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and>  e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows" \<lbrace>p\<rbrace>DO body INVAR invar WHILE b OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"  
  unfolding do_while_lfp_invr_prog_def
  by (rule do_while_hoare_prog_minimal[OF WF seq_step induct_step])  

lemma do_while_invr_vrt_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and>  e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows" \<lbrace>p\<rbrace>DO body INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"  
  unfolding do_while_lfp_invr_vrt_prog_def
  by (rule do_while_hoare_prog_minimal[OF WF seq_step induct_step])  
    
lemma do_while_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body WHILE b OD\<lbrace>q\<rbrace>\<^sub>P" 
  unfolding do_while_lfp_prog_def_alt
  by (rule seq_hoare_prog[OF seq_step 
                             while_hoare_prog_consequence[OF WF uimp_refl PHI I0' induct_step I0]])
    
lemma do_while_invr_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body INVAR invar WHILE b OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_prog_def
  by (rule do_while_hoare_prog_consequence[OF WF seq_step PHI I0' induct_step I0])  

lemma do_while_invr_vrt_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_vrt_prog_def
  by (rule do_while_hoare_prog_consequence[OF WF seq_step PHI I0' induct_step I0])  
    
lemma do_while_hoare_prog_wp:
  assumes WF: "wf R"
  assumes I0: "`p \<Rightarrow> p''`"  
  assumes seq_step: "\<lbrace>p''\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>DO body WHILE b OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding do_while_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0]
                   while_hoare_prog_wp[OF WF uimp_refl PHI I0' induct_step])

lemma do_while_invr_hoare_prog_wp:
  assumes WF: "wf R"
   assumes I0: "`p \<Rightarrow> p''`"  
  assumes seq_step: "\<lbrace>p''\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>DO body INVAR invar WHILE b OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_prog_def do_while_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0]
                   while_hoare_prog_wp[OF WF uimp_refl PHI I0' induct_step])

lemma do_while_invr_vrt_hoare_prog_wp[hoare_wp_rules]:
  assumes WF: "wf R"
  assumes I0: "`p \<Rightarrow> p''`"   
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>DO body INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_vrt_prog_def do_while_lfp_invr_prog_def do_while_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0]
                   while_hoare_prog_wp[OF WF uimp_refl PHI I0' induct_step])

lemma do_while_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body WHILE b OD\<lbrace>\<not>b  \<and> invar\<rbrace>\<^sub>P"
  unfolding  do_while_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0']
                   while_hoare_prog_sp[OF WF uimp_refl induct_step I0])
lemma do_while_invr_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body INVAR invar WHILE b OD\<lbrace>\<not>b  \<and> invar\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_prog_def do_while_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0']
                   while_hoare_prog_sp[OF WF uimp_refl induct_step I0])
                 
lemma do_while_invr_vrt_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b OD\<lbrace>\<not>b  \<and> invar\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_vrt_prog_def do_while_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0']
                   while_hoare_prog_sp[OF WF uimp_refl induct_step I0])
                 
subsection {*Hoare for for_loop*}     
    
lemma for_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body ; incr\<lbrace>invar \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>FOR (init, b, incr) DO body OD \<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding for_lfp_prog_def
  by (simp add: from_until_hoare_prog_minimal [OF WF seq_step, of _ e] induct_step)  

lemma for_invr_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body ; incr\<lbrace>invar \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>FOR (init, b, incr) INVAR invar DO body OD \<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_prog_def for_lfp_prog_def
  by (simp add: from_until_hoare_prog_minimal [OF WF seq_step, of _ e] induct_step)  

lemma for_invr_vrt_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body ; incr\<lbrace>invar \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>FOR (init, b, incr) INVAR invar VRT \<guillemotleft>R\<guillemotright> DO body OD \<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_vrt_prog_def for_lfp_prog_def
  by (simp add: from_until_hoare_prog_minimal [OF WF seq_step, of _ e] induct_step)      

lemma for_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step:  "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"
  shows "\<lbrace>p\<rbrace>FOR (init, b, incr) DO body OD\<lbrace>q\<rbrace>\<^sub>P"  
  unfolding for_lfp_prog_def
  by(simp add: from_until_hoare_prog_consequence [OF WF seq_step PHI _ induct_step I0] I0')

lemma for_invr_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step:  "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"
  shows "\<lbrace>p\<rbrace>FOR (init, b, incr) INVAR invar DO body OD\<lbrace>q\<rbrace>\<^sub>P"  
  unfolding for_lfp_prog_def for_lfp_invr_prog_def
  by(simp add: from_until_hoare_prog_consequence [OF WF seq_step PHI _ induct_step I0] I0')

lemma for_invr_vrt_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step:  "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"
  shows "\<lbrace>p\<rbrace>FOR (init, b, incr) INVAR invar VRT \<guillemotleft>R\<guillemotright> DO body OD\<lbrace>q\<rbrace>\<^sub>P"  
  unfolding for_lfp_prog_def for_lfp_invr_vrt_prog_def
  by(simp add: from_until_hoare_prog_consequence [OF WF seq_step PHI _ induct_step I0] I0')
    
lemma for_hoare_prog_wp:
  assumes WF : "wf R"
  assumes I0: "`p\<Rightarrow> p''`"  
  assumes seq_step: "\<lbrace>p''\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e=\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding for_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0]
                while_hoare_prog_wp[OF WF uimp_refl PHI I0' induct_step])

lemma for_invr_hoare_prog_wp:
  assumes WF : "wf R"
  assumes I0: "`p \<Rightarrow> p''`"  
  assumes seq_step: "\<lbrace>p''\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e=\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) INVAR invar DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_prog_def for_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0]
                while_hoare_prog_wp[OF WF uimp_refl PHI I0' induct_step])

lemma for_invr_vrt_hoare_prog_wp[hoare_wp_rules]:
  assumes WF : "wf R"
  assumes I0: "`p \<Rightarrow> p''`"  
  assumes seq_step: "\<lbrace>p''\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e=\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) INVAR invar VRT \<guillemotleft>R\<guillemotright>DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_vrt_prog_def for_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0]
                while_hoare_prog_wp[OF WF uimp_refl PHI I0' induct_step])

lemma for_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding for_lfp_prog_def_alt  
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0']
                while_hoare_prog_sp[OF WF uimp_refl induct_step I0])
 
lemma for_invr_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0':  "`q'' \<Rightarrow> invar`"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) INVAR invar DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_prog_def for_lfp_prog_def_alt  
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0']
                while_hoare_prog_sp[OF WF uimp_refl induct_step I0])
     
    
lemma for_invr_vrt_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0':"`q''\<Rightarrow> invar`" 
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) INVAR invar VRT \<guillemotleft>R\<guillemotright>DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_vrt_prog_def for_lfp_prog_def_alt  
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0']
                while_hoare_prog_sp[OF WF uimp_refl induct_step I0])
     
lemmas loop_invr_vrt_hoare_prog_sp_instantiated [hoare_sp_rules] = 
       while_invr_vrt_hoare_prog_sp [where e = "&\<Sigma>"]
       for_invr_vrt_hoare_prog_sp [where e = "&\<Sigma>"]
       do_while_invr_vrt_hoare_prog_sp [where e = "&\<Sigma>"]
       from_until_invr_vrt_hoare_prog_sp[where e = "&\<Sigma>"]
 
section {*VCG*} 
  
subsection {*VCG General Purpose Tactics*}      
text{* Automating premises insertion*}  
method_setup insert_assms = \<open>Scan.succeed (fn _ => CONTEXT_METHOD (fn facts => fn (ctxt,st) => let
   val tac = HEADGOAL (Method.insert_tac ctxt facts)
   val ctxt = Method.set_facts [] ctxt
 in Method.CONTEXT ctxt (tac st)
 end))\<close>                      
                       
text {* The defer processing and the thin_tac processing in the sequel was inspired by tutorial5.thy in Peter Lammich course
        \url{https://bitbucket.org/plammich/certprog_public/downloads/}*}
 
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

text {*vcg_can_defer is a tactic that succeed if the conclusion of a goal is not Hoare triple
       or if it has no DEFERRED markup*}  
  
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
  
subsection {*VCG Post Processing Tactics*} 
  
text{*Tactics and methods in this section are used to do Post-Processing on the generated VCs.
      Namely, The application of symbolic execution laws from the theory usubst
     to the VCs in a very controlled way.*}  
  
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
  
subsection {*VCG Goal Beautify Tactics*}    

text{*Tactics and methods in this section are used to beautify the goals before presenting them to the user.
      Namely, after the application of post-processing a lot of semantic machinery and debugging information
      remains existing in the different proof goals. The methods below clean it up since these 
      assumptions are useless at this point.
    *}
  
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
  (match conclusion in "_ (get\<^bsub>x\<^esub> A)" for x A \<Rightarrow> \<open>rule GET_REMOVER[where L= x and s= A], simp only:\<close>)+,
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

subsection {*VCG Core Tactics*}    
    
method hoare_sp_vcg_pre = (simp only: seqr_assoc[symmetric])?, rule post_weak_prog_hoare  

method hoare_sp_rule_apply = rule hoare_sp_rules

method hoare_wp_rule_apply = rule hoare_wp_rules

method hoare_annotaion_rule_apply = rule hoare_wp_rules  
  
named_theorems lens_laws_vcg_simps
  
lemmas [lens_laws_vcg_simps] =
  lens_indep.lens_put_irr1
  lens_indep.lens_put_irr2

method vcg_step_solver methods solver = 
       (hoare_sp_rule_apply | solver)

text \<open>A one step vcg without post processing nor debugging information. The output of this
      method is: for the goal, on which it is applied to, a upred.\<close>
  
method  hoare_sp_vcg_step = (hoare_sp_rule_apply | vcg_defer)

text \<open>A multiple step vcg without post processing nor debugging information. The output of this
      method is proof goals of the form of upreds.\<close>  
method  hoare_sp_vcg_steps = hoare_sp_vcg_pre, hoare_sp_vcg_step+ , (unfold DEFERRED_def)

method vcg_hol_post_processing_debugger = 
   (pred_simp(*TODO: pred_simp need to be applied in a controlled way*))?,
   (simp only:  lens_laws_vcg_simps)?(*TODO: if this fails add a debug message here*)
  
named_theorems lens_get_lens_put_simplifer
declare lens_laws_vcg_simps[lens_get_lens_put_simplifer]  
declare vwb_simplifier[lens_get_lens_put_simplifer]
declare mwb_lens.put_put[lens_get_lens_put_simplifer] 
declare weak_lens.put_get[lens_get_lens_put_simplifer]
declare wb_lens.get_put[lens_get_lens_put_simplifer]
declare bij_lens.strong_get_put[lens_get_lens_put_simplifer]
  
method vcg_hol_post_processing = 
   (pred_simp(*TODO:pred_simp need to be applied in a controlled way*))?,
   (auto simp only: lens_get_lens_put_simplifer)?

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
    (hoare_sp_vcg_steps; ((unfold pr_var_def in_var_def out_var_def)?, (unfold lens_indep_all_alt)?,
                               ((simp only: lens_indep_all_simplifier)+ (*TODO: Substitute with a debug mode version*))?,
                                 clarsimp?, 
                                 (vcg_upreds_post_processing_debugger+)?,
                                 vcg_hol_post_processing_debugger))
 
method hoare_sp_vcg_steps_pp = 
    (hoare_sp_vcg_steps; ((unfold pr_var_def in_var_def out_var_def)?, (unfold lens_indep_all_alt)?,
                               ((simp only: lens_indep_all_simplifier)+)?,
                                 clarsimp?,
                                 (vcg_upreds_post_processing+)?,
                                  vcg_hol_post_processing(*TODO: ADD SOLVING STEP HERE*)))  

method vcg_hoare_sp_steps_pp_beautify = 
  (hoare_sp_vcg_steps_pp; get_remover?; (vcg_elim_determ beautify_thms)?)    
section {*Experiments on VCG*}

subsection {* Through these experiments I want to observe the following problems: 
              - I want to deal with the problem of nested existential(SOLVED)
              - I want to deal with the problem of blow up due to the semantic machinery coming with lenses(SOLVED)
              - I want to have modularity(NOT SOLVED)

*}

lemmata increment_method: 
  assumes "lens_indep_all [x, y]"
  assumes "vwb_lens x"  "vwb_lens y"
  shows  
"\<lbrace>&y >\<^sub>u 0\<rbrace>
   x :== 0 ; 
   INVAR &y >\<^sub>u 0 \<and> &y \<ge>\<^sub>u &x 
   VRT \<guillemotleft>(measure o Rep_uexpr) (&y - &x)\<guillemotright> 
   WHILE &x <\<^sub>u &y DO x:== (&x + 1) OD
 \<lbrace>&y =\<^sub>u &x\<rbrace>\<^sub>P"
  done
    
subsection {*even count program*} 

lemmata even_count_gen:
  assumes "lens_indep_all [i,j]"
  assumes "vwb_lens i" "vwb_lens j"  
  shows  
"\<lbrace>\<guillemotleft>in_val\<guillemotright> >\<^sub>u 0 \<rbrace>
   i :== \<guillemotleft>0::int\<guillemotright>;
   j :== 0 ; 
   INVAR  (&j =\<^sub>u (&i + 1) div \<guillemotleft>2\<guillemotright> \<and> &i \<le>\<^sub>u \<guillemotleft>in_val\<guillemotright>) 
   VRT \<guillemotleft>measure (nat o (Rep_uexpr (\<guillemotleft>in_val\<guillemotright> - &i)))\<guillemotright>
   WHILE &i <\<^sub>u \<guillemotleft>in_val\<guillemotright>
   DO
     IF &i mod \<guillemotleft>2\<guillemotright> =\<^sub>u 0 
     THEN j :== (&j + 1)
     ELSE SKIP 
     FI;
    i :== (&i + 1)
   OD
 \<lbrace>&j =\<^sub>u (\<guillemotleft>in_val\<guillemotright> + 1)div \<guillemotleft>2\<guillemotright>\<rbrace>\<^sub>P" 
    apply presburger+    
  done   

lemmata even_count_gen':
  assumes "lens_indep_all [i,j, endd]"
  assumes  "vwb_lens i" "vwb_lens j"  
  shows  
"\<lbrace>\<guillemotleft>in_val\<guillemotright> >\<^sub>u 0\<rbrace>
   i :== \<guillemotleft>0::int\<guillemotright>;
   j :== 0 ; 
   INVAR  (&j =\<^sub>u (&i + 1) div 2 \<and> &i \<le>\<^sub>u \<guillemotleft>in_val\<guillemotright>) 
   VRT \<guillemotleft>measure (nat o (Rep_uexpr (\<guillemotleft>in_val\<guillemotright> - &i)))\<guillemotright>
   WHILE &i <\<^sub>u \<guillemotleft>in_val\<guillemotright>
   DO
     IF &i mod 2 =\<^sub>u 0 
     THEN j :== (&j + 1)
     ELSE SKIP 
     FI;
    i :== (&i + 1)
   OD
 \<lbrace>&j =\<^sub>u (\<guillemotleft>in_val\<guillemotright> + 1)div 2\<rbrace>\<^sub>P"  
    apply (simp_all add: zdiv_zadd1_eq)
  done    
    
subsection {*sqrt program*}
  
definition Isqrt :: "int \<Rightarrow> int \<Rightarrow> bool" 
   where "Isqrt n\<^sub>0 r \<equiv> 0\<le>r \<and> (r-1)\<^sup>2 \<le> n\<^sub>0" 
     
lemma Isqrt_aux:
  "0 \<le> n\<^sub>0 \<Longrightarrow> Isqrt n\<^sub>0 1"
  "\<lbrakk>0 \<le> n\<^sub>0; r * r \<le> n\<^sub>0; Isqrt n\<^sub>0 r\<rbrakk> \<Longrightarrow> Isqrt n\<^sub>0 (r + 1)"
  "\<lbrakk>0 \<le> n\<^sub>0; \<not> r * r \<le> n\<^sub>0; Isqrt n\<^sub>0 r\<rbrakk> \<Longrightarrow> (r - 1)\<^sup>2 \<le> n\<^sub>0 \<and> n\<^sub>0 < r\<^sup>2"
  "Isqrt n\<^sub>0 r \<Longrightarrow> r * r \<le> n\<^sub>0 \<Longrightarrow> r\<le>n\<^sub>0"
  "\<lbrakk>0 \<le> n\<^sub>0; \<not> r * r \<le> n\<^sub>0; Isqrt n\<^sub>0 r\<rbrakk> \<Longrightarrow> 0 < r"
  apply (auto simp: Isqrt_def power2_eq_square algebra_simps)
  by (smt combine_common_factor mult_right_mono semiring_normalization_rules(3))
      
lemma sqrt_prog_correct:
  assumes "vwb_lens r"
  shows
"\<lbrace>0 \<le>\<^sub>u \<guillemotleft>input_val\<guillemotright>\<rbrace>
   r :== 1 ; 
   INVAR 0\<le>\<^sub>u \<guillemotleft>input_val\<guillemotright> \<and> bop Isqrt (\<guillemotleft>input_val\<guillemotright>) (&r)
   VRT  \<guillemotleft>measure (nat o (Rep_uexpr ((\<guillemotleft>input_val\<guillemotright> + 1) - &r)))\<guillemotright>
   WHILE (&r * &r \<le>\<^sub>u \<guillemotleft>input_val\<guillemotright>)
   DO 
    r :== (&r + 1)
   OD;
   r :== (&r - 1)
 \<lbrace>0\<le>\<^sub>u &r \<and> uop power2 (&r) \<le>\<^sub>u \<guillemotleft>input_val\<guillemotright> \<and> \<guillemotleft>input_val\<guillemotright> <\<^sub>u uop power2 (&r + 1)\<rbrace>\<^sub>P" 
  apply (insert assms)
   supply Isqrt_aux [simp]
  apply vcg_hoare_sp_steps_pp_beautify
  done    
    
subsection {*gcd*}
  
text {*In the followin we illustrate the effect of domain theory based approach. 
       Namely, in the lemma gcd_correct we use the hard coded max function 
       @{term "(trop If (&r >\<^sub>u &x) (&r) (&x))"}. This leads to long proof. 
       However in gcd_correct' we use the max function from HOL library. 
      This leads to a shorter proof since max library contains the necessary lemmas that simplify
       the reasoning.*}
  
lemmata gcd_correct:
  assumes "lens_indep_all [r, x]"
  assumes "vwb_lens r" "vwb_lens x" 
  shows  
"\<lbrace>&r =\<^sub>u \<guillemotleft>input_val_a\<guillemotright> \<and> &x =\<^sub>u \<guillemotleft>input_val_b\<guillemotright> \<and> \<guillemotleft>input_val_b\<guillemotright> >\<^sub>u 0 \<and> \<guillemotleft>input_val_a\<guillemotright>>\<^sub>u 0\<rbrace> 
   INVAR &r >\<^sub>u0 \<and> &x >\<^sub>u 0 \<and> bop gcd (&r) (&x) =\<^sub>u  bop gcd (\<guillemotleft>input_val_a\<guillemotright>) (\<guillemotleft>input_val_b\<guillemotright>)
   VRT \<guillemotleft>measure (Rep_uexpr (trop If (&r >\<^sub>u &x) (&r) (&x)))\<guillemotright>
   WHILE \<not>(&r =\<^sub>u &x)
   DO
    IF &r >\<^sub>u &x
    THEN r :== (&r - &x)
    ELSE x :== (&x - &r)
    FI
   OD
 \<lbrace>&r =\<^sub>u &x \<and> &r =\<^sub>u bop gcd (\<guillemotleft>input_val_a\<guillemotright>) (\<guillemotleft>input_val_b\<guillemotright>)\<rbrace>\<^sub>P"
     apply (auto simp: gcd_diff1_nat)
   apply (metis gcd.commute gcd_diff1_nat not_le)+
  done  
     
lemmata gcd_correct':
  assumes "lens_indep_all [r, x]"
  assumes "vwb_lens r" "vwb_lens x" 
  shows  
"\<lbrace>&r =\<^sub>u \<guillemotleft>input_val_a\<guillemotright> \<and> &x =\<^sub>u \<guillemotleft>input_val_b\<guillemotright> \<and> \<guillemotleft>input_val_b\<guillemotright>>\<^sub>u 0 \<and> \<guillemotleft>input_val_a\<guillemotright>>\<^sub>u 0\<rbrace> 
   INVAR &r >\<^sub>u0 \<and> &x >\<^sub>u 0 \<and> bop gcd (&r) (&x) =\<^sub>u  bop gcd \<guillemotleft>input_val_a\<guillemotright> \<guillemotleft>input_val_b\<guillemotright>
   VRT \<guillemotleft>measure (Rep_uexpr (bop max (&r) (&x)))\<guillemotright>
   WHILE \<not>(&r =\<^sub>u &x)
   DO
    IF &r >\<^sub>u &x
    THEN r :== (&r - &x)
    ELSE x :== (&x - &r)
    FI
   OD
 \<lbrace>&r =\<^sub>u &x \<and> &r =\<^sub>u bop gcd \<guillemotleft>input_val_a\<guillemotright> \<guillemotleft>input_val_b\<guillemotright>\<rbrace>\<^sub>P"
   apply (simp add: gcd_diff1_nat)
  apply (metis gcd.commute gcd_diff1_nat not_le)
  done  
    
section {*Arrays*}
  
subsection {*Array Max program: one-variable loop*}

lemmata max_program_correct:
  assumes "r \<bowtie> i" 
  assumes "vwb_lens i" "vwb_lens r" 
  shows  
"\<lbrace>uop length \<guillemotleft>input_val_a\<guillemotright> \<ge>\<^sub>u1 \<and> &i =\<^sub>u 1 \<and> &r =\<^sub>u bop nth \<guillemotleft>input_val_a:: int list\<guillemotright> 0\<rbrace> 
   INVAR  0 <\<^sub>u &i \<and> &i \<le>\<^sub>u  uop length \<guillemotleft>input_val_a\<guillemotright> \<and> &r =\<^sub>u uop Max ran\<^sub>u(bop take (&i) \<guillemotleft>input_val_a\<guillemotright>) 
   VRT  \<guillemotleft>measure (Rep_uexpr (uop length \<guillemotleft>input_val_a\<guillemotright> - (&i)))\<guillemotright>  
   WHILE \<not>(&i =\<^sub>u uop length \<guillemotleft>input_val_a\<guillemotright>) 
   DO 
      IF &r <\<^sub>u  bop nth \<guillemotleft>input_val_a\<guillemotright> (&i) 
      THEN r :== bop nth \<guillemotleft>input_val_a\<guillemotright> (&i)
      ELSE SKIP
      FI;
      i :== (&i + 1)
   OD   
 \<lbrace>&r =\<^sub>uuop Max ran\<^sub>u(\<guillemotleft>input_val_a\<guillemotright>)\<rbrace>\<^sub>P"  
  subgoal for A 
    by (cases input_val_a; auto)
  subgoal for A i                  
    apply (clarsimp simp: take_Suc_conv_app_nth)
    apply (subst Max_insert) by auto
  subgoal for A i 
    apply (clarsimp simp: take_Suc_conv_app_nth)  
    apply (subst Max_insert) by auto
  done  
    
find_theorems name: "rep_eq" "LENS_GET_TAG (Rep_uexpr ?e = ?t)" (*This what pred_simp uses...*)
 
(*
TODO List for next iteration:

*)      


end

