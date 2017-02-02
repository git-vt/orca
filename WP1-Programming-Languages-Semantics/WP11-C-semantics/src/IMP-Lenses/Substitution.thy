
chapter "Syntax of Commands"

theory Substitution imports Lenses Unrest  "~~/src/HOL/Eisbach/Eisbach"

begin

subsection {* Substitution definitions *}

text {* We introduce a polymorphic constant that will be used to represent application of
        a substitution, and also a set of theorems to represent laws. *}

(*consts
  usubst :: "'s \<Rightarrow> 'a \<Rightarrow> 'b"*) 

named_theorems states

text {* A substitution is simply a transformation on the alphabet; it shows how variables
        should be mapped to different values. *}

type_synonym ('\<alpha>,'\<beta>) pstates = "'\<alpha> \<Rightarrow> '\<beta>"

type_synonym '\<alpha> states = "'\<alpha> \<Rightarrow> '\<alpha>"

lift_definition subst :: "('\<alpha>, '\<beta>) pstates \<Rightarrow> ('\<tau> , '\<beta>) expr \<Rightarrow> ('\<tau> , '\<alpha>) expr" (infixr "\<dagger>" 80) is
"\<lambda> \<sigma> e s. e (\<sigma> s)" .

text {* Update the value of a variable to an expression in a substitution *}

consts subst_upd :: "('\<alpha>,'\<beta>) pstates \<Rightarrow> 'v \<Rightarrow> ('\<tau> , '\<alpha>) expr \<Rightarrow> ('\<alpha>,'\<beta>) pstates"


definition subst_upd_var :: "('\<alpha>,'\<beta>) pstates \<Rightarrow> ('\<tau> , '\<beta> ) var \<Rightarrow> ('\<tau>, '\<alpha>) expr \<Rightarrow> ('\<alpha>,'\<beta>) pstates" where
"subst_upd_var \<sigma> x v = (\<lambda> s. put\<^bsub>x\<^esub> (\<sigma> s) (v s))"

adhoc_overloading
  subst_upd subst_upd_var 

text {*Lookup the expression associated with a variable in a substitution*}

lift_definition esubst_lookup :: "('\<alpha>,'\<beta>) pstates \<Rightarrow>  ('\<tau> , '\<beta> ) var \<Rightarrow> ('\<tau>, '\<alpha>) expr" ("\<langle>_\<rangle>\<^sub>s")
is "\<lambda> \<sigma> x s. get\<^bsub>x\<^esub> (\<sigma> s)" .

nonterminal smaplet and smaplets

syntax
  "_smaplet"  :: "['a, 'a] => smaplet"             ("_ /\<mapsto>\<^sub>s/ _")
  ""          :: "smaplet => smaplets"            ("_")
  "_SMaplets" :: "[smaplet, smaplets] => smaplets" ("_,/ _")
  "_SubstUpd" :: "['m states, smaplets] => 'm states" ("_/'(_')" [900,0] 900)
  "_Subst"    :: "smaplets => 'a \<rightharpoonup> 'b"            ("(1[_])")

translations
  "_SubstUpd m (_SMaplets xy ms)"     == "_SubstUpd (_SubstUpd m xy) ms"
  "_SubstUpd m (_smaplet x y)"        == "CONST subst_upd m x y"
  "_Subst ms"                         == "_SubstUpd (CONST id) ms"
  "_Subst (_SMaplets ms1 ms2)"        <= "_SubstUpd (_Subst ms1) ms2"
  "_SMaplets ms1 (_SMaplets ms2 ms3)" <= "_SMaplets (_SMaplets ms1 ms2) ms3"

text {*unrest_usebst basically lift unrest to statements*}

definition unrest_usubst :: "('a, '\<alpha>) var \<Rightarrow> '\<alpha> states \<Rightarrow> bool" (infix "\<sharp>\<sharp>" 20)
where "unrest_usubst x \<sigma> = (\<forall> \<rho> v. \<sigma> (put\<^bsub>x\<^esub> \<rho> v) = put\<^bsub>x\<^esub> (\<sigma> \<rho>) v)"

subsection {* Substitution laws *}

text {* We set up a simple substitution tactic that applies substitution and unrestriction laws *}

method subst_tac = (simp add: states unrest)?
 
lemma usubst_lookup_id [states]: "\<langle>id\<rangle>\<^sub>s x = imp_var x"
  by (transfer, simp)

lemma usubst_lookup_upd [states]:
  assumes "mwb_lens x"
  shows "\<langle>\<sigma>(x \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x = v"
  using assms
  by (simp add: subst_upd_var_def, transfer) (simp)
  
lemma usubst_upd_idem [states]:
  assumes "mwb_lens x"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, x \<mapsto>\<^sub>s v) = \<sigma>(x \<mapsto>\<^sub>s v)"
  by (simp add: subst_upd_var_def assms comp_def)

lemma usubst_upd_comm:
  assumes "x \<bowtie> y"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v) = \<sigma>(y \<mapsto>\<^sub>s v, x \<mapsto>\<^sub>s u)"
  using assms
  by (rule_tac ext, auto simp add: subst_upd_var_def assms comp_def lens_indep_comm)
 
lemma usubst_upd_comm2:
  assumes "z \<bowtie> y" and "mwb_lens x"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v, z \<mapsto>\<^sub>s s) = \<sigma>(x \<mapsto>\<^sub>s u, z \<mapsto>\<^sub>s s, y \<mapsto>\<^sub>s v)"
  using assms ext unfolding subst_upd_var_def assms comp_def 
  by (simp add: lens_indep_comm)

lemma usubst_upd_var_id [states]: 
  "vwb_lens x \<Longrightarrow> [x \<mapsto>\<^sub>s imp_var x] = id"
  using assms unfolding subst_upd_var_def
  by transfer (rule ext,auto)

lemma usubst_lookup_upd_indep [states]:
  assumes "mwb_lens x" "x \<bowtie> y"
  shows "\<langle>\<sigma>(y \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  using assms unfolding  subst_upd_var_def
  by (transfer, simp)

lemma subst_unrest [states]: 
  assumes 1: "x \<sharp> P"
  shows "\<sigma>(x \<mapsto>\<^sub>s v) \<dagger> P = \<sigma> \<dagger> P"
  using 1 unfolding subst_upd_var_def
  by (transfer, auto)

lemma id_subst [states]: "id \<dagger> v = v"
  by (transfer, simp)

lemma subst_var [states]: "\<sigma> \<dagger> imp_var x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  by (transfer, simp)

lemma subst_uop [states]: "\<sigma> \<dagger> uop f v = uop f (\<sigma> \<dagger> v) "
  by (transfer, simp)

lemma subst_bop [states]: "\<sigma> \<dagger> bop f u v = bop f (\<sigma> \<dagger> u) (\<sigma> \<dagger> v)"
  by (transfer, simp)

lemma subst_trop [states]: "\<sigma> \<dagger> trop f u v w = 
                            trop f (\<sigma> \<dagger> u) (\<sigma> \<dagger> v) (\<sigma> \<dagger> w)"
  by (transfer, simp)

lemma subst_qtop [states]: "\<sigma> \<dagger> qtop f u v w x = 
                            qtop f (\<sigma> \<dagger> u) (\<sigma> \<dagger> v) (\<sigma> \<dagger> w) (\<sigma> \<dagger> x)"
  by (transfer, simp)

lemma subst_plus [states]: "\<sigma> \<dagger>  bop (op +) x y = bop (op +) (\<sigma> \<dagger> x)  (\<sigma> \<dagger> y) "
  by transfer auto

lemma subst_times [states]: "\<sigma> \<dagger> bop (op *) x y = bop (op *) (\<sigma> \<dagger> x) (\<sigma> \<dagger> y)"
  by transfer auto

lemma subst_mod [states]: "\<sigma> \<dagger>  bop (op mod) x y = bop (op mod )(\<sigma> \<dagger> x) (\<sigma> \<dagger> y)"
  by transfer auto

lemma subst_div [states]: "\<sigma> \<dagger> bop (op div) x y = bop (op div) (\<sigma> \<dagger> x) (\<sigma> \<dagger> y)"
  by transfer auto

lemma subst_minus [states]: "\<sigma> \<dagger> bop (op -) x y =  bop (op -) (\<sigma> \<dagger> x) (\<sigma> \<dagger> y)"
  by transfer auto

lemma subst_uminus [states]: "\<sigma> \<dagger> uop (op -) x = uop (op -) (\<sigma> \<dagger> x)"
  by transfer auto

lemma usubst_sgn [states]: "\<sigma> \<dagger> uop sgn x = uop sgn (\<sigma> \<dagger> x)"
  by transfer auto

lemma usubst_abs [states]: "\<sigma> \<dagger> uop abs x  = uop abs (\<sigma> \<dagger> x)"
  by transfer auto

lemma subst_zero [states]: "\<sigma> \<dagger> \<guillemotleft>0\<guillemotright> = \<guillemotleft>0\<guillemotright>"
  by transfer auto

lemma subst_one [states]: "\<sigma> \<dagger> \<guillemotleft>1\<guillemotright> = \<guillemotleft>1\<guillemotright>"
  by transfer auto

lemma subst_eq_upred [states]: "\<sigma> \<dagger> bop (op =) x y = bop (op =) (\<sigma> \<dagger> x) (\<sigma> \<dagger> y)"
  by transfer auto

lemma subst_subst [states]: "\<sigma> \<dagger> \<rho> \<dagger> e = (\<rho> \<circ> \<sigma>) \<dagger> e"
  by (transfer, simp)

lemma subst_upd_comp [states]: 
  fixes x :: "('a, '\<alpha>) var"
  shows "\<rho>(x \<mapsto>\<^sub>s v) \<circ> \<sigma> = (\<rho> \<circ> \<sigma>)(x \<mapsto>\<^sub>s \<sigma> \<dagger> v)"
  by (rule ext, simp add: subst_upd_var_def, transfer, simp)

lemma subst_singleton: 
  fixes x :: "('a, '\<alpha>) var"
  assumes "x \<sharp>\<sharp> \<sigma>"
  shows "(\<sigma>(x \<mapsto>\<^sub>s v) \<dagger> P) = (([x \<mapsto>\<^sub>s v]) \<dagger> (\<sigma> \<dagger> P))"
  using assms unfolding  unrest_usubst_def subst_upd_var_def
  by transfer simp

subsection {* Unrestriction laws *}

lemma unrest_usubst_single [unrest]:
  assumes 1: "mwb_lens x"
  and     2: "x \<sharp> v"
  shows    "x \<sharp> ([x \<mapsto>\<^sub>s v] \<dagger> P)"
  using assms unfolding subst_upd_var_def
  by (transfer, simp)

lemma unrest_usubst_id [unrest]:
  assumes "mwb_lens x"
  shows "x \<sharp>\<sharp> id"
  using assms unfolding unrest_usubst_def
  by transfer simp

lemma unrest_usubst_upd [unrest]:
  assumes 1:"x \<bowtie> y"
  and     2:" x \<sharp>\<sharp> \<sigma>"
  and     3:"x \<sharp> v" 
  shows   "x \<sharp>\<sharp> (\<sigma>(y \<mapsto>\<^sub>s v))"
  using assms
  by (simp add: lens_indep_comm subst_upd_var_def unrest.abs_eq unrest_usubst_def)

lemma unrest_subst [unrest]:
  assumes 1:"x \<sharp> P"
  and     2:"x \<sharp>\<sharp> \<sigma>"
  shows "x \<sharp> (\<sigma> \<dagger> P)"
  using assms unfolding unrest_usubst_def
  by (transfer, simp)


end
