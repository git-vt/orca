chapter{*Meta-logical Operators*}
theory Unrest
imports Expressions
begin 
section{*Unrestriction*}
text {*In this section we define one of the meta-logical operators on lenses. 
       Unrestriction is an operator used to express that the evaluation of a given substitution 
       does not depend on a given lens. It can be used for example to express that a given
       program variable, represented by a lens, does not occur in a given expression
       of the programming language. In other words Unrestriction encode the semantic freshness, 
       that allows to reason about the presence of variables in expressions 
       without being concerned with abstract syntax trees. This is a sufficient
       notion to prove many laws that would ordinarily rely on an \emph{fv} function.*}

named_theorems unrest

lift_definition unrest :: "('\<tau>, '\<alpha>) var \<Rightarrow> ('exp, '\<alpha>) expr \<Rightarrow> bool" (infix "\<sharp>" 20)
is "\<lambda>var exp. \<forall> \<sigma> v. exp (put\<^bsub>var\<^esub> \<sigma> v) = exp \<sigma>" .

lemma unrest_var_comp [unrest]:
  assumes 1: "x \<sharp> P"
  and     2: "y \<sharp> P"
  shows "(x;\<^sub>Ly) \<sharp> P"
  using 1 2
  by (transfer, simp add: lens_defs)

lemma unrest_const [unrest]: "x \<sharp> \<guillemotleft>v\<guillemotright>"
  by (transfer, simp)

lemma unrest_var [unrest]: 
  assumes 1: "vwb_lens x"
  and     2: "x \<bowtie> y"
  shows "y \<sharp> imp_var x"
  using 1 2
  by (transfer, auto)

lemma unrest_uop [unrest]: 
  assumes 1:"x \<sharp> e"
  shows    "x \<sharp> uop f e"
  using assms
  by (transfer, simp)

lemma unrest_bop [unrest]: 
  assumes 1:"x \<sharp> u" 
  and     2:"x \<sharp> v" 
  shows   "x \<sharp> bop f u v"
  using assms
  by (transfer, simp)

lemma unrest_trop [unrest]: 
  assumes 1: "x \<sharp> u"
  and     2: "x \<sharp> v" 
  and     3: "x \<sharp> w"
  shows "x \<sharp> trop f u v w"
  using assms
  by (transfer, simp)

lemma unrest_qtop [unrest]: 
  assumes 1:"x \<sharp> u"
  and     2:"x \<sharp> v" 
  and     3:"x \<sharp> w" 
  and     4:"x \<sharp> y" 
  shows "x \<sharp> qtop f u v w y"
  using assms
  by (transfer, simp)

lemma id_lift_expr_eq:
  "(x \<sharp> uop id) = (x \<sharp> (\<lambda>\<sigma>. id \<sigma>))"
  by (transfer, auto)

lemma unrest_id [unrest]: 
  assumes 1: "ief_lens x"
  shows "x \<sharp> \<guillemotleft>id\<guillemotright>"
  using 1
  by (transfer, auto)


lemma eq_lift_expr_eq:
  "(x \<sharp> (bop (op =) u v)) = (x \<sharp> (\<lambda>\<sigma>. u \<sigma> = v \<sigma>))"
  by (transfer, auto)

lemma unrest_eq [unrest]: 
  assumes 1:"x \<sharp> u"
  and     2:"x \<sharp> v"
  shows  "x \<sharp> (bop (op =) u v)"
  using 1 2 by (transfer, auto)

lemma unrest_numeral [unrest]: 
  assumes 1: "x \<sharp> n"
  shows "x \<sharp> (\<lambda>\<sigma>. (numeral (n \<sigma>)))"
  using 1
  by (auto simp: unrest.abs_eq)

lemma unrest_sgn [unrest]:
  assumes 1: "x \<sharp> u"
  shows "x \<sharp> (\<lambda>\<sigma>. (sgn (u \<sigma>)))"
  using 1
  by (auto simp: unrest.abs_eq)

lemma unrest_abs [unrest]:
  assumes 1: "x \<sharp> u"
  shows "x \<sharp> (\<lambda>\<sigma>. (abs (u \<sigma>)))"
  using 1
  by (auto simp: unrest.abs_eq)

lemma plus_lift_expr_eq: 
  "(x \<sharp> (bop (op +) u v)) = (x \<sharp> (\<lambda>\<sigma>. u \<sigma> + v \<sigma>))"
  by transfer auto

lemma unrest_plus [unrest]: 
  assumes 1:"x \<sharp> u"
  and     2:"x \<sharp> v"
  shows "(x \<sharp> (bop (op +) u v))"
  using assms
  by transfer auto

lemma unrest_uminus [unrest]: 
  assumes 1: "x \<sharp> u"
  shows "x \<sharp> (\<lambda>\<sigma>. -(u \<sigma>))"    
  using 1
  by (auto simp: unrest.abs_eq)

lemma minus_lift_expr_eq: 
  "(x \<sharp> (bop (op -) u v)) = (x \<sharp> (\<lambda>\<sigma>. u \<sigma> - v \<sigma>))"
  by transfer auto

lemma unrest_minus [unrest]: 
  assumes 1:"x \<sharp> u"
  and     2:"x \<sharp> v"
  shows "x \<sharp> (bop (op -) u v)"
  using 1 2
  by transfer auto

lemma times_lift_expr_eq: 
  "(x \<sharp> (bop (op *) u v)) = (x \<sharp> (\<lambda>\<sigma>. u \<sigma> * v \<sigma>))"
  by transfer auto

lemma unrest_times [unrest]: 
  assumes 1:"x \<sharp> u"
  and     2:"x \<sharp> v" 
  shows "x \<sharp> (bop (op *) u v)"
  using 1 2
  by transfer auto

lemma times_devide_expr_eq: 
  "(x \<sharp> (bop (op /) u v)) = (x \<sharp> (\<lambda>\<sigma>. u \<sigma> / v \<sigma>))"
  by transfer auto

lemma unrest_divide [unrest]: 
  assumes 1:"x \<sharp> u"
  and     2:"x \<sharp> v"
  shows "x \<sharp> (bop (op /) u v)"
  using 1 2
  by transfer auto

lemma unrest_ulambda [unrest]:
  assumes 1: "\<forall> x. v \<sharp> F x" 
  shows "v \<sharp> (\<lambda>x. (\<lambda>\<sigma>. (F \<sigma>) x))"
  using 1
  by (transfer, simp)

lemma times_mod_expr_eq: 
  "(x \<sharp> (bop (op mod) u v)) = (x \<sharp> (\<lambda>\<sigma>. u \<sigma> mod v \<sigma>))"
  by transfer auto

lemma unrest_mod [unrest]: 
  assumes 1:"x \<sharp> u"
  and     2:"x \<sharp> v"
  shows "x \<sharp> (bop (op mod) u v)"
  using 1 2
  by transfer auto

lemma times_div_expr_eq: 
  "(x \<sharp> (bop (op div) u v)) = (x \<sharp> (\<lambda>\<sigma>. u \<sigma> div v \<sigma>))"
  by transfer auto

lemma unrest_div [unrest]: 
  assumes 1:"x \<sharp> u"
  and     2:"x \<sharp> v"
  shows "x \<sharp> (bop (op div) u v)"
  using 1 2
  by transfer auto

end