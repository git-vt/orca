
section {*Expressions*}
text{*In this section we introduce the type of variables and expressions used in our 
      specification language. Since we use a shallow embedding for expressions we introduce
      the different lifting operators between the different types.*}

theory Expressions imports Lenses "~~/src/Tools/Adhoc_Overloading" 

begin
subsection {*Types*}
text{*In this setting the state-space is represented by the 
      type @{text "\<alpha>"}, and expressions by the type @{text "\<tau>"}*}

type_synonym ('\<tau> , '\<alpha> ) var = "('\<tau> \<Longrightarrow> '\<alpha>)"         
type_synonym  ('\<tau> ,'\<alpha>) expr  =  "'\<alpha>  \<Rightarrow> '\<tau>" 

subsection {*Lifting vars to to expressions*}

lift_definition imp_var :: "('\<tau>, '\<alpha>) var \<Rightarrow> ('\<tau>, '\<alpha>) expr" ("VAR _") is 
  lens_get .

subsection {*Lifting HOL functions to expressions*}

lift_definition Const :: "'t \<Rightarrow> ('t, '\<alpha>) expr" ("\<guillemotleft>_\<guillemotright>") is 
  "\<lambda> v \<sigma>. v" .

lift_definition uop :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('b, '\<alpha>) expr" is 
  "\<lambda> f e \<sigma>. f (e \<sigma>)" .

lift_definition bop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('b, '\<alpha>) expr \<Rightarrow> ('c, '\<alpha>) expr" is 
  "\<lambda> f x y \<sigma>. f (x \<sigma>) (y \<sigma>)" .

lift_definition trop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('b, '\<alpha>) expr \<Rightarrow> ('c, '\<alpha>) expr \<Rightarrow> ('d, '\<alpha>) expr" is
  "\<lambda> f x y z \<sigma>. f (x \<sigma>) (y \<sigma>) (z \<sigma>)" .

lift_definition qtop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 
   ('a, '\<alpha>) expr \<Rightarrow> ('b, '\<alpha>) expr \<Rightarrow> ('c, '\<alpha>) expr \<Rightarrow> ('d, '\<alpha>) expr \<Rightarrow>
   ('e, '\<alpha>) expr" is
   "\<lambda> f x y z w \<sigma>. f (x \<sigma>) (y \<sigma>) (z \<sigma>) (w \<sigma>)" .

subsection {*Lifting HOL Constant operations to expressions*}

abbreviation True_expr :: "(bool, '\<alpha>) expr" ("TRUE")
where "True_expr \<equiv> \<guillemotleft>True\<guillemotright>"

abbreviation False_expr :: "(bool, '\<alpha>) expr" ("FALSE")
where "False_expr \<equiv> \<guillemotleft>False\<guillemotright>"

subsection {*Lifting HOL unary operations to expressions*}

abbreviation uminus_expr :: "('a::uminus, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" ("-\<^sub>e _" [81] 80) 
where "uminus_expr x \<equiv> uop uminus x"

abbreviation inverse_expr :: "('a::inverse, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr"
where "inverse_expr x \<equiv> uop inverse x"

abbreviation sgn_expr ::"('a::sgn, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" ("SGN")
where "sgn_expr x \<equiv> uop sgn x"

abbreviation abs_expr ::"('a::abs, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" ("ABS")
where "abs_expr x \<equiv> uop abs x"

abbreviation Not_expr :: "(bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr"("\<not>\<^sub>e _" [40] 40)
where "Not_expr bexp \<equiv> uop Not bexp "

lift_definition Ex_expr :: "('a, '\<alpha>) var \<Rightarrow> (bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr" ("\<exists>\<^sub>e _ . _" [0, 10] 10)is
"\<lambda> x P b. (\<exists> v. P(put\<^bsub>x\<^esub> b v))" .

lift_definition All_expr ::"('a, '\<alpha>) var \<Rightarrow> (bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr" ("\<forall>\<^sub>e _ . _" [0, 10] 10)is
"\<lambda> x P b. (\<forall> v. P(put\<^bsub>x\<^esub> b v))" .

abbreviation Ex1_expr :: "('a \<Rightarrow> bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr"(binder "\<exists>!\<^sub>e" 10)
where "Ex1_expr P \<equiv> uop Ex1 P"

subsection {*Lifting HOL binary operations to expressions*}

abbreviation eq_expr :: "('a, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr" (infixl "=\<^sub>e" 50)
where "eq_expr x y \<equiv> bop HOL.eq x y"

abbreviation conj_expr :: "(bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr"(infixr "\<and>\<^sub>e" 35)
where "conj_expr bexp1 bexp2 \<equiv>  bop conj bexp1 bexp2"

abbreviation disj_expr :: "(bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr"(infixr "\<or>\<^sub>e" 30)
where "disj_expr bexp1 bexp2 \<equiv>  bop disj bexp1 bexp2"

abbreviation implies_expr :: "(bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr"(infixr "\<longrightarrow>\<^sub>e" 25)
where "implies_expr bexp1 bexp2 \<equiv>  bop implies bexp1 bexp2"

abbreviation plus_expr :: "('a::plus, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" (infixl "+\<^sub>e" 65)
where "plus_expr x y \<equiv> bop (op +) x y"

abbreviation minus_expr :: "('a::minus, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" (infixl "-\<^sub>e" 65)
where "minus_expr x y \<equiv> bop (op -) x y"

abbreviation times_expr :: "('a::times, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" (infixl "*\<^sub>e" 65)
where "times_expr x y \<equiv> bop (op *) x y"

abbreviation divide_expr :: "('a::divide, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" (infixl "div\<^sub>e" 70)
where  "divide_expr x y \<equiv> bop divide x y"

abbreviation mod_expr ::"('a::Divides.div, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" (infixl "mod\<^sub>e" 70)
where "mod_expr x y \<equiv> bop (op mod) x y"

abbreviation less_eq_expr :: "('a::ord, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr" ("(_/ \<le>\<^sub>e _)"  [51, 51] 50)
where "less_eq_expr x y \<equiv>  bop (op \<le>) x y" 

abbreviation less_expr :: "('a::ord, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr"  ("(_/ <\<^sub>e _)"  [51, 51] 50)
where "less_expr x y \<equiv> (bop less x y)"

subsection {*Drop boolean expressions*}

lemma drop_bexp_eq:"(P = TRUE) = (\<forall>\<sigma>. P \<sigma>)"
  by (transfer, auto)

lift_definition drop_bexp :: "(bool ,  '\<alpha>) expr \<Rightarrow> bool" ("\<lceil>_\<rceil>")is
"\<lambda>P. (\<forall>\<sigma>. P \<sigma>)".


end