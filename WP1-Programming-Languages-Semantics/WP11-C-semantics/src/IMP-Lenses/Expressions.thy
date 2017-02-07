
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

definition True_expr :: "(bool, '\<alpha>) expr" ("TRUE")
where [simp]:"True_expr = \<guillemotleft>True\<guillemotright>"

definition False_expr :: "(bool, '\<alpha>) expr" ("FALSE")
where [simp]:"False_expr = \<guillemotleft>False\<guillemotright>"

subsection {*Lifting HOL unary operations to expressions*}

definition uminus_expr :: "('a::uminus, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" ("-\<^sub>e _" [81] 80) 
where [simp]:"uminus_expr x = uop uminus x"

definition inverse_expr :: "('a::inverse, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr"
where [simp]:"inverse_expr x = uop inverse x"

definition sgn_expr ::"('a::sgn, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" ("SGN")
where [simp]:"sgn_expr x = uop sgn x"

definition abs_expr ::"('a::abs, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" ("ABS")
where [simp]:"abs_expr x = uop abs x"

definition Not_expr :: "(bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr"("\<not>\<^sub>e _" [40] 40)
where [simp]:"Not_expr bexp = uop Not bexp "

definition All_expr :: "('a \<Rightarrow> bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr"(binder "\<forall>\<^sub>e" 10)
where [simp]:"All_expr P = uop All P"

definition Ex_expr :: "('a \<Rightarrow> bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr"(binder "\<exists>\<^sub>e" 10)
where [simp]:"Ex_expr P = uop Ex P"

definition Ex1_expr :: "('a \<Rightarrow> bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr"(binder "\<exists>!\<^sub>e" 10)
where [simp]:"Ex1_expr P = uop Ex1 P"

subsection {*Lifting HOL binary operations to expressions*}

definition eq_expr :: "('a, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr" (infixl "=\<^sub>e" 50)
where [simp]:"eq_expr x y = bop HOL.eq x y"

definition conj_expr :: "(bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr"(infixr "\<and>\<^sub>e" 35)
where [simp]:"conj_expr bexp1 bexp2 =  bop conj bexp1 bexp2"

definition disj_expr :: "(bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr"(infixr "\<or>\<^sub>e" 30)
where [simp]:"disj_expr bexp1 bexp2 =  bop disj bexp1 bexp2"

definition implies_expr :: "(bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr"(infixr "\<longrightarrow>\<^sub>e" 25)
where [simp]:"implies_expr bexp1 bexp2 =  bop implies bexp1 bexp2"

definition plus_expr :: "('a::plus, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" (infixl "+\<^sub>e" 65)
where [simp]:"plus_expr x y = bop (op +) x y"

definition minus_expr :: "('a::minus, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" (infixl "-\<^sub>e" 65)
where [simp]:"minus_expr x y = bop (op -) x y"

definition times_expr :: "('a::times, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" (infixl "*\<^sub>e" 65)
where [simp]:"times_expr x y = bop (op *) x y"

definition divide_expr :: "('a::divide, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" (infixl "div\<^sub>e" 70)
where [simp]: "divide_expr x y = bop divide x y"

definition mod_expr ::"('a::Divides.div, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr" (infixl "mod\<^sub>e" 70)
where [simp]:"mod_expr x y = bop (op mod) x y"

definition less_eq_expr :: "('a::ord, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr" ("(_/ \<le>\<^sub>e _)"  [51, 51] 50)
where  [simp]: "less_eq_expr x y =  bop (op \<le>) x y" 

definition less_expr :: "('a::ord, '\<alpha>) expr \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr"  ("(_/ <\<^sub>e _)"  [51, 51] 50)
where [simp]:"less_expr x y = (bop less x y)"

subsection {*Drop boolean expressions*}

lemma drop_bexp_eq:"(P = TRUE) = (\<forall>\<sigma>. P \<sigma>)"
  by (simp, transfer, auto)

lift_definition drop_bexp :: "(bool ,  '\<alpha>) expr \<Rightarrow> bool" ("\<lceil>_\<rceil>")is
"\<lambda>P. (\<forall>\<sigma>. P \<sigma>)".


end