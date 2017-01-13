chapter {*Types and Core Definitions of C*}
theory "IMP-function"

imports Main
          "$ISABELLE_HOME/src/HOL/Library/Numeral_Type"
             (*"../../HOL-TestGen-2016/src/Testing"*)
                                                
begin 

section \<open>IMP state\<close>

text \<open>In IMP language the state is a partial map going from locations, \ie, variables names
      to their values. We assume that we can only have HOL integers for IMP variables.\<close>
(*TODO Yakoub:  adapt IMP arithmetic expressions to other C arithmetic  expressions, 
  \eg,IMP does not support int32, float, double, signed int, unsigned int etc.
  TASK Yakoub: add the above types on a top of Isabelle/HOL + add their algebraic rules etc.*)

type_synonym state = "string \<Rightarrow> int option"

section \<open>IMP expressions\<close>

subsection \<open>Arithmetic expressions\<close>
text \<open>In shallow embedding, since the arithmetic expressions already exist on top of HOL.
      Since arithmetic operations are overloaded on HOL, \ie, they can instantiated for different
      types, so   
      we don't need to explicitly model their syntax.\<close>

subsubsection\<open>Aexp configuration\<close>

text\<open>For each type of expressions supported by the language, we need a \emph{configuration}.
     A configuration is a partial function that takes an expression and a state and returns
     an evaluation of the expression in that state. For abbreviation purposes,
     we first create a type synonym for each expression's configuration,
     and then implement a semantics for the evaluation function based on that type.\<close>

type_synonym Aconfig = "int \<times> state \<Rightarrow> int option"

fun Aeval ::"Aconfig"
where 
"Aeval (n, \<sigma>) =   Some (id n)"

type_synonym Sconfig = "string \<times> state \<Rightarrow> int option"

fun Seval ::"Sconfig"
where "Seval (s, \<sigma>) =  \<sigma> s"

lemma sums_Eval:
  assumes 1:"Aeval (a0, \<sigma>) = Some n0"
  and     2:"Aeval (a1, \<sigma>) = Some n1"
  and     3: "n = n0 + n1"
  shows"Aeval (a0 + a1, \<sigma>) = Some n"
  using assms
  by auto

lemma minus_Eval:
  assumes 1:"Aeval (a0, \<sigma>) = Some n0"
  and     2:"Aeval (a1, \<sigma>) = Some n1"
  and     3: "n = n0 - n1"
  shows"Aeval (a0 - a1, \<sigma>) = Some n"
  using assms
  by auto

lemma multi_Eval:
  assumes 1:"Aeval (a0, \<sigma>) = Some n0"
  and     2:"Aeval (a1, \<sigma>) = Some n1"
  and     3: "n = n0 * n1"
  shows"Aeval (a0 * a1, \<sigma>) = Some n"
  using assms
  by auto

text\<open>All the rules above are used to simplify .\<close>
lemma "Aeval (a0, \<sigma>) = Some a0"
 by auto

subsection\<open>IMP boolean expressions\<close>

text\<open>Since we opt for shallow embedding, and since the type bool already exists on a top 
     of HOL we don't need to model the syntax for bool expressions.\<close>

subsubsection\<open>Bexp configuration\<close>

type_synonym  Bconfig = "bool \<times> state \<Rightarrow> bool"

fun Beval ::"Bconfig"
where 
 "Beval (True, \<sigma>) = True"
|"Beval (False, \<sigma>) = False"

lemma equ_Eval:
  assumes 1: "Aeval (a0, \<sigma>) = Some n0"
  and     2: "Aeval (a1, \<sigma>) = Some n1"
  and     3: "n0 = n1"
  shows      "Beval (a0 = a1, \<sigma>)"
  using assms
  by auto

lemma equ_EvalN:
  assumes 1: "Aeval (a0, \<sigma>) = Some n0"
  and     2: "Aeval (a1, \<sigma>) = Some n1"
  and     3: "n0 \<noteq> n1"
  shows      "\<not> Beval (a0 = a1, \<sigma>)"
  using assms
  by auto

lemma lessEqu_Eval:
  assumes 1: "Aeval (a0, \<sigma>) = Some n0"
  and     2: "Aeval (a1, \<sigma>) = Some n1"
  and     3: "n0 \<le> n1"
  shows      "Beval (a0 \<le> a1, \<sigma>)"
  using assms
  by auto

lemma lessEqu_EvalN:
  assumes 1: "Aeval (a0, \<sigma>) = Some n0"
  and     2: "Aeval (a1, \<sigma>) = Some n1"
  and     3: "\<not>(n0 \<le> n1)"
  shows      "\<not> Beval (a0 \<le> a1, \<sigma>)"
  using assms
  by auto

lemma not_Eval:
  assumes 1: "b"
  shows    "\<not> Beval (\<not>b, \<sigma>)"
  using assms
  by auto

lemma not_EvalN:
  assumes 1: "\<not>b"
  shows    "Beval (\<not>b, \<sigma>)"
  using assms
  by auto

lemma and_Eval:
  assumes 1: "Beval (b0, \<sigma>) = t0"
  and     2: "Beval (b1, \<sigma>) = t1"
  and     3: "t0"
  and     4: "t1"
  shows    "Beval (b0 \<and> b1, \<sigma>)"
  using assms
proof -
  have f1: "Beval (b0, \<sigma>)"
    by (metis "1" "3") 
  have f2: "Beval (b1, \<sigma>)"
    by (metis "2" "4") 
  have "Beval (b0 \<and> b1, \<sigma>) \<or> \<not> b0 \<or> \<not> b1"
    by fastforce
  then show ?thesis
    using f2 f1 by fastforce
qed

lemma and_EvalN1:
  assumes 1: "Beval (b0, \<sigma>) = t0"
  and     2: "Beval (b1, \<sigma>) = t1"
  and     3: "\<not>t0"
  shows    "\<not> Beval (b0 \<and> b1, \<sigma>)"
  using assms
  by (metis (full_types) Beval.simps(2))

lemma and_EvalN2:
  assumes 1: "Beval (b0, \<sigma>) = t0"
  and     2: "Beval (b1, \<sigma>) = t1"
  and     3: "t0"
  and     4: "\<not>t1"
  shows    "\<not>Beval (b0 \<and> b1, \<sigma>)"
  using assms
  by (metis (full_types) Beval.simps(2))

lemma or_Eval:
  assumes 1: "Beval (b0, \<sigma>) = t0"
  and     2: "Beval (b1, \<sigma>) = t1"
  and     3: "t0"
  and     4: "t1"
  shows    "Beval (b0 \<or> b1, \<sigma>)"
  using assms
proof -
  have "(b0 \<or> b1) \<or> Beval (b0 \<or> b1, \<sigma>)"
    using "2" "4" by auto 
  then show ?thesis
    using Beval.simps(1) by presburger
qed

lemma or_EvalN1:
  assumes 1: "Beval (b0, \<sigma>) = t0"
  and     2: "Beval (b1, \<sigma>) = t1"
  and     3: "t0"
  shows    "Beval (b0 \<or> b1, \<sigma>)"
  using assms
proof -
  have "(b0 \<or> b1) \<or> Beval (b0 \<or> b1, \<sigma>)"
    using "1" "3" by auto 
  then show ?thesis
    using Beval.simps(1) by presburger
qed

lemma or_EvalN2:
  assumes 1: "Beval (b0, \<sigma>) = t0"
  and     2: "Beval (b1, \<sigma>) = t1"
  and     3: "t1"
  shows    "Beval (b0 \<or> b1, \<sigma>)"
  using assms
proof -
  have "(b0 \<or> b1) \<or> Beval (b0 \<or> b1, \<sigma>)"
    using "2" "3" by auto 
  then show ?thesis
    using Beval.simps(1) by presburger
qed

lemma "Beval (b, \<sigma>) =  b"
  using id_apply 
  by fastforce
 
subsection\<open>IMP commands expressions\<close>
text\<open>Commands are expressions that take as inputs other IMP expressions and a state and returns
     a new state. The new updated state will contain new evaluations for the locations.
     The commands are the only way to give a semantics to a location.\<close>

datatype Com = skip |assign "string" "int"| "if" "bool" "Com" "Com" | 
               seq "Com" "Com" | while "bool" "Com"

subsection\<open>IMP Semantics\<close>

type_synonym Comconfig = "Com \<times> state \<Rightarrow> state"

fun unfold :: "nat \<times> Com \<Rightarrow> Com"
where
  uf_skip : "unfold(n, skip)     = skip"
| uf_ass  : "unfold(n, assign a  E)  = (assign a  E)"
| uf_If   : "unfold(n, Com.if b  c1  c2) = 
             Com.if b  (unfold(n, c1))  (unfold(n, c2))"
| uf_while: "unfold(n, while b  c ) = 
            (if 0 < n 
             then Com.if b  (seq (unfold(n,c)) (unfold(n- 1, while b  c )))  skip
             else while b  (unfold(0, c)) )"


inductive Ceval ::"Com \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" ("\<langle>_,_\<rangle> \<Rightarrow> _"  [20,98] 89)
where 
 Skip:"\<langle>skip, \<sigma> \<rangle> \<Rightarrow> \<sigma>"|
 Assign:"\<langle>assign LOC a, \<sigma> \<rangle> \<Rightarrow> \<sigma>(LOC := (Some a))"|
 IfT:"b \<Longrightarrow>  \<langle>c0 , \<sigma> \<rangle> \<Rightarrow> \<sigma>' \<Longrightarrow> \<langle>Com.if b c0 c1, \<sigma> \<rangle> \<Rightarrow> \<sigma>'"|
 IfF:"\<not> b \<Longrightarrow>  \<langle>c1 , \<sigma> \<rangle> \<Rightarrow> \<sigma>' \<Longrightarrow> \<langle>Com.if b c0 c1, \<sigma> \<rangle> \<Rightarrow> \<sigma>'"|
 WhileT:"b \<Longrightarrow>  \<langle>c , \<sigma> \<rangle> \<Rightarrow> \<sigma>'  \<Longrightarrow> \<langle>while b c, \<sigma>' \<rangle> \<Rightarrow> \<sigma>''\<Longrightarrow> \<langle>while b c, \<sigma> \<rangle> \<Rightarrow> \<sigma>''"|
 WhileF:"\<not> b \<Longrightarrow>  \<langle>while b c, \<sigma> \<rangle> \<Rightarrow> \<sigma>"|
 Seq:" \<langle>c0, \<sigma> \<rangle> \<Rightarrow> \<sigma>' \<Longrightarrow>  \<langle>c1, \<sigma>' \<rangle> \<Rightarrow> \<sigma>'' \<Longrightarrow>\<langle>seq c0 c1, \<sigma> \<rangle> \<Rightarrow> \<sigma>''"

inductive_cases Ceval_elim [cases set]:
"\<langle>skip, \<sigma> \<rangle> \<Rightarrow> \<sigma>'" "\<langle>assign LOC a, \<sigma> \<rangle> \<Rightarrow> \<sigma>'" "\<langle>Com.if b c0 c1, \<sigma> \<rangle> \<Rightarrow> \<sigma>'"
"\<langle>while b c, \<sigma> \<rangle> \<Rightarrow> \<sigma>'" "\<langle>seq c0 c1, \<sigma> \<rangle> \<Rightarrow> \<sigma>'"


lemma skip_Eval:"\<langle>skip, \<sigma> \<rangle> \<Rightarrow> \<sigma>"
  using Skip
  by simp

lemma assign_Eval:
  assumes 1:"Aeval (a, \<sigma>) = m"
  shows  "\<langle>assign LOC a, \<sigma> \<rangle> \<Rightarrow> \<sigma>(LOC :=  m)"
  using 1 Assign 
  by auto

lemma if_Eval1:
  assumes 1:"b"
  and     2:" \<langle>c0 , \<sigma> \<rangle> \<Rightarrow> \<sigma>'"
  shows  "\<langle>Com.if b c0 c1, \<sigma> \<rangle> \<Rightarrow> \<sigma>'"
  using 1 2 IfT
  by simp

lemma if_Eval2:
  assumes 1:"\<not>b"
  and     2:" \<langle>c1 , \<sigma> \<rangle> \<Rightarrow> \<sigma>'"
  shows  "\<langle>Com.if b c0 c1, \<sigma> \<rangle> \<Rightarrow> \<sigma>'"
  using 1 2 IfF
  by simp

lemma while_Eval1:
  assumes 1:"\<not>b"
  shows  "\<langle>while b c, \<sigma> \<rangle> \<Rightarrow> \<sigma>"
  using 1 WhileF
  by simp

lemma while_Eval2:
  assumes 1:"b"
  and     2:"\<langle>c , \<sigma> \<rangle> \<Rightarrow> \<sigma>'"
  and     3: "\<langle>while b c, \<sigma>' \<rangle> \<Rightarrow> \<sigma>''"
  shows  "\<langle>while b c, \<sigma>\<rangle> \<Rightarrow> \<sigma>''"
  using 1 2 3 WhileT
  by simp

section\<open>Conclusion\<close>
text\<open>Shallow embedding allows for the reuse of the existing HOL rules for the evaluation of expressions.
     In IMP, commands can update the state by updating location's values.
     The role of an operational semantics is to reduce commands to expressions and then reduce
     expressions to their evaluation.
     A syntax-directed specification with operational semantics allows for a powerful 
     expressions and powerful evaluation process\<close>


end