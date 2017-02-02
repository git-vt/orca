
section {*expressions*}

theory Expressions imports Lenses "~~/src/Tools/Adhoc_Overloading" 

begin

text{*In this setting the state-space is represented by the 
      type @{text "\<alpha>"}, and expressions by the type @{text "\<tau>"}*}
type_synonym ('\<tau> , '\<alpha> ) var = "('\<tau> \<Longrightarrow> '\<alpha>)"         
type_synonym  ('\<tau> ,'\<alpha>) expr  =  "'\<alpha>  \<Rightarrow> '\<tau>" 



  -- "arithmetic and boolean expressions are not modelled explicitly here,"

text {*Lifting vars to expr*}
lift_definition imp_var :: "('\<tau>, '\<alpha>) var \<Rightarrow> ('\<tau>, '\<alpha>) expr" ("VAR _") is 
  lens_get .


text {*Lifting HOL constant functions to expr*}
lift_definition Const :: "'t \<Rightarrow> ('t, '\<alpha>) expr" ("\<guillemotleft>_\<guillemotright>") is 
  "\<lambda> v b. v" .

lift_definition uop :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('b, '\<alpha>) expr"
  is "\<lambda> f e b. f (e b)" .

lift_definition bop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('b, '\<alpha>) expr \<Rightarrow> ('c, '\<alpha>) expr"
  is "\<lambda> f u v b. f (u b) (v b)" .

lift_definition trop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a, '\<alpha>) expr \<Rightarrow> ('b, '\<alpha>) expr \<Rightarrow> ('c, '\<alpha>) expr \<Rightarrow> ('d, '\<alpha>) expr"
  is "\<lambda> f u v w b. f (u b) (v b) (w b)" .

lift_definition qtop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 
   ('a, '\<alpha>) expr \<Rightarrow> ('b, '\<alpha>) expr \<Rightarrow> ('c, '\<alpha>) expr \<Rightarrow> ('d, '\<alpha>) expr \<Rightarrow>
   ('e, '\<alpha>) expr"
  is "\<lambda> f u v w x b. f (u b) (v b) (w b) (x b)" .


end
