chapter "Shallow IMP"
section{*Commands*}
text{*Instead of using a deep-embedding for the abstract syntax we use shallow embedding.
      To do so we need an explicit notion of substitution and variables.
      We use abbreviation in order that we do not hide the core theory behind
      another definition layer. Which makes it more suited for exploitation by simp, auto, etc*}

theory utp_rel 
imports "utp_pred" "utp_alphabet" "utp_urel_setup"

begin

type_synonym '\<alpha> cond      = "'\<alpha> upred"
type_synonym ('\<alpha>, '\<beta>) rel = "('\<alpha> \<times> '\<beta>) upred"
type_synonym '\<alpha> hrel      = "('\<alpha> \<times> '\<alpha>) upred"
type_synonym ('a, '\<alpha>) hexpr = "('a, '\<alpha> \<times> '\<alpha>) uexpr"

translations
  (type) "('\<alpha>, '\<beta>) rel" <= (type) "('\<alpha> \<times> '\<beta>) upred"
  
text {* We set up some overloaded constants for sequential composition and the identity in case
  we want to overload their definitions later. *}
  
consts
  useq     :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr ";;" 71)
  uassigns :: "'a usubst \<Rightarrow> 'b" ("\<langle>_\<rangle>\<^sub>a")
  uskip    :: "'a" ("II")
  

subsection{*Conditional*}

abbreviation rcond::"('\<alpha>, '\<beta>) rel \<Rightarrow> '\<alpha> cond \<Rightarrow> ('\<alpha>, '\<beta>) rel \<Rightarrow> ('\<alpha>, '\<beta>) rel"
                                                          ("(3_ \<triangleleft> _ \<triangleright>\<^sub>r/ _)" [52,0,53] 52)
where "(P \<triangleleft> b \<triangleright>\<^sub>r Q) \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>< \<triangleright> Q)"

subsection{*Sequential composition*}

lift_definition seqr::"('\<alpha>, '\<beta>) rel \<Rightarrow> ('\<beta>, '\<gamma>) rel \<Rightarrow> ('\<alpha>, '\<gamma>) rel"  is
  "\<lambda> P Q r. r \<in> ({p. P p} O {q. Q q})" .
    
 adhoc_overloading
  useq seqr
  
text {* We also set up a homogeneous sequential composition operator, and versions of @{term true}
  and @{term false} that are explicitly typed by a homogeneous alphabet. *}

abbreviation seqh :: "'\<alpha> hrel \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" (infixr ";;\<^sub>h" 71) where
"seqh P Q \<equiv> (P ;; Q)"  

lift_definition assigns_r :: "'\<alpha> usubst \<Rightarrow> '\<alpha> hrel"
  is "\<lambda> \<sigma> (A, A'). A' = \<sigma>(A)" .

adhoc_overloading
  uassigns assigns_r
 
subsection{*SKIP*}                                                     

definition skip_ra :: "('\<beta>, '\<alpha>) lens \<Rightarrow>'\<alpha> hrel" where
[urel_defs]: "skip_ra v = ($v\<acute> =\<^sub>u $v)"

syntax
  "_skip_ra" :: "salpha \<Rightarrow> logic" ("II\<^bsub>_\<^esub>")

translations
  "_skip_ra v" == "CONST skip_ra v"
  
definition skip_r :: "'\<alpha> hrel" where
[urel_defs]:"skip_r = assigns_r id"

adhoc_overloading
  uskip skip_r
  
subsection{*Assign*}

definition assigns_ra :: "'\<alpha> usubst \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> '\<alpha> hrel" ("\<langle>_\<rangle>\<^bsub>_\<^esub>") where
"\<langle>\<sigma>\<rangle>\<^bsub>a\<^esub> = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> II\<^bsub>a\<^esub>)"

abbreviation assign_r :: "('t \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"  where 
  "assign_r v expr \<equiv> assigns_r [v \<mapsto>\<^sub>s expr]"

  
abbreviation assign_2_r ::
  "('t1 \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t2 \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t1, '\<alpha>) uexpr \<Rightarrow> ('t2, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel" where 
  "assign_2_r x y u v \<equiv> assigns_r [x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v]"


text {* We set up iterated sequential composition which iterates an indexed predicate over the
  elements of a list. *}
  
definition seqr_iter :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b hrel) \<Rightarrow> 'b hrel" where
[urel_defs]: "seqr_iter xs P = foldr (\<lambda> i Q. P(i) ;; Q) xs II"    

abbreviation conv_r :: "('a, '\<alpha> \<times> '\<beta>) uexpr \<Rightarrow> ('a, '\<beta> \<times> '\<alpha>) uexpr" ("_\<^sup>-" [999] 999)
where "conv_r e \<equiv> e \<oplus>\<^sub>p swap\<^sub>L"
  


subsection{*While-loop*}
text{*In order to specify while loops we need a concept that refers to the result of the execution
      of body of the loop. We call the result of the execution of the body the next state space.
      Rel is a function that takes a substitution on a state and apply it on a given init
      state. The resulting state from the application is the next state.
      Now we need to reason on the next state space to see if we continue the execution of the body
      or we skip it.*}

definition while :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sup>\<top> _ do _ od") where
"while b C =  (\<nu> X \<bullet> (C ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)"

abbreviation while_top :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while _ do _ od") where
"while b do P od \<equiv> while\<^sup>\<top> b do P od"

definition while_bot :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sub>\<bottom> _ do _ od") where
"while\<^sub>\<bottom> b do P od = (\<mu> X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)"

declare while_def [urel_defs]

subsection{*While-loop inv*}
text {* While loops with invariant decoration *}

definition while_inv :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while _ invr _ do _ od" 71) where
"while b invr p do S od = while\<^sup>\<top> b do S od"

subsection{*assert and assume*}

definition rassume :: "'\<alpha> upred \<Rightarrow> '\<alpha> hrel" ("_\<^sup>\<top>" [999] 999) where
[urel_defs]: "rassume c = II \<triangleleft> c \<triangleright>\<^sub>r false"

definition rassert :: "'\<alpha> upred \<Rightarrow> '\<alpha> hrel" ("_\<^sub>\<bottom>" [999] 999) where
[urel_defs]: "rassert c = II \<triangleleft> c \<triangleright>\<^sub>r true"

text {* Homogeneous relations form a quantale. This allows us to import a large number of laws
        from Struth and Armstrong's Kleene Algebra theory~\cite{Armstrong2015}. *}

abbreviation truer :: "'\<alpha> hrel" ("true\<^sub>h") where
"truer \<equiv> true"

abbreviation falser :: "'\<alpha> hrel" ("false\<^sub>h") where
"falser \<equiv> false"

text {* We next describe frames and antiframes with the help of lenses. A frame states that $P$
  defines the behaviour of all variables not in $a$, and all those in $a$ remain the same. An
  antiframe describes the converse: all variables in $a$ are specified by $P$, and all other
  variables remain the same. For more information please see \cite{Morgan90a}.*}

definition frame :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "frame a P = (\<^bold>\<exists> st \<bullet> P\<lbrakk>\<guillemotleft>st\<guillemotright>/$\<Sigma>\<acute>\<rbrakk> \<and> $\<Sigma>\<acute> =\<^sub>u \<guillemotleft>st\<guillemotright> \<oplus> $\<Sigma> on &a)"

definition antiframe :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "antiframe a P = (\<^bold>\<exists> st \<bullet> P\<lbrakk>\<guillemotleft>st\<guillemotright>/$\<Sigma>\<acute>\<rbrakk> \<and> $\<Sigma>\<acute> =\<^sub>u $\<Sigma> \<oplus> \<guillemotleft>st\<guillemotright> on &a)"

text {* The nameset operator can be used to hide a portion of the after-state that lies outside
  the lens $a$. It can be useful to partition a relation's variables in order to conjoin it
  with another relation. *}

definition nameset :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "nameset a P = (P \<restriction>\<^sub>v {$\<Sigma>,$a\<acute>})" 

subsection{*block*}
text{*Block is used to model scoping. This feature can be used to introduce local variables and 
      to handle parameter passing in procedures. To model the block we need a feature to abstract
      over the state-space. This way we can  initialize the value of the variable when we jump inside the block
      and restore it when we exit the block. This feature is provided implicitly by the type_def
      used to model UTP expr. It is @{const Abs_uexpr}. The definition of block takes 4 parameters: 
     \begin{itemize}
       \<^item> initP: It is used to initialize the values of variables when we jump inside the block.
       \<^item> body: It contains the body of the block.
       \<^item> restore : a function used to restore the values of variables when we jump outside the block.
       \<^item> return : A function used to return a value if the block uses the traditional return 
                  statement.
     \end{itemize}
*}


definition block :: "('a, 'c) rel \<Rightarrow> ('c, 'd) rel  \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'd \<times> 'b \<Rightarrow> ('d, 'e) rel) \<Rightarrow> 
                     ('a \<times> 'b \<Rightarrow> 'd \<times> 'b \<Rightarrow> ('e, 'b) rel) \<Rightarrow> ('a, 'b) rel" where
[urel_defs]:"block initP body restore return = 
             Abs_uexpr (\<lambda>(s, s'). 
             \<lbrakk>initP ;; body ;; 
             Abs_uexpr (\<lambda>(t, t').\<lbrakk>restore (s, s') (t, t');; return(s, s') (t, t')\<rbrakk>\<^sub>e (t, t'))\<rbrakk>\<^sub>e (s, s'))" 




subsection {* Syntax Translations *}
   
syntax
  -- {* Alternative traditional conditional syntax *}
  "_utp_if" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>u (_)/ then (_)/ else (_))" [0, 0, 71] 71)
  -- {* Iterated sequential composition *}
  "_seqr_iter" :: "pttrn \<Rightarrow> 'a list \<Rightarrow> '\<sigma> hrel \<Rightarrow> '\<sigma> hrel" ("(3;; _ : _ \<bullet>/ _)" [0, 0, 10] 10)
  -- {* Single and multiple assignement *}
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrel"  ("'(_') :== '(_')")  
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrel"  (infixr ":==" 72)
  -- {* Indexed assignment *}
  "_assignment_upd" :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(_[_] :==/ _)" [73, 0, 0] 72)
  -- {* Substitution constructor *}
  "_mk_usubst"      :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> usubst"
  -- {* Alphabetised skip *}
  "_skip_ra"        :: "salpha \<Rightarrow> logic" ("II\<^bsub>_\<^esub>")
  -- {* Frame *}
  "_frame"          :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:\<lbrakk>_\<rbrakk>" [79,0] 80)
  -- {* Antiframe *}
  "_antiframe"      :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]" [99,0] 100)
  -- {* Nameset *}
  "_nameset"        :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("ns _ \<bullet> _" [0,999] 999)
  
translations
  "_utp_if b P Q" => "P \<triangleleft> b \<triangleright>\<^sub>r Q"
  ";; x : l \<bullet> P" \<rightleftharpoons> "(CONST seqr_iter) l (\<lambda>x. P)"
  "_mk_usubst \<sigma> (_svid_unit x) v" \<rightleftharpoons> "\<sigma>(&x \<mapsto>\<^sub>s v)"
  "_mk_usubst \<sigma> (_svid_list x xs) (_uexprs v vs)" \<rightleftharpoons> "(_mk_usubst (\<sigma>(&x \<mapsto>\<^sub>s v)) xs vs)"
  "_assignment xs vs" => "CONST uassigns (_mk_usubst (CONST id) xs vs)"
  "x :== v" <= "CONST uassigns (CONST subst_upd (CONST id) (CONST svar x) v)"
  "x :== v" <= "CONST uassigns (CONST subst_upd (CONST id) x v)"
  "x,y :== u,v" <= "CONST uassigns (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"
  -- {* Indexed assignment uses the overloaded collection update function \emph{uupd}. *}
  "x [k] :== v" => "x :== &x(k \<mapsto> v)\<^sub>u"
  "_skip_ra v" \<rightleftharpoons> "CONST skip_ra v"
  "_frame x P" => "CONST frame x P"
  "_frame (_salphaset (_salphamk x)) P" <= "CONST frame x P"
  "_antiframe x P" => "CONST antiframe x P"
  "_antiframe (_salphaset (_salphamk x)) P" <= "CONST antiframe x P"
  "_nameset x P" == "CONST nameset x P"

text {* The following code sets up pretty-printing for homogeneous relational expressions. We cannot 
  do this via the ``translations'' command as we only want the rule to apply when the input and output
  alphabet types are the same. The code has to deconstruct a @{typ "('a, '\<alpha>) uexpr"} type, determine 
  that it is relational (product alphabet), and then checks if the types \emph{alpha} and \emph{beta} 
  are the same. If they are, the type is printed as a \emph{hexpr}. Otherwise, we have no match. 
  We then set up a regular translation for the \emph{hrel} type that uses this. *}
  
print_translation {*
let
fun tr' ctx [ a
            , Const (@{type_syntax "prod"},_) $ alpha $ beta ] = 
  if (alpha = beta) 
    then Syntax.const @{type_syntax "hexpr"} $ a $ alpha
    else raise Match;
in [(@{type_syntax "uexpr"},tr')]
end
*}
  
translations
  (type) "'\<alpha> hrel" <= (type) "(bool, '\<alpha>) hexpr"
  
subsection {* Program values *}

abbreviation prog_val :: "'\<alpha> hrel \<Rightarrow> ('\<alpha> hrel, '\<alpha>) uexpr" ("\<lbrace>|_|\<rbrace>\<^sub>u")
where "\<lbrace>|P|\<rbrace>\<^sub>u \<equiv> \<guillemotleft>P\<guillemotright>"

lift_definition call :: "('\<alpha> hrel, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"
is "\<lambda> P b. P (fst b) b" .

lemma call_prog_val: "call \<lbrace>|P|\<rbrace>\<^sub>u = P"
  by (simp add: call_def urel_defs lit.rep_eq Rep_uexpr_inverse)

(*notation (latex)
  skip_r  ("\<SKIP>") and
  cond  ("\<IF> _ \<THEN> _ \<ELSE> _"  60) and
  while  ("\<WHILE> _ \<DO> _ \<OD>"  60)*)

subsection {*Props *}

text {* We describe some properties of relations, including functional and injective relations. *}

definition ufunctional :: "('a, 'b) rel \<Rightarrow> bool"
where [urel_defs]: "ufunctional R \<longleftrightarrow> II \<sqsubseteq> R\<^sup>- ;; R"

definition uinj :: "('a, 'b) rel \<Rightarrow> bool"
where [urel_defs]: "uinj R \<longleftrightarrow> II \<sqsubseteq> R ;; R\<^sup>-"

-- {* Configuration for UTP tactics (see @{theory utp_tactics}). *}

update_uexpr_rep_eq_thms -- {* Reread @{text rep_eq} theorems. *}
text {* A test is like a precondition, except that it identifies to the postcondition. It
        forms the basis for Kleene Algebra with Tests (KAT). *}

definition lift_test :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel" ("\<lceil>_\<rceil>\<^sub>t")
where "\<lceil>b\<rceil>\<^sub>t = (\<lceil>b\<rceil>\<^sub>< \<and> II)"

declare cond_def [urel_defs]
declare skip_r_def [urel_defs]

text {* We implement a poor man's version of alphabet restriction that hides a variable within a relation *}

definition rel_var_res :: "'\<alpha> hrel \<Rightarrow> ('a \<Longrightarrow> '\<alpha>)  \<Rightarrow> '\<alpha> hrel" (infix "\<restriction>\<^sub>\<alpha>" 80) where
[urel_defs]:"P \<restriction>\<^sub>\<alpha> x = (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P)"

lemma Rep_inverse[code]:"Rep_uexpr (Abs_uexpr x) = x" 
by rel_auto

subsection {* Relational alphabet extension *}

lift_definition rel_alpha_ext :: "'\<beta> hrel \<Rightarrow> ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel" (infix "\<oplus>\<^sub>R" 65)
is "\<lambda> P x (b1, b2). P (get\<^bsub>x\<^esub> b1, get\<^bsub>x\<^esub> b2) \<and> (\<forall> b. b1 \<oplus>\<^sub>L b on x = b2 \<oplus>\<^sub>L b on x)" .

lemma rel_alpha_ext_alt_def:
  assumes "vwb_lens y" "x +\<^sub>L y \<approx>\<^sub>L 1\<^sub>L" "x \<bowtie> y"
  shows "P \<oplus>\<^sub>R x = (P \<oplus>\<^sub>p (x \<times>\<^sub>L x) \<and> $y\<acute> =\<^sub>u $y)"
  using assms
  apply (rel_auto robust, simp_all add: lens_override_def)
  apply (metis lens_indep_get lens_indep_sym)
  apply (metis vwb_lens_def wb_lens.get_put wb_lens_def weak_lens.put_get)
done  
end
