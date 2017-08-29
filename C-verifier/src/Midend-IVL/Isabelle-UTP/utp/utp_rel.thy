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

translations
  (type) "('\<alpha>, '\<beta>) rel" <= (type) "('\<alpha> \<times> '\<beta>) upred"

subsection{*SKIP*}


definition skip_ra :: "('\<beta>, '\<alpha>) lens \<Rightarrow>'\<alpha> hrel" where
[urel_defs]: "skip_ra v = ($v\<acute> =\<^sub>u $v)"

syntax
  "_skip_ra" :: "salpha \<Rightarrow> logic" ("II\<^bsub>_\<^esub>")

translations
  "_skip_ra v" == "CONST skip_ra v"

lift_definition assigns_r :: "'\<alpha> usubst \<Rightarrow> '\<alpha> hrel" ("\<langle>_\<rangle>\<^sub>a")
  is "\<lambda> \<sigma> (A, A'). A' = \<sigma>(A)" .

definition skip_r :: "'\<alpha> hrel" where
[urel_defs]:"skip_r = assigns_r id"

subsection{*Assign*}

definition assigns_ra :: "'\<alpha> usubst \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> '\<alpha> hrel" ("\<langle>_\<rangle>\<^bsub>_\<^esub>") where
"\<langle>\<sigma>\<rangle>\<^bsub>a\<^esub> = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> II\<^bsub>a\<^esub>)"

abbreviation assign_r :: "('t, '\<alpha>) uvar \<Rightarrow> ('t, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"  where 
  "assign_r v expr \<equiv> assigns_r [v \<mapsto>\<^sub>s expr]"

abbreviation assign_2_r ::
  "('t1, '\<alpha>) uvar \<Rightarrow> ('t2, '\<alpha>) uvar \<Rightarrow> ('t1, '\<alpha>) uexpr \<Rightarrow> ('t2, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel" where 
  "assign_2_r x y u v \<equiv> assigns_r [x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v]"

subsection{*Conditional*}

abbreviation rcond::"('\<alpha>, '\<beta>) rel \<Rightarrow> '\<alpha> cond \<Rightarrow> ('\<alpha>, '\<beta>) rel \<Rightarrow> ('\<alpha>, '\<beta>) rel"
                                                          ("(3_ \<triangleleft> _ \<triangleright>\<^sub>r/ _)" [52,0,53] 52)
where "(P \<triangleleft> b \<triangleright>\<^sub>r Q) \<equiv> (P \<triangleleft>\<lceil>b\<rceil>\<^sub>< \<triangleright> Q)"

subsection{*Sequential composition*}

lift_definition seqr::"('\<alpha>, '\<beta>) rel \<Rightarrow> ('\<beta>, '\<gamma>) rel \<Rightarrow> ('\<alpha>, '\<gamma>) rel"  is
  "\<lambda> P Q r. r \<in> ({p. P p} O {q. Q q})" .

lift_definition conv_r :: "('a, '\<alpha> \<times> '\<beta>) uexpr \<Rightarrow> ('a, '\<beta> \<times> '\<alpha>) uexpr" ("_\<^sup>-" [999] 999)
is "\<lambda> e (b1, b2). e (b2, b1)" .

subsection{*Syntax setup*}

nonterminal
  svid_list and uexpr_list

syntax
  "_svid_unit"  :: "svid \<Rightarrow> svid_list" ("_")
  "_svid_list"  :: "svid \<Rightarrow> svid_list \<Rightarrow> svid_list" ("_,/ _")
  "_uexpr_unit" :: "('a, '\<alpha>) uexpr \<Rightarrow> uexpr_list" ("_" [40] 40)
  "_uexpr_list" :: "('a, '\<alpha>) uexpr \<Rightarrow> uexpr_list \<Rightarrow> uexpr_list" ("_,/ _" [40,40] 40)
  "_assignment" :: "svid_list \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrel"  ("_ :== _ " [60, 60] 52)
  "_mk_usubst"  :: "svid_list \<Rightarrow> uexprs \<Rightarrow> '\<alpha> usubst"

translations
  "_mk_usubst \<sigma> (_svid_unit x) v" == "\<sigma>(&x \<mapsto>\<^sub>s v)"
  "_mk_usubst \<sigma> (_svid_list x xs) (_uexprs v vs)" == "(_mk_usubst (\<sigma>(&x \<mapsto>\<^sub>s v)) xs vs)"
  "_assignment xs vs" => "CONST assigns_r (_mk_usubst (CONST id) xs vs)"
  "x :== v" <= "CONST assigns_r (CONST subst_upd (CONST id) (CONST svar x) v)"
  "x :== v" <= "CONST assigns_r (CONST subst_upd (CONST id) x v)"
  "x,y :== u,v" <= "CONST assigns_r (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"

adhoc_overloading
  useq seqr and
  uskip skip_r

subsection{*While-loop*}
text{*In order to specify while loops we need a concept that refers to the result of the execution
      of body of the loop. We call the result of the execution of the body the next state space.
      Rel is a function that takes a substitution on a state and apply it on a given init
      state. The resulting state from the application is the next state.
      Now we need to reason on the next state space to see if we continue the execution of the body
      or we skip it.*}

term "(\<nu> X \<bullet> (C ;; X))"
definition while :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sup>\<top> _ do _ od") where
"while b C =  (\<nu> X \<bullet> (C ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)"

abbreviation while_top :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while _ do _ od") where
"while b do P od \<equiv> while\<^sup>\<top> b do P od"

definition while_bot :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sub>\<bottom> _ do _ od") where
"while\<^sub>\<bottom> b do P od = (\<mu> X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)"

declare while_def [urel_defs]

subsection{*While-loop inv*}
text {* While loops with invariant decoration *}

definition while_inv :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while _ invr _ do _ od" 70) where
"while b invr p do S od = while\<^sup>\<top> b do S od"

subsection{*assert and assume*}

definition rassume :: "'\<alpha> upred \<Rightarrow> '\<alpha> hrel" ("_\<^sup>\<top>" [999] 999) where
[urel_defs]: "rassume c = II \<triangleleft> c \<triangleright>\<^sub>r false"

definition rassert :: "'\<alpha> upred \<Rightarrow> '\<alpha> hrel" ("_\<^sub>\<bottom>" [999] 999) where
[urel_defs]: "rassert c = II \<triangleleft> c \<triangleright>\<^sub>r true"

subsection{*throw*} 
text{*To model exceptions we need to use the flag OK from UTP.
      It is a way to capture the termination or non termination of a program.*}

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


subsection {* Program values *}

abbreviation prog_val :: "'\<alpha> hrel \<Rightarrow> ('\<alpha> hrel, '\<alpha>) uexpr" ("\<lbrace>|_|\<rbrace>\<^sub>u")
where "\<lbrace>|P|\<rbrace>\<^sub>u \<equiv> \<guillemotleft>P\<guillemotright>"

lift_definition call :: "('\<alpha> hrel, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"
is "\<lambda> P b. P (fst b) b" .

lemma call_prog_val: "call \<lbrace>|P|\<rbrace>\<^sub>u = P"
  by (simp add: call_def urel_defs lit.rep_eq Rep_uexpr_inverse)

notation (latex)
  skip_r  ("\<SKIP>") and
  cond  ("\<IF> _ \<THEN> _ \<ELSE> _"  60) and
  while  ("\<WHILE> _ \<DO> _ \<OD>"  60)

subsection {*Props *}

text {* We describe some properties of relations *}

definition ufunctional :: "('a, 'b) rel \<Rightarrow> bool"
where "ufunctional R \<longleftrightarrow> II \<sqsubseteq> R\<^sup>- ;; R"

declare ufunctional_def [urel_defs]

definition uinj :: "('a, 'b) rel \<Rightarrow> bool"
where "uinj R \<longleftrightarrow> II \<sqsubseteq> R ;; R\<^sup>-"

declare uinj_def [urel_defs]

text {* A test is like a precondition, except that it identifies to the postcondition. It
        forms the basis for Kleene Algebra with Tests (KAT). *}

definition lift_test :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel" ("\<lceil>_\<rceil>\<^sub>t")
where "\<lceil>b\<rceil>\<^sub>t = (\<lceil>b\<rceil>\<^sub>< \<and> II)"

declare cond_def [urel_defs]
declare skip_r_def [urel_defs]

text {* We implement a poor man's version of alphabet restriction that hides a variable within a relation *}

definition rel_var_res :: "'\<alpha> hrel \<Rightarrow> ('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> hrel" (infix "\<restriction>\<^sub>\<alpha>" 80) where
"P \<restriction>\<^sub>\<alpha> x = (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P)"

declare rel_var_res_def [urel_defs]

-- {* Configuration for UTP tactics (see @{theory utp_tactics}). *}

update_uexpr_rep_eq_thms -- {* Reread @{text rep_eq} theorems. *}

lemma Rep_inverse[code]:"Rep_uexpr (Abs_uexpr x) = x" 
by rel_auto

end
