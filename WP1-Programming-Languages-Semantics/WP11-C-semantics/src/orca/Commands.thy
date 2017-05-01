chapter "Shallow IMP"
section{*Commands*}
text{*Instead of using a deep-embedding for the abstract syntax we use shallow embedding.
      To do so we need an explicit notion of substitution and variables.
      We use abbreviation in order that we do not hide the core theory behind
      another definition layer. Which makes it more suited for exploitation by simp, auto, etc*}

theory Commands 
imports "utp/utp_designs"

begin


type_synonym '\<alpha> cond      = "'\<alpha> upred"
type_synonym ('\<alpha>, '\<beta>) rel = "('\<alpha> \<times> '\<beta>) upred"
type_synonym '\<alpha> hrel      = "('\<alpha> \<times> '\<alpha>) upred"

translations
  (type) "('\<alpha>, '\<beta>) rel" <= (type) "('\<alpha> \<times> '\<beta>) upred"

subsection{*SKIP*}
lift_definition assigns_r :: "'\<alpha> usubst \<Rightarrow> '\<alpha> hrel" ("\<langle>_\<rangle>\<^sub>a")
  is "\<lambda> \<sigma> (A, A'). A' = \<sigma>(A)" .

definition skip_r :: "'\<alpha> hrel"("SKIP") where
[urel_defs]:"skip_r = assigns_r id"

subsection{*Assign*}

abbreviation assign_r :: "('t, '\<alpha>) uvar \<Rightarrow> ('t, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"  where 
  "assign_r v expr \<equiv> assigns_r [v \<mapsto>\<^sub>s expr]"

abbreviation assign_2_r ::
  "('t1, '\<alpha>) uvar \<Rightarrow> ('t2, '\<alpha>) uvar \<Rightarrow> ('t1, '\<alpha>) uexpr \<Rightarrow> ('t2, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel" where 
  "assign_2_r x y u v \<equiv> assigns_r [x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v]"

subsection{*Conditional*}

definition cond::"'\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" ("IF (_)/ THEN (_) ELSE (_)"  70)
where [urel_defs]:"(IF b THEN P ELSE Q) = ((b \<and> P) \<or> ((\<not> b) \<and> Q))"

abbreviation rcond::"('\<alpha>, '\<beta>) rel \<Rightarrow> '\<alpha> cond \<Rightarrow> ('\<alpha>, '\<beta>) rel \<Rightarrow> ('\<alpha>, '\<beta>) rel"
                                                          ("(3_ \<triangleleft> _ \<triangleright>\<^sub>r/ _)" [52,0,53] 52)
where "(P \<triangleleft> b \<triangleright>\<^sub>r Q) \<equiv> (IF \<lceil>b\<rceil>\<^sub>< THEN P ELSE Q)"

subsection{*Sequential composition*}

lift_definition seqr::"('\<alpha>, '\<beta>) rel \<Rightarrow> ('\<beta>, '\<gamma>) rel \<Rightarrow> ('\<alpha>, '\<gamma>) rel" (infixr ";;" 51) is
  "\<lambda> P Q r. r \<in> ({p. P p} O {q. Q q})" .

subsection{*While-loop*}
text{*In order to specify while loops we need a concept that refers to the result of the execution
      of body of the loop. We call the result of the execution of the body the next state space.
      Rel is a function that takes a substitution on a state and apply it on a given init
      state. The resulting state from the application is the next state.
      Now we need to reason on the next state space to see if we continue the execution of the body
      or we skip it.*}

definition While :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("WHILE (_) DO /(_) OD"  70) where
"While b C =  (\<nu> X \<bullet> (C ;; X) \<triangleleft> b \<triangleright>\<^sub>r SKIP)"

subsection{*While-loop inv*}
text {* While loops with invariant decoration *}

definition while_inv :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while _ invr _ do _ od" 70) where
"while b invr p do S od = WHILE b DO S OD"

subsection{*assert and assume*}

definition rassume :: "'\<alpha> upred \<Rightarrow> '\<alpha> hrel" ("_\<^sup>\<top>" [999] 999) where
[urel_defs]: "rassume c = SKIP \<triangleleft> c \<triangleright>\<^sub>r false"

definition rassert :: "'\<alpha> upred \<Rightarrow> '\<alpha> hrel" ("_\<^sub>\<bottom>" [999] 999) where
[urel_defs]: "rassert c = SKIP \<triangleleft> c \<triangleright>\<^sub>r true"

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

notation (latex)
  skip_r  ("\<SKIP>") and
  cond  ("\<IF> _ \<THEN> _ \<ELSE> _"  60) and
  While  ("\<WHILE> _ \<DO> _ \<OD>"  60)


end
