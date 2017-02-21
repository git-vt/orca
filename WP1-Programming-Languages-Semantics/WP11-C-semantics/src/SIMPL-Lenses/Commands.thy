chapter "Shallow IMP"
section{*Commands*}
text{*Instead of using a deep-embedding for the abstract syntax we use shallow embedding.
      To do so we need an explicit notion of substitution and variables.
      We use abbreviation in order that we do not hide the core theory behind
      another definition layer. Which makes it more suitable for simp, auto, etc*}

theory Commands imports Substitution

begin

subsection {*Extended State*}
text {*Our goal is to extend the language IMP with new features. 
      To capture abstractly the semantics of the new features, we 
      extend the state space abstract values. The datatype @{text "('\<sigma>,'f) xstate"} 
      extend the state space by four abstract values:
     \begin{itemize}
       \<^item> Normal: A state value abstracting the initial state and also a result of a normal execution.
       \<^item> Abrupt: A state value abstracting abrupt termination of an execution, eg., and execution
                 of a command that raise an exception.
       \<^item> Fault : A state value abstracting a fault execution, eg., an execution of a command
                 that does not respect an assertion.
       \<^item> Stuck : A state value abstracting non-terminating executions.
     \end{itemize}
*}

datatype (dead '\<sigma>,'f) xstate = isNorm: Normal '\<sigma> | isAbr: Abrupt '\<sigma> | isFault: Fault 'f | isStuck: Stuck

subsection{*Wrapper*}
text {*In this section we introduce a generic wrapper for the different commands.
       The wrapper takes as an argument a command and execute it according to the abstract value
       of the state. This wrapper is used to execute a given program following the semantics
       of Simpl.*}

definition Xstate_lift :: "('\<sigma>,'f) xstate states \<Rightarrow> ('\<sigma>,'f) xstate states" where
  "Xstate_lift C = (\<lambda> x\<sigma>. case x\<sigma> of  Normal \<sigma> \<Rightarrow> C (Normal \<sigma>) | _ \<Rightarrow> x\<sigma> )"

subsection{*SKIP*}

abbreviation "SKIP \<equiv> id"

subsection{*Assign*}

abbreviation Assign :: "('\<tau> , '\<sigma> ) var \<Rightarrow> ('\<tau> ,'\<sigma>) expr \<Rightarrow> '\<sigma> states" ("_ :== _ " [80, 80] 70) where
  "Assign Var Expr \<equiv>   (subst_upd_var id Var Expr)"

abbreviation Assign\<^sub>\<sigma> :: " '\<sigma> states \<Rightarrow> ('\<tau> , '\<sigma> ) var \<Rightarrow> ('\<tau> ,'\<sigma>) expr \<Rightarrow> '\<sigma> states" ("_ '(_ :==\<^sub>\<sigma> _') " [80,80, 80] 70) where
  "Assign\<^sub>\<sigma> \<sigma> Var Expr \<equiv> \<sigma>(Var \<mapsto>\<^sub>s \<sigma> \<dagger> Expr)" (*It means transform the state by \<sigma> and then do the 
                                            assignment on the transformed state*)

subsection{*Conditional*}

abbreviation Cond :: "(bool , '\<sigma>) expr \<Rightarrow> '\<sigma> states \<Rightarrow> '\<sigma> states \<Rightarrow> '\<sigma> states" ("IF (_)/ THEN (_) ELSE (_)"  70) where
  "Cond Bexp C1 C2  \<equiv> (\<lambda> \<sigma>. if Bexp \<sigma> then C1 \<sigma> else C2 \<sigma>)" 

subsection{*Sequential composition*}

abbreviation Seq :: "'\<sigma> states \<Rightarrow> '\<sigma> states \<Rightarrow> '\<sigma> states"  ("_; _" [61, 60] 60) where
  "Seq  C1 C2 \<equiv> (C2 o C1)" 

subsection{*While-loop*}
text{*In order to specify while loops we need a concept that refers to the result of the execution
      of body of the loop. We call the result of the execution of the body the next state space.
      Rel is a function that takes a substitution on a state and apply it on a given init
      state. The resulting state from the application is the next state.
      Now we need to reason on the next state space to see if we continue the execution of the body
      or we skip it.*}

(*This definition is inspired by HOL/IMP/denotational.thy*)
definition Rel :: "('\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> '\<sigma> rel"
where "Rel f = {(\<sigma>, \<sigma>'). (f \<sigma> = \<sigma>')}"

definition RelInv :: "'\<sigma> rel \<Rightarrow> ('\<sigma> \<Rightarrow> '\<sigma>) "
where "RelInv S = (\<lambda> \<sigma>. (SOME \<sigma>'. (\<sigma>, \<sigma>') \<in> S))"

definition W :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow>('\<sigma> \<times> '\<sigma>) set \<Rightarrow> (('\<sigma> \<times> '\<sigma>) set \<Rightarrow> ('\<sigma> \<times> '\<sigma>) set)" 
where     "W b cd = (\<lambda>cw. {(s,t). if b s then (s, t) \<in> cd O cw else s = t})"

abbreviation While :: "(('\<sigma>,'f) xstate \<Rightarrow> bool) \<Rightarrow> ('\<sigma>,'f) xstate states \<Rightarrow> ('\<sigma>,'f) xstate states"  ("WHILE (_) DO /(_) OD"  70) where
  "While Bexp Body \<equiv> (RelInv(lfp(W Bexp (Rel Body))))"

subsection{*Assert*}
text {*In order to annotate our programs we introduce a new statement to our language.
       The assert statement is a statement that do not change the state but assert an annotation
       to the program. *}

abbreviation assert :: "'f \<Rightarrow> (bool ,('\<sigma>,'f) xstate) expr \<Rightarrow> ('\<sigma>,'f) xstate states \<Rightarrow> ('\<sigma>,'f) xstate states" ("Assert (_) /{_} /(_)"  70) where
  "Assert f {bexp} C \<equiv> (IF bexp THEN C ELSE (\<lambda>x\<sigma>. Fault f))" (*emm... This means that whenever the assertions is
                                                                False the execution of the program is stopped*)

subsection{*Catch*}
text {*Abrupt terminations are handled using the statement @{text try_catch}.*}

abbreviation Try_Catch :: "('\<sigma>,'f) xstate states \<Rightarrow> ('\<sigma>,'f) xstate states \<Rightarrow> ('\<sigma>,'f) xstate states" ("TRY (_) CATCH /(_) END"  70) where
  "TRY C1 CATCH C2 END \<equiv> 
   (\<lambda>x\<sigma>. case C1 x\<sigma> of Normal \<sigma> \<Rightarrow> Normal \<sigma> | Abrupt \<sigma> \<Rightarrow> C2 (Normal \<sigma>) | 
                       Fault f  \<Rightarrow> Fault f  | Stuck \<Rightarrow> Stuck)"

subsection{*Throw*}
text {*The throw statement is used to express abrupt terminations such as: continue, break, return.
       It transforms the state space form @{text Normal} to  @{text Abrupt}.*}

abbreviation Throw :: "('\<sigma>,'f) xstate states" ("THROW"  70) where
  "THROW \<equiv> (\<lambda>x\<sigma>. case x\<sigma> of Normal \<sigma> \<Rightarrow> Abrupt \<sigma> | _ \<Rightarrow> x\<sigma>)"

subsection{*Blocks*}
text {*The statement @{text Blocks} is used to implement scoping and code blocks.
       To do so we follow the LLVM apporach called stuck unwinding. 
       Each time we enter the block we initialize the variables with the values of the
       inner scope using @{text init}. We execute the @{text body}. 
       Each time we go out of the scope we restore the values of the outer scope using 
       @{text return}. If the function returns a result we use @{text c} to store the 
       returning result.*}

abbreviation Block :: "[('\<sigma>,'f) xstate states,('\<sigma>,'f) xstate states,
                        ('\<sigma>,'f) xstate\<Rightarrow>('\<sigma>,'f) xstate\<Rightarrow>('\<sigma>,'f) xstate,
                        ('\<sigma>,'f) xstate\<Rightarrow>('\<sigma>,'f) xstate\<Rightarrow>('\<sigma>,'f) xstate states]\<Rightarrow> ('\<sigma>,'f) xstate states" where
  "Block init body return c \<equiv> (\<lambda>\<sigma>. ((TRY init ; body CATCH return \<sigma> ; THROW END); 
                                     (\<lambda>\<sigma>'. (return \<sigma>; c \<sigma> \<sigma>') \<sigma>')) \<sigma>)"

subsection {*Side effects*}

lemma side_effect1:
  assumes "mwb_lens m" and "mwb_lens R" and "mwb_lens tmp" and 
  "m \<bowtie> R" and "m \<bowtie> n"  and "m \<bowtie> tmp" and "R \<bowtie> tmp" and "n \<bowtie> tmp"
  shows "\<lceil>(VAR m) =\<^sub>e \<guillemotleft>2::int\<guillemotright> \<and>\<^sub>e (VAR n) =\<^sub>e \<guillemotleft>0::int\<guillemotright> \<longrightarrow>\<^sub>e 
          \<langle>tmp :== (VAR m) ; m :== ((VAR m) +\<^sub>e \<guillemotleft>1::int\<guillemotright>) ; R :== ((VAR tmp) +\<^sub>e VAR n)\<rangle>\<^sub>s R =\<^sub>e \<guillemotleft>2::int\<guillemotright>\<rceil>"
  using assms unfolding subst_upd_var_def lens_indep_def
  by transfer auto

lemma side_effect2:  
  assumes "mwb_lens m" and "mwb_lens R" and "m \<bowtie> R" and "m \<bowtie> n" 
  shows"\<lceil>(VAR m) =\<^sub>e \<guillemotleft>2::int\<guillemotright> \<and>\<^sub>e (VAR n) =\<^sub>e \<guillemotleft>0::int\<guillemotright> \<longrightarrow>\<^sub>e 
        \<langle>[m \<mapsto>\<^sub>s ((VAR m) +\<^sub>e \<guillemotleft>1::int\<guillemotright>), R \<mapsto>\<^sub>s ((VAR m) +\<^sub>e VAR n)]\<rangle>\<^sub>s R=\<^sub>e \<guillemotleft>2::int\<guillemotright>\<rceil>"
  using assms unfolding subst_upd_var_def lens_indep_def
  by transfer auto

notation (latex)
  SKIP  ("\<SKIP>") and
  Cond  ("\<IF> _ \<THEN> _ \<ELSE> _"  60) and
  While  ("\<WHILE> _ \<DO> _ \<OD>"  60)


end
