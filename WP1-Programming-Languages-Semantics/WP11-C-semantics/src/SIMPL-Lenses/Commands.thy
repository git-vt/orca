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


datatype (dead '\<sigma>,'f) xstate = isNorm: Normal '\<sigma> ("\<langle>(_)\<rangle>") | isAbr: Abrupt '\<sigma> ("\<langle>|(_)|\<rangle>")| 
                               isFault: Fault 'f ("\<langle>!(_)!\<rangle>")| isStuck: Stuck ("\<langle>\<infinity>\<rangle>")
text {*removing the transfer rules related to @{typ "('\<sigma>,'f)xstate"} from the transfer package.*}
declare xstate.ctr_transfer [transfer_rule del]
declare xstate.disc_transfer[transfer_rule del]
declare xstate.rec_transfer [transfer_rule del]
declare xstate.case_transfer[transfer_rule del]
declare xstate.rel_transfer [transfer_rule del]
declare xstate.map_transfer [transfer_rule del]
declare xstate.set_transfer [transfer_rule del]

subsection{*Wrapper*}
text {*In this section we introduce a generic wrapper for the different commands.
       The wrapper takes as an argument a command and execute it according to the abstract value
       of the state. This wrapper is used to execute a given program following the semantics
       of Simpl.*}

lift_definition Xstate_lift :: "'\<sigma> states \<Rightarrow> ('\<sigma>,'f) xstate states" ("\<lbrakk>(_)\<rbrakk>")is
  "\<lambda>C x\<sigma>. (case x\<sigma> of  \<langle>\<sigma>\<rangle> \<Rightarrow> \<langle>C \<sigma>\<rangle> | _ \<Rightarrow> x\<sigma> )".

lift_definition Xstate_drop :: "('\<sigma>,'f) xstate states  \<Rightarrow> '\<sigma> states" ("\<lbrakk>(_)\<rbrakk>")is
  "\<lambda>C \<sigma>. (case C \<langle>\<sigma>\<rangle> of  \<langle>\<sigma>'\<rangle> \<Rightarrow> \<sigma>' 

| _ \<Rightarrow> x\<sigma> )".oops

subsection{*SKIP*}

abbreviation "SKIP \<equiv> id"

subsection{*Assign*}

lift_definition Assign :: "('\<tau> , '\<sigma>) var \<Rightarrow> ('\<tau> ,'\<sigma>) expr \<Rightarrow> ('\<sigma>,'f) xstate states" ("_ :== _ " [80, 80] 70) is
  "\<lambda>var expr x\<sigma>. (case x\<sigma> of \<langle>\<sigma>\<rangle> \<Rightarrow> \<langle>subst_upd_var id var expr \<sigma>\<rangle> | _ \<Rightarrow> x\<sigma>)".

abbreviation Assign\<^sub>\<sigma> :: " '\<sigma> states \<Rightarrow> ('\<tau> , '\<sigma> ) var \<Rightarrow> ('\<tau> ,'\<sigma>) expr \<Rightarrow> '\<sigma> states" ("_ '(_ :==\<^sub>\<sigma> _') " [80,80, 80] 70) where
  "Assign\<^sub>\<sigma> \<sigma> Var Expr \<equiv> \<sigma>(Var \<mapsto>\<^sub>s (\<sigma> \<dagger> Expr))" (*It means transform the state by \<sigma> and then do the 
                                            assignment on the transformed state*)

subsection{*Conditional*}

lift_definition Cond :: "(bool ,'\<sigma>) expr \<Rightarrow> ('\<sigma>,'f) xstate states \<Rightarrow> ('\<sigma>,'f) xstate states \<Rightarrow> ('\<sigma>,'f) xstate states" ("IF (_)/ THEN (_) ELSE (_)"  70) is
  "\<lambda>bexp C1 C2 x\<sigma>. (case x\<sigma> of \<langle>\<sigma>\<rangle> \<Rightarrow> (if bexp \<sigma> then C1 \<langle>\<sigma>\<rangle> else C2 \<langle>\<sigma>\<rangle>) |  _ \<Rightarrow> x\<sigma>)".

subsection{*Sequential composition*}

lift_definition Seq :: "('\<sigma>,'f) xstate states \<Rightarrow> ('\<sigma>,'f) xstate states \<Rightarrow> ('\<sigma>,'f) xstate states"  ("_; _" [61, 60] 60) is
  "\<lambda> C1 C2 x\<sigma>. (case x\<sigma> of \<langle>\<sigma>\<rangle> \<Rightarrow> C2 (C1 x\<sigma>) |  _ \<Rightarrow> x\<sigma>)".

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

abbreviation While :: "('\<alpha> \<Rightarrow> bool) \<Rightarrow> '\<alpha> states \<Rightarrow> '\<alpha> states"  ("WHILE (_) DO /(_) OD"  70) where
  "While Bexp Body \<equiv> (RelInv(lfp(W Bexp (Rel Body))))" 

subsection{*Assert*}
text {*In order to annotate our programs we introduce a new statement to our language.
       The assert statement is a statement that do not change the state but assert an annotation
       to the program. *}

lift_definition Assert :: "'f \<Rightarrow> (bool , '\<sigma>) expr \<Rightarrow> ('\<sigma>,'f) xstate states \<Rightarrow> ('\<sigma>,'f) xstate states" ("ASSERT (_) /{_} /(_)"  70) is
  "\<lambda> f bexp C x\<sigma>. (case x\<sigma> of \<langle>\<sigma>\<rangle> \<Rightarrow> (if bexp \<sigma> then  C \<langle>\<sigma>\<rangle> else  Fault f)
                   | _\<Rightarrow> x\<sigma>)".
 
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

lift_definition esubst_lookupx :: "('\<sigma>,'f) xstate states \<Rightarrow>  ('\<tau> , '\<sigma>) var \<Rightarrow> ('\<tau>, '\<sigma>) expr" ("\<langle>_\<rangle>\<^sub>sx")
is "\<lambda> \<sigma> x s. get\<^bsub>x\<^esub> (\<sigma> s)" .
term "esubst_lookupx Normal R"
term "\<langle>tmp :== (VAR m) ; m :== ((VAR m) +\<^sub>e \<guillemotleft>1::int\<guillemotright>) ; R :== ((VAR tmp) +\<^sub>e VAR n)\<rangle>\<^sub>s "
term "(tmp :== (VAR m) ; m :== ((VAR m) +\<^sub>e \<guillemotleft>1::int\<guillemotright>) ; R :== ((VAR tmp) +\<^sub>e VAR n))  "
subsection {*Side effects*}
term "\<langle>R :== ((VAR tmp) +\<^sub>e VAR n)\<rangle>\<^sub>s "
lemma side_effect1:
  assumes "mwb_lens m" and "mwb_lens R" and "mwb_lens tmp" and 
  "m \<bowtie> R" and "m \<bowtie> n"  and "m \<bowtie> tmp" and "R \<bowtie> tmp" and "n \<bowtie> tmp" 
  shows "\<lceil>((VAR m) =\<^sub>e \<guillemotleft>2::int\<guillemotright> \<and>\<^sub>e (VAR n) =\<^sub>e \<guillemotleft>0::int\<guillemotright>  \<longrightarrow>\<^sub>e 
          \<langle>tmp :== (VAR m) ; m :== ((VAR m) +\<^sub>e \<guillemotleft>1::int\<guillemotright>) ; R :== ((VAR tmp) +\<^sub>e VAR n)\<rangle>\<^sub>s R =\<^sub>e \<guillemotleft>2::int\<guillemotright>)\<rceil>"
  using assms  unfolding subst_upd_var_def lens_indep_def  Xstate_lift_def
  by transfer auto

lemma side_effect2:  
  assumes "mwb_lens m" and "mwb_lens R" and "m \<bowtie> R" and "m \<bowtie> n" 
  shows"\<lceil>(VAR m) =\<^sub>e \<guillemotleft>2::int\<guillemotright> \<and>\<^sub>e (VAR n) =\<^sub>e \<guillemotleft>0::int\<guillemotright> \<longrightarrow>\<^sub>e 
        \<langle>[m \<mapsto>\<^sub>s ((VAR m) +\<^sub>e \<guillemotleft>1::int\<guillemotright>), R \<mapsto>\<^sub>s ((VAR m) +\<^sub>e VAR n)]\<rangle>\<^sub>s R=\<^sub>e \<guillemotleft>2::int\<guillemotright>\<rceil>"
  using assms unfolding subst_upd_var_def lens_indep_def
  by transfer auto

lemma side_effect3:
  assumes "mwb_lens m" and "mwb_lens R" and "mwb_lens tmp" and 
  "m \<bowtie> R" and "m \<bowtie> n"  and "m \<bowtie> tmp" and "R \<bowtie> tmp" and "n \<bowtie> tmp" 
  shows "\<lceil>((VAR m) =\<^sub>e \<guillemotleft>2::int\<guillemotright> \<and>\<^sub>e (VAR n) =\<^sub>e \<guillemotleft>0::int\<guillemotright> \<longrightarrow>\<^sub>e 
          \<langle>\<lbrakk>tmp :== (VAR m) ; m :== ((VAR m) +\<^sub>e \<guillemotleft>1::int\<guillemotright>) ; R :== ((VAR tmp) +\<^sub>e VAR n)\<rbrakk>\<rangle>\<^sub>s R =\<^sub>e \<guillemotleft>2::int\<guillemotright>)\<rceil>"
  using assms unfolding subst_upd_var_def lens_indep_def  Xstate_lift_def
  by transfer auto

notation (latex)
  SKIP  ("\<SKIP>") and
  Cond  ("\<IF> _ \<THEN> _ \<ELSE> _"  60) and
  While  ("\<WHILE> _ \<DO> _ \<OD>"  60)


end
