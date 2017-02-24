chapter "Shallow IMP"
section{*Commands*}
text{*Instead of using a deep-embedding for the abstract syntax we use shallow embedding.
      To do so we need an explicit notion of substitution and variables.
      We use abbreviation in order that we do not hide the core theory behind
      another definition layer. Which makes it more suited for exploitation by simp, auto, etc*}

theory Commands imports Substitution

begin

subsection{*SKIP*}

abbreviation "SKIP \<equiv> id" (* in other words Skip is the id substitution.. it means (id \<dagger> id)*)

subsection{*Assign*}

abbreviation Assign :: "('\<tau> , '\<alpha> ) var \<Rightarrow> ('\<tau> ,'\<alpha>) expr \<Rightarrow> '\<alpha> states" ("_ :== _ " [80, 80] 70) where
"Assign Var Expr \<equiv> (subst_upd_var id Var Expr)" (*in other words an assign is a substitution update
                                                 on the id substitution (subst_upd (id o id) Var (id \<dagger> Expr ) )*)

abbreviation Assign\<^sub>\<sigma> :: " '\<alpha> states \<Rightarrow> ('\<tau> , '\<alpha> ) var \<Rightarrow> ('\<tau> ,'\<alpha>) expr \<Rightarrow> '\<alpha> states" ("_ '(_ :==\<^sub>\<sigma> _') " [80,80, 80] 70) where
"Assign\<^sub>\<sigma> \<sigma> Var Expr \<equiv> \<sigma>(Var \<mapsto>\<^sub>s \<sigma> \<dagger> Expr)" (*It means transform the state by \<sigma> and then do the 
                                            assignment on the transformed state*)

subsection{*Conditional*}

abbreviation Cond :: "(bool ,'\<alpha>) expr \<Rightarrow>'\<alpha> states \<Rightarrow> '\<alpha> states \<Rightarrow> '\<alpha> states" ("IF (_)/ THEN (_) ELSE (_)"  70) where
"Cond Bexp C1 C2  \<equiv> (\<lambda> \<sigma>. if Bexp \<sigma> then C1 \<sigma> else C2 \<sigma>)" (*emm...*)

subsection{*Sequential composition*}

abbreviation Seq :: "'\<alpha> states \<Rightarrow> '\<alpha> states \<Rightarrow> '\<alpha> states"  ("_; _" [61, 60] 60) where
"Seq  C1 C2  \<equiv>  C2 o C1 " (*emm... it means (C2 o C1)*)

subsection{*While-loop*}
text{*In order to specify while loops we need a concept that refers to the result of the execution
      of body of the loop. We call the result of the execution of the body the next state space.
      Rel is a function that takes a substitution on a state and apply it on a given init
      state. The resulting state from the application is the next state.
      Now we need to reason on the next state space to see if we continue the execution of the body
      or we skip it.*}

(*This definition is inspired by HOL/IMP/denotational.thy*)
definition Rel :: "('\<alpha> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> rel"
where "Rel f = {(\<sigma>, \<sigma>'). (f \<sigma> = \<sigma>')}"

definition RelInv :: "'\<alpha> rel \<Rightarrow> ('\<alpha> \<Rightarrow> '\<alpha>) "
where "RelInv S = (\<lambda> \<sigma>. (SOME \<sigma>'. (\<sigma>, \<sigma>') \<in> S))"
definition is_total :: "'\<alpha> rel \<Rightarrow> bool"
where     "is_total R \<equiv> \<forall>\<sigma>. \<exists>\<sigma>'. (\<sigma>,\<sigma>') \<in> R"

lemma is_total_Rel [simp]:"is_total(Rel c)"
unfolding is_total_def Rel_def
by auto

lemma Fun2Rel_Rel2Fun_id: 
assumes det:"single_valued R" 
  and   is_tot: "is_total R" 
shows "(Rel \<circ> RelInv) R = R"
apply (simp add: comp_def Rel_def RelInv_def,auto)
apply (meson is_tot someI_ex is_total_def)
by (metis det single_valued_def some_equality)

definition W :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow>('\<sigma> \<times> '\<sigma>) set \<Rightarrow> (('\<sigma> \<times> '\<sigma>) set \<Rightarrow> ('\<sigma> \<times> '\<sigma>) set)" 
where     "W b cd = (\<lambda>cw. {(s,t). if b s then (s, t) \<in> cd O cw else s = t})"

definition While :: "('\<alpha> \<Rightarrow> bool) \<Rightarrow> '\<alpha> states \<Rightarrow> '\<alpha> states"  ("WHILE (_) DO /(_) OD"  70) where
"While Bexp Body \<equiv> (RelInv(lfp(W Bexp (Rel Body))))" (*emm...*)


notation (latex)
  SKIP  ("\<SKIP>") and
  Cond  ("\<IF> _ \<THEN> _ \<ELSE> _"  60) and
  While  ("\<WHILE> _ \<DO> _ \<OD>"  60)


end
