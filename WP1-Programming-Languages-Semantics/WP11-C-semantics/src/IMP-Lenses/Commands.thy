chapter "Shallow IMP"
section{*Commands*}
text{*Instead of using a deep-embedding for the abstract syntax we use shallow embedding.
      To do so we need an explicit notion of substitution and variables.
      We use abbreviation in order that we do not hide the core theory behind
      another definition layer. Which makes it more suited for exploitation by simp, auto, etc*}

theory Commands 
imports "utp/utp_pred" "utp/utp_alphabet" "utp/utp_urel_setup"

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
"skip_r = assigns_r id"

subsection{*Assign*}

abbreviation assign_r :: "('t, '\<alpha>) uvar \<Rightarrow> ('t, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"  where 
  "assign_r v expr \<equiv> assigns_r [v \<mapsto>\<^sub>s expr]"

abbreviation assign_2_r ::
  "('t1, '\<alpha>) uvar \<Rightarrow> ('t2, '\<alpha>) uvar \<Rightarrow> ('t1, '\<alpha>) uexpr \<Rightarrow> ('t2, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel" where 
  "assign_2_r x y u v \<equiv> assigns_r [x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v]"

subsection{*Conditional*}

definition cond::"'\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" ("IF (_)/ THEN (_) ELSE (_)"  70)
where "(IF b THEN P ELSE Q) = (b \<and> P \<or> \<not> b \<and> Q)"
thm cond_def

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

(*This definition is inspired by HOL/IMP/denotational.thy
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

definition While' :: "('\<alpha> \<Rightarrow> bool) \<Rightarrow> '\<alpha> states \<Rightarrow> '\<alpha> states"  where
"While' b C =  (\<nu> X \<bullet> (\<lambda>\<sigma>. if b \<sigma> then X(C \<sigma>) else id \<sigma>))"
*)

definition While :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("WHILE (_) DO /(_) OD"  70) where
"While b C =  (\<nu> X \<bullet> (C ;; X) \<triangleleft> b \<triangleright>\<^sub>r SKIP)"

nonterminal
  svid_list and uexpr_list

syntax
  "_svid_unit"  :: "svid \<Rightarrow> svid_list" ("_")
  "_svid_list"  :: "svid \<Rightarrow> svid_list \<Rightarrow> svid_list" ("_,/ _")
  "_uexpr_unit" :: "('a, '\<alpha>) uexpr \<Rightarrow> uexpr_list" ("_" [40] 40)
  "_uexpr_list" :: "('a, '\<alpha>) uexpr \<Rightarrow> uexpr_list \<Rightarrow> uexpr_list" ("_,/ _" [40,40] 40)
  "_assignment" :: "svid_list \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrel"  ("_ :== _ " [80, 80] 70)
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
