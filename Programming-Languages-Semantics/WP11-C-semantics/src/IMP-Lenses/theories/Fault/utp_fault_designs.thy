theory utp_fault_designs
imports  "../utp/utp" utp_designs "../hoare/Algebraic_Laws_aux"
begin

subsection {*Sequential C-program alphabet*}

text {*In order to record the interaction of a sequential C program with its execution environment, 
       we extend the alphabet of UTP by two additional global state variables:
      \begin{itemize}   
       \<^item> abrupt_aux: a variable of type @{typ "'a option"} used to record the reason of the abrupt.
         For example a reason for abrupt in a C program can be: break, continue, return.
       \<^item> abrupt: a boolean variable used to specify if the program is in an abrupt state or not.
     \end{itemize}

*}

alphabet  cp_flt = des_vars +
  fault:: bool

declare cp_flt.splits [alpha_splits]

subsubsection {*Alphabet proofs*}
text {*
  The two locale interpretations below are a technicality to improve automatic
  proof support via the predicate and relational tactics. This is to enable the
  (re-)interpretation of state spaces to remove any occurrences of lens types
  after the proof tactics @{method pred_simp} and @{method rel_simp}, or any
  of their derivatives have been applied. Eventually, it would be desirable to
  automate both interpretations as part of a custom outer command for defining
  alphabets.
*}

interpretation cp_flt:
  lens_interp "\<lambda> (ok, r) . (ok, fault\<^sub>v r, more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation cp_flt_rel: lens_interp 
  "\<lambda>(ok, ok', r, r'). (ok, ok', fault\<^sub>v r, fault\<^sub>v r', more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done


subsubsection {*Type lifting*}

type_synonym  ('\<alpha>) cpf = "('\<alpha>) cp_flt_scheme des"
type_synonym ('\<alpha>,'\<beta>) rel_cpf  = "(('\<alpha>) cpf, ('\<beta>) cpf) rel"
type_synonym ('\<alpha>) hrel_cpf  = "(('\<alpha>) cpf) hrel"

subsubsection {*Syntactic type setup*}

translations
  (type) "('\<alpha>) cpf" <= (type) " ('\<alpha>) cp_flt_scheme des"
  (type) "('\<alpha>) cpf" <= (type) " ('\<alpha>) cp_flt_ext des"
  (type) "('\<alpha>,'\<beta>) rel_cpf" <= (type) "(('\<alpha>) cpf, ('\<beta>) cpf) rel"

notation cp_flt_child_lens\<^sub>a ("\<Sigma>\<^sub>f\<^sub>l\<^sub>t")
notation cp_flt_child_lens ("\<Sigma>\<^sub>F\<^sub>L\<^sub>T")

syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>F\<^sub>L\<^sub>T")
  "_svid_st_a"  :: "svid" ("\<Sigma>\<^sub>f\<^sub>l\<^sub>t")
translations
  "_svid_st_alpha" => "CONST cp_flt_child_lens"
   "_svid_st_a" => "CONST cp_flt_child_lens\<^sub>a"

abbreviation fault_f::"('\<alpha>, '\<beta>) rel_cpf \<Rightarrow> ('\<alpha>, '\<beta>) rel_cpf"
where "fault_f R \<equiv> R\<lbrakk>false/$fault\<rbrakk>"

abbreviation fault_t::"('\<alpha>, '\<beta>) rel_cpf \<Rightarrow> ('\<alpha>, '\<beta>) rel_cpf"
where "fault_t R \<equiv> R\<lbrakk>true/$fault\<rbrakk>"

syntax
  "_abrupt_f"  :: "logic \<Rightarrow> logic" ("_\<^sub>f\<^sub>f" [1000] 1000)
  "_abrupt_t"  :: "logic \<Rightarrow> logic" ("_\<^sub>f\<^sub>t" [1000] 1000)
  "_top_abr" :: "logic" ("\<top>\<^sub>F\<^sub>L\<^sub>T")
  "_bot_abr" :: "logic" ("\<bottom>\<^sub>F\<^sub>L\<^sub>T")

translations
  "P \<^sub>f\<^sub>f" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST fault) false) P"
  "P \<^sub>f\<^sub>t" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST fault) true) P"
  "\<top>\<^sub>F\<^sub>L\<^sub>T" => "(CONST not_upred (CONST utp_expr.var (CONST ivar CONST ok)))"
  "\<bottom>\<^sub>F\<^sub>L\<^sub>T" => "true"

lemma "\<top>\<^sub>F\<^sub>L\<^sub>T = ((\<not> $ok))"
  by auto

subsection {*Substitution lift and drop*}

abbreviation lift_rel_usubst_cpa ("\<lceil>_\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T")
where "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T \<equiv> \<sigma> \<oplus>\<^sub>s (\<Sigma>\<^sub>F\<^sub>L\<^sub>T \<times>\<^sub>L \<Sigma>\<^sub>F\<^sub>L\<^sub>T)"

abbreviation lift_usubst_cpa ("\<lceil>_\<rceil>\<^sub>s\<^sub>F\<^sub>L\<^sub>T")
where "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>F\<^sub>L\<^sub>T \<equiv> \<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s\<rceil>\<^sub>S\<^sub>F\<^sub>L\<^sub>T"

abbreviation drop_cpa_rel_usubst ("\<lfloor>_\<rfloor>\<^sub>S\<^sub>F\<^sub>L\<^sub>T")
where "\<lfloor>\<sigma>\<rfloor>\<^sub>S\<^sub>F\<^sub>L\<^sub>T \<equiv> \<sigma> \<restriction>\<^sub>s (\<Sigma>\<^sub>F\<^sub>L\<^sub>T \<times>\<^sub>L \<Sigma>\<^sub>F\<^sub>L\<^sub>T)"

abbreviation drop_cpa_usubst ("\<lfloor>_\<rfloor>\<^sub>s\<^sub>F\<^sub>L\<^sub>T")
where "\<lfloor>\<sigma>\<rfloor>\<^sub>s\<^sub>F\<^sub>L\<^sub>T \<equiv> \<lfloor>\<lfloor>\<sigma>\<rfloor>\<^sub>S\<^sub>F\<^sub>L\<^sub>T\<rfloor>\<^sub>s"

subsection {*UTP-Relations lift and drop*}

abbreviation lift_rel_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>F\<^sub>L\<^sub>T")
where "\<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>F\<^sub>L\<^sub>T \<times>\<^sub>L \<Sigma>\<^sub>F\<^sub>L\<^sub>T)"

abbreviation lift_pre_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub><")
where "\<lceil>p\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub>< \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub><\<rceil>\<^sub>F\<^sub>L\<^sub>T"

abbreviation lift_post_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub>>")
where "\<lceil>p\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub>> \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub>>\<rceil>\<^sub>F\<^sub>L\<^sub>T"

abbreviation drop_cpa_rel_uexpr ("\<lfloor>_\<rfloor>\<^sub>F\<^sub>L\<^sub>T")
where "\<lfloor>P\<rfloor>\<^sub>F\<^sub>L\<^sub>T \<equiv> P \<restriction>\<^sub>p (\<Sigma>\<^sub>F\<^sub>L\<^sub>T \<times>\<^sub>L \<Sigma>\<^sub>F\<^sub>L\<^sub>T)"

abbreviation drop_cpa_pre_uexpr ("\<lfloor>_\<rfloor>\<^sub><\<^sub>F\<^sub>L\<^sub>T")
where "\<lfloor>P\<rfloor>\<^sub><\<^sub>F\<^sub>L\<^sub>T \<equiv> \<lfloor>\<lfloor>P\<rfloor>\<^sub>F\<^sub>L\<^sub>T\<rfloor>\<^sub><"

abbreviation drop_cpa_post_uexpr ("\<lfloor>_\<rfloor>\<^sub>>\<^sub>F\<^sub>L\<^sub>T")
where "\<lfloor>P\<rfloor>\<^sub>>\<^sub>F\<^sub>L\<^sub>T \<equiv> \<lfloor>\<lfloor>P\<rfloor>\<^sub>F\<^sub>L\<^sub>T\<rfloor>\<^sub>>"

subsection {* Reactive lemmas *}


subsection{*Healthiness conditions*}

text {*Programs in abrupt state do not progress*}
definition C3_flt_def [upred_defs]: 
  "C3_flt(P) = (P \<triangleleft> \<not>$fault \<triangleright> II)"

abbreviation
 "Simpl\<^sub>F\<^sub>L\<^sub>T P \<equiv> C3_flt(\<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> (P))"

subsection{*Control flow statements*}

text
{*
  We introduce the known control-flow statements for C. Our semantics is restricted
  to @{const C3_flt}. In other words It assumes:
  \begin{itemize}   
    \<^item>  If we start the execution of a program ie, @{term "$ok"}, from an initial stable state 
       ie, @{term "\<not>($fault)"},   
    \<^item>  the program can terminates and has a final state ie,@{term "$ok\<acute>"},
    \<^item>  the final state is a normal state if it terminates and the result of execution is 
       @{term "\<not>$fault"},
  \end{itemize}
  Thus it captures Simpl semantics.
*}

definition skip_flt :: "('\<alpha>) hrel_cpf" ("SKIP\<^sub>F\<^sub>L\<^sub>T")
where [urel_defs]: "SKIP\<^sub>F\<^sub>L\<^sub>T = Simpl\<^sub>F\<^sub>L\<^sub>T (\<not>$fault\<acute> \<and> \<lceil>II\<rceil>\<^sub>F\<^sub>L\<^sub>T)"

definition assigns_flt :: " '\<alpha> usubst \<Rightarrow> ('\<alpha>) hrel_cpf" ("\<langle>_\<rangle>\<^sub>F\<^sub>L\<^sub>T")
where [urel_defs]: "\<langle>\<sigma>\<rangle>\<^sub>F\<^sub>L\<^sub>T  = Simpl\<^sub>F\<^sub>L\<^sub>T (\<not>$fault\<acute> \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>F\<^sub>L\<^sub>T)"

subsection{*Conditional*}

abbreviation If_abr :: 
  "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_cpf \<Rightarrow> ('\<alpha>) hrel_cpf \<Rightarrow> ('\<alpha>) hrel_cpf" ("bif (_)/ then (_) else (_) eif")
where "bif b then P else Q eif \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub>< \<triangleright> Q)"

subsection{*assert and assume*}

definition rassume_abr :: "'\<alpha> upred \<Rightarrow> ('\<alpha>) hrel_cpf" ("_\<^sup>\<top>\<^sup>C" [999] 999) 
where [urel_defs]: "rassume_abr c = (bif c then SKIP\<^sub>F\<^sub>L\<^sub>T else \<top>\<^sub>F\<^sub>L\<^sub>T eif)"

definition rassert_abr :: "'\<alpha> upred \<Rightarrow> ('\<alpha>) hrel_cpf" ("_\<^sub>\<bottom>\<^sub>C" [999] 999) 
where [urel_defs]: "rassert_abr c = (bif c then SKIP\<^sub>F\<^sub>L\<^sub>T else \<bottom>\<^sub>F\<^sub>L\<^sub>T eif)"

subsection{*GUARD*}

abbreviation guard_c :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_cpf" 
where "guard_c b \<equiv>  
      (bif b then SKIP\<^sub>F\<^sub>L\<^sub>T else ((\<not>$fault)\<turnstile> ($fault\<acute> \<and> \<lceil>II\<rceil>\<^sub>F\<^sub>L\<^sub>T)) eif)"

subsection{*Scoping*}
text {*The feature block specifies scoping via code blocks in C. The following specification
       do not support cases where the case is in abrupt since abrupt state at this stage is not yet
       specified*}

definition block_flt ("bob INIT (_) BODY /(_) RESTORE /(_) RETURN/(_) eob") 
where [urel_defs]:
  "bob INIT init BODY body RESTORE restore RETURN return eob= 
    ( Abs_uexpr (\<lambda>(s, s'). 
             \<lbrakk>init ;; body ;; 
             Abs_uexpr (\<lambda>(t, t').\<lbrakk>restore (s, s') (t, t');; return(s, s') (t, t')\<rbrakk>\<^sub>e (t, t'))\<rbrakk>\<^sub>e (s, s')))" 

subsection{*Loops*}

purge_notation while ("while\<^sup>\<top> _ do _ od")

definition While :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_cpf \<Rightarrow> ('\<alpha>) hrel_cpf" ("while\<^sup>\<top> _ do _ od") 
where "While b C = (\<nu> X \<bullet> bif b then (C ;; X) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)"

purge_notation while_top ("while _ do _ od")

abbreviation While_top :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_cpf \<Rightarrow> ('\<alpha>) hrel_cpf" ("while _ do _ od") 
where "while b do P od \<equiv> while\<^sup>\<top> b do P od"

purge_notation while_bot ("while\<^sub>\<bottom> _ do _ od")

definition While_bot :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_cpf \<Rightarrow> ('\<alpha>) hrel_cpf" ("while\<^sub>\<bottom> _ do _ od") 
where "while\<^sub>\<bottom> b do P od =  (\<mu> X \<bullet> bif b then (P ;; X) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)"

subsection{*While-loop inv*}
text {*While loops with invariant decoration*}

purge_notation while_inv ("while _ invr _ do _ od" 70)

definition While_inv :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_cpf \<Rightarrow> ('\<alpha>) hrel_cpf" ("while _ invr _ do _ od" 70) 
where "while b invr p do S od = while b do S od"

declare While_def [urel_defs]
declare While_inv_def [urel_defs]
declare While_bot_def [urel_defs]

syntax
  "_assignmentabr" :: "svid_list \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr "\<Midarrow>" 55)

translations
  "_assignmentabr xs vs" => "CONST assigns_flt (_mk_usubst (CONST id) xs vs)"
  "x \<Midarrow> v" <= "CONST assigns_flt (CONST subst_upd (CONST id) (CONST svar x) v)"
  "x \<Midarrow> v" <= "CONST assigns_flt (CONST subst_upd (CONST id) x v)"
  "x,y \<Midarrow> u,v" <= "CONST assigns_flt (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"



end