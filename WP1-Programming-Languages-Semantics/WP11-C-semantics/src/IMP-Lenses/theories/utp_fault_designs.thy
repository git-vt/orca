theory utp_fault_designs
imports   "../hoare/algebraic_laws_abrupt"
begin
subsection {*Sequential C-program alphabet*}

text {*In order to record the interaction of a sequential C program with its execution environment, 
       we extend the alphabet of UTP by two additional global state variables:
      \begin{itemize}   
       \<^item> fault_tr: a variable of type @{typ "'f list"} used to record a fault of from a given guard.
       \<^item> fault: a boolean variable used to
     \end{itemize}
*}

alphabet 'f cp_flt = "'a cp_abr" +
  fault :: bool
  fault_tr :: "'f list"

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
  lens_interp "\<lambda> (ok, abrupt, abrupt_aux, r). 
                 (ok, abrupt, abrupt_aux, fault\<^sub>v r, fault_tr\<^sub>v r, more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation cp_flt_rel: 
  lens_interp "\<lambda>(ok, ok', abrupt, abrupt', abrupt_aux, abrupt_aux', r, r').
  (ok, ok', abrupt, abrupt', abrupt_aux, abrupt_aux', fault\<^sub>v r, fault\<^sub>v r', fault_tr\<^sub>v r, fault_tr\<^sub>v r', more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

subsubsection {*Type lifting*}

type_synonym ('f, 'a, '\<alpha>) cpf = "('a, ('f, '\<alpha>) cp_flt_scheme) cpa"
type_synonym ('f,'a,'\<alpha>,'\<beta>) rel_cpf  = "(('f,'a,'\<alpha>) cpf, ('f,'a,'\<beta>) cpf) rel"
type_synonym ('f,'a,'\<alpha>) hrel_cp  = "(('f,'a,'\<alpha>) cpf) hrel"

subsubsection {*Syntactic type setup*}

translations
  (type) "('f, 'a, '\<alpha>) cpf" <= (type) "('a, ('f, '\<alpha>) cp_flt_scheme) cpa"
  (type) "('f, 'a, '\<alpha>) cpf" <= (type) "('a, ('f, '\<alpha>) cp_flt_ext) cpa"
  (type) "('f,'a,'\<alpha>,'\<beta>) rel_cpf" <= (type) "(('f,'a,'\<alpha>) cpf, (_,_,'\<beta>) cpf) rel"

notation cp_flt_child_lens\<^sub>a ("\<Sigma>\<^sub>f\<^sub>l\<^sub>t")
notation cp_flt_child_lens ("\<Sigma>\<^sub>F\<^sub>L\<^sub>T")

syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>F\<^sub>L\<^sub>T")
  "_svid_st_a"  :: "svid" ("\<Sigma>\<^sub>f\<^sub>l\<^sub>t")
translations
  "_svid_st_alpha" => "CONST cp_flt_child_lens"
   "_svid_st_a" => "CONST cp_flt_child_lens\<^sub>a"

lemma cvars_ord [usubst]:
  "$ok \<prec>\<^sub>v $ok\<acute>" "$abrupt \<prec>\<^sub>v $abrupt\<acute>" "$abrupt_aux \<prec>\<^sub>v $abrupt_aux\<acute>" "$fault \<prec>\<^sub>v $fault\<acute>" "$fault_tr \<prec>\<^sub>v $fault_tr\<acute>" "$stuck \<prec>\<^sub>v $stuck\<acute>" 
  "$ok \<prec>\<^sub>v $abrupt\<acute>" "$ok \<prec>\<^sub>v $abrupt" "$ok\<acute> \<prec>\<^sub>v $abrupt\<acute>" "$ok\<acute> \<prec>\<^sub>v $abrupt"
  "$ok \<prec>\<^sub>v $abrupt_aux\<acute>" "$ok \<prec>\<^sub>v $abrupt_aux" "$ok\<acute> \<prec>\<^sub>v $abrupt_aux\<acute>" "$ok\<acute> \<prec>\<^sub>v $abrupt_aux" 
  "$ok \<prec>\<^sub>v $fault\<acute>" "$ok \<prec>\<^sub>v $fault" "$ok\<acute> \<prec>\<^sub>v $fault\<acute>" "$ok\<acute> \<prec>\<^sub>v $fault"
  "$ok \<prec>\<^sub>v $fault_tr\<acute>" "$ok \<prec>\<^sub>v $fault_tr" "$ok\<acute> \<prec>\<^sub>v $fault_tr\<acute>" "$ok\<acute> \<prec>\<^sub>v $fault_tr"
  "$ok \<prec>\<^sub>v $stuck\<acute>" "$ok \<prec>\<^sub>v $stuck" "$ok\<acute> \<prec>\<^sub>v $stuck\<acute>" "$ok\<acute> \<prec>\<^sub>v $stuck"
  "$abrupt \<prec>\<^sub>v $fault" "$abrupt \<prec>\<^sub>v $fault\<acute>" "$abrupt\<acute> \<prec>\<^sub>v $fault" "$abrupt\<acute> \<prec>\<^sub>v $fault\<acute>"
  "$abrupt \<prec>\<^sub>v $fault_tr" "$abrupt \<prec>\<^sub>v $fault_tr\<acute>" "$abrupt\<acute> \<prec>\<^sub>v $fault_tr" "$abrupt\<acute> \<prec>\<^sub>v $fault_tr\<acute>"
  "$abrupt \<prec>\<^sub>v $abrupt_aux\<acute>" "$abrupt \<prec>\<^sub>v $abrupt_aux" "$abrupt\<acute> \<prec>\<^sub>v $abrupt_aux\<acute>" "$abrupt\<acute> \<prec>\<^sub>v $abrupt_aux"  
  "$fault \<prec>\<^sub>v $abrupt_aux\<acute>" "$fault \<prec>\<^sub>v $abrupt_aux" "$fault\<acute> \<prec>\<^sub>v $abrupt_aux\<acute>" "$fault\<acute> \<prec>\<^sub>v $abrupt_aux"
  "$fault_tr \<prec>\<^sub>v $abrupt_aux\<acute>" "$fault_tr \<prec>\<^sub>v $abrupt_aux" "$fault_tr\<acute> \<prec>\<^sub>v $abrupt_aux\<acute>" "$fault_tr\<acute> \<prec>\<^sub>v $abrupt_aux"
  by (simp_all add: var_name_ord_def)

abbreviation fault_f::"('f,'a,'\<alpha>,'\<beta>) rel_cpf \<Rightarrow> ('f,'a,'\<alpha>,'\<beta>) rel_cpf"
where "fault_f R \<equiv> R\<lbrakk>false/$fault\<rbrakk>"

abbreviation fault_t::"('f,'a,'\<alpha>,'\<beta>) rel_cpf \<Rightarrow>('f,'a,'\<alpha>,'\<beta>) rel_cpf"
where "fault_t R \<equiv> R\<lbrakk>true/$fault\<rbrakk>"

syntax
  "_fault_f"  :: "logic \<Rightarrow> logic" ("_\<^sub>f\<^sub>f" [1000] 1000)
  "_fault_t"  :: "logic \<Rightarrow> logic" ("_\<^sub>f\<^sub>t" [1000] 1000)

translations
  "P \<^sub>f\<^sub>f" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST fault) false) P"
  "P \<^sub>f\<^sub>t" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST fault) true) P"

subsection {*UTP-Relations lift and drop*}

abbreviation lift_desr ("\<lceil>_\<rceil>\<^sub>F\<^sub>L\<^sub>T")
where "\<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>F\<^sub>L\<^sub>T \<times>\<^sub>L \<Sigma>\<^sub>F\<^sub>L\<^sub>T)"

abbreviation lift_pre_desr ("\<lceil>_\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub><")
where "\<lceil>p\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub>< \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub><\<rceil>\<^sub>F\<^sub>L\<^sub>T"

abbreviation lift_post_desr ("\<lceil>_\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub>>")
where "\<lceil>p\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub>> \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub>>\<rceil>\<^sub>F\<^sub>L\<^sub>T"

abbreviation drop_desr ("\<lfloor>_\<rfloor>\<^sub>F\<^sub>L\<^sub>T")
where "\<lfloor>P\<rfloor>\<^sub>F\<^sub>L\<^sub>T \<equiv> P \<restriction>\<^sub>p (\<Sigma>\<^sub>F\<^sub>L\<^sub>T \<times>\<^sub>L \<Sigma>\<^sub>F\<^sub>L\<^sub>T)"


subsection {* Reactive lemmas *}

lemma unrest_ok_lift_rea [unrest]:
  "$ok \<sharp> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T" "$ok\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T"
  by (pred_auto)+

lemma unrest_abrupt_lift_rea [unrest]:
  "$abrupt \<sharp> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T" "$abrupt\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T"
  by (pred_auto)+


lemma unrest_abrupt_aux_lift_rea [unrest]:
  "$abrupt_aux \<sharp> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T" "$abrupt_aux\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T"
  by (pred_auto)+


lemma unrest_fault_lift_rea [unrest]:
  "$fault \<sharp> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T" "$fault\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T"
  by (pred_auto)+

lemma unrest_stuck_lift_rea [unrest]:
  "$fault_tr \<sharp> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T" "$fault_tr\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T"
  by (pred_auto)+

lemma seqr_fault_true [usubst]: "(P ;; Q) \<^sub>f\<^sub>t = (P \<^sub>f\<^sub>t ;; Q)"
  by (rel_auto)

lemma seqr_fault_false [usubst]: "(P ;; Q) \<^sub>f\<^sub>f = (P \<^sub>f\<^sub>f ;; Q)"
  by (rel_auto)

subsection{*Healthiness conditions*}

text {*Programs in fault do not progress*}

definition C3_flt_def [upred_defs]: 
  "C3_flt(P) = (P \<triangleleft>\<not>$fault \<and> $fault_tr =\<^sub>u \<guillemotleft>[]\<guillemotright> \<triangleright> II)"

abbreviation
 "Simpl\<^sub>F\<^sub>L\<^sub>T P \<equiv> C3_flt(C3_abr(\<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> (P)))"

subsection{*Control flow statements*}

text{*We introduce the known control-flow statements for C. Our semantics is restricted
      to @{const "Simpl\<^sub>F\<^sub>L\<^sub>T"}. In other words It assumes:
     \begin{itemize}   
       \<^item>  an execution starting from initial stable state ie,@{term "$ok"},   
       \<^item>  terminates in a final state ie,@{term "$ok\<acute>"},
       \<^item>  the final state is a normal state ie,
          @{term "\<not>$abrupt"} and @{term "$fault_tr =\<^sub>u \<guillemotleft>[]\<guillemotright>"},
     \end{itemize}
    Thus it capture Simpl semantics.
    *}

definition skip_flt :: "('f,'a,'\<alpha>) hrel_cp" ("SKIP\<^sub>F\<^sub>L\<^sub>T")
where [urel_defs]:
  "SKIP\<^sub>F\<^sub>L\<^sub>T = Simpl\<^sub>F\<^sub>L\<^sub>T (\<not>$abrupt\<acute> \<and> \<not>$abrupt_aux\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<not>$fault\<acute> \<and> $fault_tr\<acute> =\<^sub>u \<guillemotleft>[]\<guillemotright> \<and> \<lceil>II\<rceil>\<^sub>F\<^sub>L\<^sub>T)"

definition assigns_flt :: "'\<alpha> usubst \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("\<langle>_\<rangle>\<^sub>C")
where [urel_defs]: 
  "assigns_c \<sigma> =  C3(\<lceil>true\<rceil>\<^sub>C \<turnstile> (\<not>$abrupt\<acute> \<and> \<not>$stuck\<acute> \<and> \<not>$fault\<acute> \<and> $fault_tr\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>C))"

subsection{*THROW*}

definition throw_c :: "('f,'\<alpha>) hrel_cp" ("THROW")
where [urel_defs]: 
  "THROW = Simpl ($abrupt\<acute> \<and> \<not>$stuck\<acute> \<and> \<not>$fault\<acute> \<and> $fault_tr\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>II\<rceil>\<^sub>C)"

subsection{*Conditional*}

abbreviation If_c :: "'\<alpha> cond \<Rightarrow>('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("bif (_)/ then (_) else (_) eif")where
  "If_c b P Q \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>C\<^sub>< \<triangleright> Q)"

subsection{*GUARD*}

abbreviation guard_c :: "'f \<Rightarrow> '\<alpha> cond \<Rightarrow> ('f,'\<alpha>) hrel_cp" 
where "guard_c f b \<equiv>  
      (bif b then SKIP else (\<not>$abrupt\<acute> \<and> \<not>$stuck\<acute> \<and> $fault\<acute> \<and> $fault_tr\<acute> =\<^sub>u \<guillemotleft>Some f\<guillemotright> \<and> \<lceil>II\<rceil>\<^sub>C) eif)"

subsection{*assert and assume*}

definition rassume_c :: "'\<alpha> upred \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("_\<^sup>\<top>\<^sup>C" [999] 999) where
[urel_defs]: "rassume_c c = (bif c then SKIP else \<top>\<^sub>D eif)"

definition rassert_c :: "'\<alpha> upred \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("_\<^sub>\<bottom>\<^sub>C" [999] 999) where
[urel_defs]: "rassert_c c = (bif c then SKIP else \<bottom>\<^sub>D eif)"

subsection{*Exceptions*}

abbreviation catch_c :: "('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("try (_) catch /(_) end")
where "try P catch Q end \<equiv> (P ;; ((abrupt:== (\<not> &abrupt) ;;Q) \<triangleleft> $abrupt \<triangleright> II))"

subsection{*Scoping*}

definition block_c ("bob INIT (_) BODY /(_) RESTORE /(_) RETURN/(_) eob") where
[urel_defs]:
  "bob INIT init BODY body RESTORE restore RETURN return eob= 
    (Abs_uexpr (\<lambda>(s, s'). 
     \<lbrakk>init ;; body ;; Abs_uexpr (\<lambda>(t, t').
                       \<lbrakk>(abrupt:== (\<not> &abrupt) ;;restore (s, s') (t, t');; THROW) \<triangleleft> $abrupt \<triangleright> II;; 
         restore (s, s') (t, t');; return(s, s') (t, t')\<rbrakk>\<^sub>e (t, t'))\<rbrakk>\<^sub>e (s, s')))" 

subsection{*Loops*}
purge_notation while ("while\<^sup>\<top> _ do _ od")

definition While :: "'\<alpha> cond \<Rightarrow> ('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("while\<^sup>\<top> _ do _ od") where
"While b C = (\<nu> X \<bullet> bif b then (C ;; X) else SKIP eif)"

purge_notation while_top ("while _ do _ od")

abbreviation While_top :: "'\<alpha> cond \<Rightarrow> ('f,'\<alpha>) hrel_cp \<Rightarrow>  ('f,'\<alpha>) hrel_cp" ("while _ do _ od") where
"while b do P od \<equiv> while\<^sup>\<top> b do P od"

purge_notation while_bot ("while\<^sub>\<bottom> _ do _ od")

definition While_bot :: "'\<alpha> cond \<Rightarrow> ('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("while\<^sub>\<bottom> _ do _ od") where
"while\<^sub>\<bottom> b do P od =  (\<mu> X \<bullet> bif b then (P ;; X) else SKIP eif)"

subsection{*While-loop inv*}
text {* While loops with invariant decoration *}

purge_notation while_inv ("while _ invr _ do _ od" 70)

definition While_inv :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("while _ invr _ do _ od" 70) where
"while b invr p do S od = while b do S od"

declare While_def [urel_defs]
declare While_inv_def [urel_defs]
declare While_bot_def [urel_defs]


syntax
  "_assignmentc" :: "svid_list \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr "\<Midarrow>" 55)

translations
  "_assignmentc xs vs" => "CONST assigns_c (_mk_usubst (CONST id) xs vs)"
  "x \<Midarrow> v" <= "CONST assigns_c (CONST subst_upd (CONST id) (CONST svar x) v)"
  "x \<Midarrow> v" <= "CONST assigns_c (CONST subst_upd (CONST id) x v)"
  "x,y \<Midarrow> u,v" <= "CONST assigns_c (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"

end