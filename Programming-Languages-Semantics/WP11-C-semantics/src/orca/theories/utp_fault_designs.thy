theory utp_fault_designs
imports   "../utp/utp" utp_designs
begin
subsection {*Sequential C-program alphabet*}

text {*In order to record the interaction of a sequential C program with its execution environment, 
       we extend the alphabet of UTP by two additional global state variables:
      \begin{itemize}   
       \<^item> fault: a variable of type @{typ "'f option"} used to record a fault of a given guard is 
         not satisfied.
       \<^item> abrupt: a boolean variable used to
     \end{itemize}

*}

alphabet 'f cp_vars = des_vars +
  abrupt:: bool
  fault :: bool
  stuck :: bool
  fault_tr :: "'f option"
  
  (*wait :: bool*)

declare cp_vars.splits [alpha_splits]

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

interpretation cp_vars:
  lens_interp "\<lambda> (ok, r) . (ok, abrupt\<^sub>v r, fault\<^sub>v r, fault_tr\<^sub>v r, stuck\<^sub>v r, more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation cp_vars_rel: lens_interp "\<lambda>(ok, ok', r, r').
  (ok, ok', abrupt\<^sub>v r, abrupt\<^sub>v r', fault\<^sub>v r, fault\<^sub>v r', fault_tr\<^sub>v r, fault_tr\<^sub>v r', stuck\<^sub>v r, 
   stuck\<^sub>v r',more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done


subsubsection {*Type lifting*}

type_synonym ('f, '\<alpha>) cp = "('f, '\<alpha>) cp_vars_scheme des"
type_synonym ('f,'\<alpha>,'\<beta>) rel_cp  = "(('f,'\<alpha>) cp, ('f,'\<beta>) cp) rel"
type_synonym ('f,'\<alpha>) hrel_cp  = "(('f,'\<alpha>) cp) hrel"

subsubsection {*Syntactic type setup*}

translations
  (type) "('f,'\<alpha>) cp" <= (type) "('f, '\<alpha>) cp_vars_scheme des"
  (type) "('f,'\<alpha>) cp" <= (type) "('f, '\<alpha>) cp_vars_ext des"
  (type) "('f,'\<alpha>,'\<beta>) rel_cp" <= (type) "(('f,'\<alpha>) cp, (_,'\<beta>) cp) rel"

notation cp_vars_child_lens\<^sub>a ("\<Sigma>\<^sub>c")
notation cp_vars_child_lens ("\<Sigma>\<^sub>C")

syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>C")
  "_svid_st_a"  :: "svid" ("\<Sigma>\<^sub>c")
translations
  "_svid_st_alpha" => "CONST cp_vars_child_lens"
   "_svid_st_a" => "CONST cp_vars_child_lens\<^sub>a"

lemma cvars_ord [usubst]:
  "$ok \<prec>\<^sub>v $ok\<acute>" "$abrupt \<prec>\<^sub>v $abrupt\<acute>" "$fault \<prec>\<^sub>v $fault\<acute>" "$fault_tr \<prec>\<^sub>v $fault_tr\<acute>" "$stuck \<prec>\<^sub>v $stuck\<acute>" 
  "$ok \<prec>\<^sub>v $abrupt\<acute>" "$ok \<prec>\<^sub>v $abrupt" "$ok\<acute> \<prec>\<^sub>v $abrupt\<acute>" "$ok\<acute> \<prec>\<^sub>v $abrupt" 
  "$ok \<prec>\<^sub>v $fault\<acute>" "$ok \<prec>\<^sub>v $fault" "$ok\<acute> \<prec>\<^sub>v $fault\<acute>" "$ok\<acute> \<prec>\<^sub>v $fault"
  "$ok \<prec>\<^sub>v $fault_tr\<acute>" "$ok \<prec>\<^sub>v $fault_tr" "$ok\<acute> \<prec>\<^sub>v $fault_tr\<acute>" "$ok\<acute> \<prec>\<^sub>v $fault_tr"
  "$ok \<prec>\<^sub>v $stuck\<acute>" "$ok \<prec>\<^sub>v $stuck" "$ok\<acute> \<prec>\<^sub>v $stuck\<acute>" "$ok\<acute> \<prec>\<^sub>v $stuck"
  "$abrupt \<prec>\<^sub>v $fault" "$abrupt \<prec>\<^sub>v $fault\<acute>" "$abrupt\<acute> \<prec>\<^sub>v $fault" "$abrupt\<acute> \<prec>\<^sub>v $fault\<acute>"
  "$abrupt \<prec>\<^sub>v $fault_tr" "$abrupt \<prec>\<^sub>v $fault_tr\<acute>" "$abrupt\<acute> \<prec>\<^sub>v $fault_tr" "$abrupt\<acute> \<prec>\<^sub>v $fault_tr\<acute>"
  "$abrupt \<prec>\<^sub>v $stuck\<acute>" "$abrupt \<prec>\<^sub>v $stuck" "$abrupt\<acute> \<prec>\<^sub>v $stuck\<acute>" "$abrupt\<acute> \<prec>\<^sub>v $stuck"  
  "$fault \<prec>\<^sub>v $stuck\<acute>" "$fault \<prec>\<^sub>v $stuck" "$fault\<acute> \<prec>\<^sub>v $stuck\<acute>" "$fault\<acute> \<prec>\<^sub>v $stuck"
  "$fault_tr \<prec>\<^sub>v $stuck\<acute>" "$fault_tr \<prec>\<^sub>v $stuck" "$fault_tr\<acute> \<prec>\<^sub>v $stuck\<acute>" "$fault_tr\<acute> \<prec>\<^sub>v $stuck"
  by (simp_all add: var_name_ord_def)

abbreviation abrupt_f::"('f, '\<alpha>, '\<beta>) rel_cp \<Rightarrow> ('f, '\<alpha>, '\<beta>) rel_cp"
where "abrupt_f R \<equiv> R\<lbrakk>false/$abrupt\<rbrakk>"

abbreviation abrupt_t::"('f, '\<alpha>, '\<beta>) rel_cp \<Rightarrow> ('f, '\<alpha>, '\<beta>) rel_cp"
where "abrupt_t R \<equiv> R\<lbrakk>true/$abrupt\<rbrakk>"

abbreviation fault_f::"('f, '\<alpha>, '\<beta>) rel_cp \<Rightarrow> ('f, '\<alpha>, '\<beta>) rel_cp"
where "fault_f R \<equiv> R\<lbrakk>false/$fault\<rbrakk>"

abbreviation fault_t::"('f, '\<alpha>, '\<beta>) rel_cp \<Rightarrow> ('f, '\<alpha>, '\<beta>) rel_cp"
where "fault_t R \<equiv> R\<lbrakk>true/$fault\<rbrakk>"

abbreviation stuck_f::"('f, '\<alpha>, '\<beta>) rel_cp \<Rightarrow> ('f, '\<alpha>, '\<beta>) rel_cp"
where "stuck_f R \<equiv> R\<lbrakk>false/$stuck\<rbrakk>"

abbreviation stuck_t::"('f, '\<alpha>, '\<beta>) rel_cp \<Rightarrow> ('f, '\<alpha>, '\<beta>) rel_cp"
where "stuck_t R \<equiv> R\<lbrakk>true/$stuck\<rbrakk>"

syntax
  "_abrupt_f"  :: "logic \<Rightarrow> logic" ("_\<^sub>a\<^sub>f" [1000] 1000)
  "_abrupt_t"  :: "logic \<Rightarrow> logic" ("_\<^sub>a\<^sub>t" [1000] 1000)
  "_fault_f"  :: "logic \<Rightarrow> logic" ("_\<^sub>f\<^sub>f" [1000] 1000)
  "_fault_t"  :: "logic \<Rightarrow> logic" ("_\<^sub>f\<^sub>t" [1000] 1000)
  "_stuck_f"  :: "logic \<Rightarrow> logic" ("_\<^sub>s\<^sub>f" [1000] 1000)
  "_stuck_t"  :: "logic \<Rightarrow> logic" ("_\<^sub>s\<^sub>t" [1000] 1000)

translations
  "P \<^sub>a\<^sub>f" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST abrupt) false) P"
  "P \<^sub>a\<^sub>t" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST abrupt) true) P"
  "P \<^sub>f\<^sub>f" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST fault) false) P"
  "P \<^sub>f\<^sub>t" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST fault) true) P"
  "P \<^sub>s\<^sub>f" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST stuck) false) P"
  "P \<^sub>s\<^sub>t" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST stuck) true) P"

subsection {*UTP-Relations lift and drop*}

abbreviation lift_desr ("\<lceil>_\<rceil>\<^sub>C")
where "\<lceil>P\<rceil>\<^sub>C \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>C \<times>\<^sub>L \<Sigma>\<^sub>C)"

abbreviation lift_pre_desr ("\<lceil>_\<rceil>\<^sub>C\<^sub><")
where "\<lceil>p\<rceil>\<^sub>C\<^sub>< \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub><\<rceil>\<^sub>C"

abbreviation lift_post_desr ("\<lceil>_\<rceil>\<^sub>C\<^sub>>")
where "\<lceil>p\<rceil>\<^sub>C\<^sub>> \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub>>\<rceil>\<^sub>C"

abbreviation drop_desr ("\<lfloor>_\<rfloor>\<^sub>C")
where "\<lfloor>P\<rfloor>\<^sub>C \<equiv> P \<restriction>\<^sub>p (\<Sigma>\<^sub>C \<times>\<^sub>L \<Sigma>\<^sub>C)"


subsection {* Reactive lemmas *}

lemma unrest_ok_lift_rea [unrest]:
  "$ok \<sharp> \<lceil>P\<rceil>\<^sub>C" "$ok\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>C"
  by (pred_auto)+

lemma unrest_abrupt_lift_rea [unrest]:
  "$abrupt \<sharp> \<lceil>P\<rceil>\<^sub>C" "$abrupt\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>C"
  by (pred_auto)+

lemma unrest_fault_lift_rea [unrest]:
  "$fault \<sharp> \<lceil>P\<rceil>\<^sub>C" "$fault\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>C"
  by (pred_auto)+

lemma unrest_stuck_lift_rea [unrest]:
  "$stuck \<sharp> \<lceil>P\<rceil>\<^sub>C" "$stuck\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>C"
  by (pred_auto)+

lemma seqr_abrupt_true [usubst]: "(P ;; Q) \<^sub>a\<^sub>t = (P \<^sub>a\<^sub>t ;; Q)"
  by (rel_auto)

lemma seqr_abrupt_false [usubst]: "(P ;; Q) \<^sub>a\<^sub>f = (P \<^sub>a\<^sub>f ;; Q)"
  by (rel_auto)

lemma seqr_fault_true [usubst]: "(P ;; Q) \<^sub>f\<^sub>t = (P \<^sub>f\<^sub>t ;; Q)"
  by (rel_auto)

lemma seqr_fault_false [usubst]: "(P ;; Q) \<^sub>f\<^sub>f = (P \<^sub>f\<^sub>f ;; Q)"
  by (rel_auto)

lemma seqr_stuck_true [usubst]: "(P ;; Q) \<^sub>s\<^sub>t = (P \<^sub>s\<^sub>t ;; Q)"
  by (rel_auto)

lemma seqr_stuck_false [usubst]: "(P ;; Q) \<^sub>s\<^sub>f = (P \<^sub>s\<^sub>f ;; Q)"
  by (rel_auto)

subsection{*Healthiness conditions*}

text {*Programs in fault or abrupt or stuck state do not progress*}
definition C3_def [upred_defs]: 
  "C3(P) = (P \<triangleleft> \<not>$abrupt \<and> \<not>$fault \<and> \<not>$stuck \<and> $fault_tr =\<^sub>u \<guillemotleft>None\<guillemotright> \<triangleright> II)"

subsection{*Control flow statements*}

text{*We introduce the known control-flow statements for C. Our semantics is restricted
      to @{const C3}. In other words It assumes:
     \begin{itemize}   
       \<^item>  an execution starting from initial stable state ie,@{term "$ok"},   
       \<^item>  terminates a final state ie,@{term "$ok\<acute>"},
       \<^item>  the final state is a normal state ie,
          @{term "\<not>$abrupt"} and @{term "$fault_tr =\<^sub>u \<guillemotleft>None\<guillemotright>"},
     \end{itemize}
    Thus it capture Simpl semantics.
    *}

abbreviation
 "Simpl P \<equiv> C3(\<lceil>true\<rceil>\<^sub>C \<turnstile> (P))"

definition skip_c :: "('f,'\<alpha>) hrel_cp" ("SKIP")
where [urel_defs]:
  "SKIP = Simpl (\<not>$abrupt\<acute> \<and> \<not>$stuck\<acute> \<and> \<not>$fault\<acute> \<and> $fault_tr\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>II\<rceil>\<^sub>C)"

definition stuck_c :: "('f,'\<alpha>) hrel_cp" ("STUCK")
where [urel_defs]: "STUCK = C3($stuck\<acute>)"

definition assigns_c :: "'\<alpha> usubst \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("\<langle>_\<rangle>\<^sub>C")
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