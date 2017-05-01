theory utp_fault_designs
imports   "../utp/utp" utp_designs
begin
subsection {*Sequential C-program alphabet*}

text {*In order to record the interaction of a sequential C program with its execution environment, 
       we extend the alphabet of UTP by four additional global state variables:
      \begin{itemize}   
       \<^item> wait: a boolean variable used to   
       \<^item> fault: a variable of type @{typ "'f option"} used to record a fault of a given guard is 
         not satisfied.
       \<^item> abrupt: a boolean variable used to
       \<^item> wait: a boolean variable used to
     \end{itemize}

*}
alphabet 'f cp_vars = des_vars +
  abrupt:: bool
  fault :: "'f option"
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
  lens_interp "\<lambda> (ok, r) . (ok, fault\<^sub>v r, abrupt\<^sub>v r, (*wait\<^sub>v r,*)more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation cp_vars_rel: lens_interp "\<lambda>(ok, ok', r, r').
  (ok, ok', fault\<^sub>v r, fault\<^sub>v r', abrupt\<^sub>v r, abrupt\<^sub>v r', (*wait\<^sub>v r, wait\<^sub>v r',*) more r, more r')"
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
  "$fault \<prec>\<^sub>v $fault\<acute>" "$abrupt \<prec>\<^sub>v $abrupt\<acute>"  "$ok \<prec>\<^sub>v $ok\<acute>"
  (*"$ok \<prec>\<^sub>v $wait\<acute>" "$ok \<prec>\<^sub>v $wait" "$ok\<acute> \<prec>\<^sub>v $wait\<acute>"  "$ok\<acute> \<prec>\<^sub>v $wait"*)
  "$ok \<prec>\<^sub>v $fault\<acute>" "$ok \<prec>\<^sub>v $fault" "$ok\<acute> \<prec>\<^sub>v $fault\<acute>"  "$ok\<acute> \<prec>\<^sub>v $fault"
  "$ok \<prec>\<^sub>v $abrupt\<acute>" "$ok \<prec>\<^sub>v $abrupt" "$ok\<acute> \<prec>\<^sub>v $abrupt\<acute>"  "$ok\<acute> \<prec>\<^sub>v $abrupt" 
  "$fault \<prec>\<^sub>v $abrupt\<acute>" "$fault \<prec>\<^sub>v $abrupt" "$fault\<acute> \<prec>\<^sub>v $abrupt\<acute>"  "$fault\<acute> \<prec>\<^sub>v $abrupt"
  (*"$fault \<prec>\<^sub>v $wait\<acute>" "$fault \<prec>\<^sub>v $wait" "$fault\<acute> \<prec>\<^sub>v $wait\<acute>"  "$fault\<acute> \<prec>\<^sub>v $wait"
  "$abrupt \<prec>\<^sub>v $wait\<acute>" "$abrupt \<prec>\<^sub>v $wait" "$abrupt\<acute> \<prec>\<^sub>v $wait\<acute>"  "$abrupt\<acute> \<prec>\<^sub>v $wait" *)
  by (simp_all add: var_name_ord_def)

abbreviation abrupt_f::"('f, '\<alpha>, '\<beta>) rel_cp \<Rightarrow> ('f, '\<alpha>, '\<beta>) rel_cp"
where "abrupt_f R \<equiv> R\<lbrakk>false/$abrupt\<rbrakk>"

abbreviation abrupt_t::"('f, '\<alpha>, '\<beta>) rel_cp \<Rightarrow> ('f, '\<alpha>, '\<beta>) rel_cp"
where "abrupt_t R \<equiv> R\<lbrakk>true/$abrupt\<rbrakk>"

syntax
  "_abrupt_f"  :: "logic \<Rightarrow> logic" ("_\<^sub>a\<^sub>f" [1000] 1000)
  "_abrupt_t"  :: "logic \<Rightarrow> logic" ("_\<^sub>a\<^sub>t" [1000] 1000)

translations
  "P \<^sub>a\<^sub>f" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST abrupt) false) P"
  "P \<^sub>a\<^sub>t" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST abrupt) true) P"

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

lemma unrest_wait_lift_rea [unrest]:
  "$abrupt \<sharp> \<lceil>P\<rceil>\<^sub>C" "$abrupt\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>C"
  by (pred_auto)+

lemma unrest_tr_lift_rea [unrest]:
  "$fault \<sharp> \<lceil>P\<rceil>\<^sub>C" "$fault\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>C"
  by (pred_auto)+

lemma seqr_wait_true [usubst]: "(P ;; Q) \<^sub>a\<^sub>t = (P \<^sub>a\<^sub>t ;; Q)"
  by (rel_auto)

lemma seqr_wait_false [usubst]: "(P ;; Q) \<^sub>a\<^sub>f = (P \<^sub>a\<^sub>f ;; Q)"
  by (rel_auto)

subsection {*exec semantics*}
text {*We introduce an execution semantics for the designs containing a specific values for 
       the auxiliary variables composing C-program alphabet. Under this execution function
       we consider only \emph{stable} input state ie., normal input state. 
       Since Simpl semantics is defined only for input normal state, we will have an 
       equivalent semantics as the one of Simpl language.*}

definition exec:: "('f,'\<alpha>,'\<beta>) rel_cp \<Rightarrow> ('f,'\<alpha>,'\<beta>) rel_cp" 
where [urel_defs]:"exec prog = (prog =\<^sub>u $ok) "
subsection{*Healthiness conditions*}

text {*Programs in abrupt state do not progress*}
definition C3a_def [upred_defs]: "C3a(P) = (P \<triangleleft> \<not>$abrupt \<triangleright> II)"

text {*Programs in fault state do not progress*}
definition C3b_def [upred_defs]: "C3b(P) = (P \<triangleleft> $fault =\<^sub>u \<guillemotleft>None\<guillemotright> \<triangleright> II)"

text {*Programs in fault or abrupt state do not progress*}
definition C3_def [upred_defs]: "C3(P) = (P \<triangleleft> \<not>$abrupt \<and> $fault =\<^sub>u \<guillemotleft>None\<guillemotright> \<triangleright> II)"

subsection{*Control flow statements*}

text{*We introduce the known control-flow statements for C. Our semantics is restricted
      to @{const exec}. In other words It assumes:
     \begin{itemize}   
       \<^item>  an execution starting from initial stable state ie,@{term "$ok"},   
       \<^item>  terminates a final state ie,@{term "$ok\<acute>"},
       \<^item>  the final state is a normal state ie,
          @{term "\<not>$abrupt"} and @{term "$fault =\<^sub>u \<guillemotleft>None\<guillemotright>"},
     \end{itemize}
    Thus it capture Simpl semantics.
    *}

definition skip_c :: "('f,'\<alpha>) hrel_cp" ("SKIP")
where [urel_defs]:"SKIP = C3(true \<turnstile> (\<not>$abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>II\<rceil>\<^sub>C))"

definition stuck_c :: "('f,'\<alpha>) hrel_cp" ("STUCK")
where [urel_defs]: "STUCK = (\<not>$ok\<acute> \<or>  $abrupt\<acute> \<or> $fault\<acute> \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright>)"

definition assigns_c :: "'\<alpha> usubst \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("\<langle>_\<rangle>\<^sub>C")
where [urel_defs]: "assigns_c \<sigma> = 
                    C3(\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<not>$abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>C))"

subsection{*assert and assume*}

definition rassume_c :: "'\<alpha> upred \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("_\<^sup>\<top>\<^sup>C" [999] 999) where
[urel_defs]: "rassume_c c = SKIP \<triangleleft> \<lceil>c\<rceil>\<^sub>C\<^sub>< \<triangleright> \<top>\<^sub>D"

definition rassert_c :: "'\<alpha> upred \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("_\<^sub>\<bottom>\<^sub>C" [999] 999) where
[urel_defs]: "rassert_c c = SKIP \<triangleleft> \<lceil>c\<rceil>\<^sub>C\<^sub>< \<triangleright> \<bottom>\<^sub>D"

subsection{*THROW*}

definition throw_c :: "('f,'\<alpha>) hrel_cp" ("THROW")
where [urel_defs]: "THROW = C3(true \<turnstile> ($abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>II\<rceil>\<^sub>C))"

subsection{*GUARD*}

abbreviation guard_c :: "'f \<Rightarrow> '\<alpha> cond \<Rightarrow>('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp" (*Is this correct!*) 
where "guard_c f b P \<equiv> C3(true \<turnstile> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>C\<^sub>< \<triangleright> (\<not>$abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>Some f\<guillemotright> \<and> \<lceil>II\<rceil>\<^sub>C)))"

subsection{*Exceptions*}

abbreviation catch_c :: "('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("TRY (_) CATCH /(_) END")
where "TRY P CATCH Q END \<equiv> 
       C3(true \<turnstile> (P ;; ((abrupt:== (\<not> &abrupt) ;;Q) \<triangleleft> $abrupt \<triangleright> II)))"

subsection{*Scoping*}

definition block_c  where
[urel_defs]:"block_c init body restore return = 
            Abs_uexpr (\<lambda>(s, s'). \<lbrakk>init ;; body ;; Abs_uexpr (\<lambda>(t, t').
                                                    \<lbrakk>(abrupt:== (\<not> &abrupt) ;;restore (s, s') (t, t');; THROW) \<triangleleft> $abrupt \<triangleright> II;; 
         restore (s, s') (t, t');; return(s, s') (t, t')\<rbrakk>\<^sub>e (t, t'))\<rbrakk>\<^sub>e (s, s'))" 
subsection{*Conditional*}

abbreviation If_c :: "'\<alpha> cond \<Rightarrow>('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("IF (_)/ THEN (_) ELSE (_)")where
  "If_c b P Q \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>C\<^sub>< \<triangleright> Q) "
subsection{*Loops*}

definition While :: "'\<alpha> cond \<Rightarrow> ('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("While\<^sup>\<top> _ do _ od") where
"While b C =  (\<nu> X \<bullet> (C ;; X) \<triangleleft> \<lceil>b\<rceil>\<^sub>C\<^sub>< \<triangleright> SKIP)"

abbreviation While_top :: "'\<alpha> cond \<Rightarrow> ('f,'\<alpha>) hrel_cp \<Rightarrow>  ('f,'\<alpha>) hrel_cp" ("WHILE _ DO _ OD") where
"WHILE b DO P OD \<equiv> While\<^sup>\<top> b do P od"

definition While_bot :: "'\<alpha> cond \<Rightarrow> ('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("While\<^sub>\<bottom> _ do _ od") where
"While\<^sub>\<bottom> b do P od = (\<mu> X \<bullet> (P ;; X) \<triangleleft> \<lceil>b\<rceil>\<^sub>C\<^sub>< \<triangleright> SKIP)"

declare While_def [urel_defs]

subsection{*While-loop inv*}
text {* While loops with invariant decoration *}

definition while_inv :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('f,'\<alpha>) hrel_cp \<Rightarrow> ('f,'\<alpha>) hrel_cp" ("WHILE _ invr _ DO _ OD" 70) where
"WHILE b invr p DO S OD = WHILE b DO S OD"

declare While_def [urel_defs]
declare while_inv_def [urel_defs]
declare While_bot_def [urel_defs]

(*What happen if we do not use healthiness conditions*)
lemma "(true \<turnstile> (\<not>$abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> II) ;; 
        true \<turnstile> ($abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> II)) =
       ( true \<turnstile> false)"
  by rel_auto
                   
lemma [simp]:"(SKIP ;; C3(true \<turnstile> P)) = C3(true \<turnstile> P)"
  by rel_auto

lemma "(SKIP ;; THROW) = THROW"
  by rel_auto

lemma "(THROW ;; SKIP) = THROW" 
  by rel_auto

lemma "(THROW ;; guard_c f b P) = THROW" 
  by rel_auto

lemma "((THROW ;; TRY P CATCH Q END)) = 
     THROW" 
  by rel_auto

lemma "`(THROW \<and> $ok \<and>$fault =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<not>$abrupt) \<Rightarrow> STUCK`"
  by rel_simp

lemma "`(guard_c f false P \<and> $ok \<and>$fault =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<not>$abrupt) \<Rightarrow> STUCK`"
  by rel_simp 

lemma "((true \<turnstile> (\<not>$abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> II)) =\<^sub>u $ok) =
        ($ok\<acute>\<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright>  \<and> \<not>$abrupt\<acute> \<and> II)"
  by rel_auto


(*lemma "(true ;; guard_c f b P) = true" by rel_auto
lemma "(SKIP ;;\<langle>s\<rangle>\<^sub>C) = \<langle>s\<rangle>\<^sub>C" by rel_auto
lemma "(\<langle>s\<rangle>\<^sub>C ;; SKIP) = \<langle>s\<rangle>\<^sub>C" by rel_auto

lemma "(SKIP =\<^sub>u ($ok \<and> \<not>$abrupt \<and> $fault =\<^sub>u \<guillemotleft>None\<guillemotright>)) = ($ok\<acute> \<and> \<not> $abrupt\<acute> \<and>  $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> II)"
  by rel_auto

lemma "II = ($\<Sigma>\<acute> =\<^sub>u $\<Sigma>)" by auto

lemma "(SKIP =\<^sub>u (\<not>$ok) ) = (\<not>$ok\<acute> \<or>  $abrupt\<acute> \<or> $fault\<acute> \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright> \<or> \<not>II)"
  by rel_auto

lemma "(SKIP) = ((\<not>$ok)\<or> (\<not>$abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> II))"
  by rel_auto


lemma "(H1 (II) =\<^sub>u $ok)= ($ok\<acute> \<and> II)" by rel_auto


*)
syntax
  "_assignmentc" :: "svid_list \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=" 55)

translations
  "_assignmentc xs vs" => "CONST assigns_c (_mk_usubst (CONST id) xs vs)"
  "x := v" <= "CONST assigns_c (CONST subst_upd (CONST id) (CONST svar x) v)"
  "x := v" <= "CONST assigns_c (CONST subst_upd (CONST id) x v)"
  "x,y := u,v" <= "CONST assigns_c (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"




end