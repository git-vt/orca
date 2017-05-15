theory utp_fault_designs
imports  utp_reactive
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

alphabet 'f cp_vars = "'t rp_vars" +
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
  lens_interp "\<lambda> (ok, wait, tr, r). 
  (ok, wait, tr, abrupt\<^sub>v r, fault\<^sub>v r, more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation cp_vars_rel: lens_interp "\<lambda>(ok, ok', wait, tr, wait', tr', r, r').
  (ok, ok', wait, wait', tr, tr', abrupt\<^sub>v r, abrupt\<^sub>v r', fault\<^sub>v r, fault\<^sub>v r', more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

subsubsection {*Type lifting*}

type_synonym ('t, 'f, '\<alpha>) cp = "('t, ('f, '\<alpha>) cp_vars_scheme) rp"
type_synonym ('t,'f,'\<alpha>,'\<beta>) rel_cp  = "(('t,'f,'\<alpha>) cp, ('t,'f,'\<beta>) cp) rel"
type_synonym ('t,'f,'\<alpha>) hrel_cp  = "(('t,'f,'\<alpha>) cp) hrel"

subsubsection {*Syntactic type setup*}

translations
  (type) "('t, 'f, '\<alpha>) cp" <= (type) "('t, ('f, '\<alpha>) cp_vars_scheme) rp_vars_scheme des"
  (type) "('t, 'f, '\<alpha>) cp" <= (type) "('t, ('f, '\<alpha>) cp_vars_scheme) rp_vars_ext des"
  (type) "('t, 'f,'\<alpha>,'\<beta>) rel_cp" <= (type) "(('t,'f,'\<alpha>) cp, (_,_,'\<beta>) cp) rel"

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
  "$ok \<prec>\<^sub>v $wait\<acute>" "$ok \<prec>\<^sub>v $wait" "$ok\<acute> \<prec>\<^sub>v $wait\<acute>"  "$ok\<acute> \<prec>\<^sub>v $wait"
  "$ok \<prec>\<^sub>v $fault\<acute>" "$ok \<prec>\<^sub>v $fault" "$ok\<acute> \<prec>\<^sub>v $fault\<acute>"  "$ok\<acute> \<prec>\<^sub>v $fault"
  "$ok \<prec>\<^sub>v $abrupt\<acute>" "$ok \<prec>\<^sub>v $abrupt" "$ok\<acute> \<prec>\<^sub>v $abrupt\<acute>"  "$ok\<acute> \<prec>\<^sub>v $abrupt" 
  "$fault \<prec>\<^sub>v $abrupt\<acute>" "$fault \<prec>\<^sub>v $abrupt" "$fault\<acute> \<prec>\<^sub>v $abrupt\<acute>"  "$fault\<acute> \<prec>\<^sub>v $abrupt"
  "$fault \<prec>\<^sub>v $wait\<acute>" "$fault \<prec>\<^sub>v $wait" "$fault\<acute> \<prec>\<^sub>v $wait\<acute>"  "$fault\<acute> \<prec>\<^sub>v $wait"
  "$abrupt \<prec>\<^sub>v $wait\<acute>" "$abrupt \<prec>\<^sub>v $wait" "$abrupt\<acute> \<prec>\<^sub>v $wait\<acute>"  "$abrupt\<acute> \<prec>\<^sub>v $wait"
  by (simp_all add: var_name_ord_def)

abbreviation abrupt_f::"('t::ordered_cancel_monoid_diff,'f, '\<alpha>, '\<beta>) rel_cp \<Rightarrow> 
                        ('t,'f, '\<alpha>, '\<beta>) rel_cp"
where "abrupt_f R \<equiv> R\<lbrakk>false/$abrupt\<rbrakk>"

abbreviation abrupt_t::"('t::ordered_cancel_monoid_diff,'f, '\<alpha>, '\<beta>) rel_cp \<Rightarrow> 
                        ('t,'f, '\<alpha>, '\<beta>) rel_cp"
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

subsection{*Healthiness conditions*}
text {*In UTP healthiness conditions is away to express invariant on the alphabet.
       The following healthiness condition express that programs in, wait, fault or 
       abrupt state do not progress.*}
definition C3_def [upred_defs]: "C3(P) = 
           (P \<triangleleft>  \<not>$wait \<and> \<not>$abrupt \<and> $fault =\<^sub>u \<guillemotleft>None\<guillemotright> \<triangleright> II )"

subsection {*exec semantics*}
text {*We introduce an execution semantics for the designs containing a specific values for 
       the auxiliary variables composing C-program alphabet. Under this execution function
       we consider only \emph{stable} initial state ie., normal initial state. 
       Since Simpl semantics is defined only for initial normal state, using this semantics
       will allow for an equivalent semantics as the one of Simpl language.*}

abbreviation
 "Simpl P \<equiv> C3(true \<turnstile> (P))"

subsection{*Control flow statements*}

text{*In the sequel we introduce the control-flow statements for C programming language.*}

definition skip_c :: "('t::ordered_cancel_monoid_diff,'f,'\<alpha>) hrel_cp" ("SKIP")
where [urel_defs]:"SKIP = Simpl ($tr\<acute> =\<^sub>u $tr \<and> \<not>$wait\<acute> \<and> \<not>$abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>II\<rceil>\<^sub>C)"

definition stuck_c :: "('t::ordered_cancel_monoid_diff,'f,'\<alpha>) hrel_cp" ("STUCK")
where [urel_defs]: "STUCK = (\<not>$ok\<acute> \<or> $wait\<acute> \<or> $abrupt\<acute> \<or> $fault\<acute> \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright>)"

definition assigns_c :: "'\<alpha> usubst \<Rightarrow> ('t::ordered_cancel_monoid_diff,'f,'\<alpha>) hrel_cp" ("\<langle>_\<rangle>\<^sub>C")
where [urel_defs]: "assigns_c \<sigma> = 
                    C3(\<lceil>true\<rceil>\<^sub>D \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not>$wait\<acute> \<and> \<not>$abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>C))"

subsection{*THROW*}

definition throw_c :: "('t::ordered_cancel_monoid_diff,'f,'\<alpha>) hrel_cp" ("THROW")
where [urel_defs]: "THROW = Simpl ($tr\<acute> =\<^sub>u $tr \<and> \<not>$wait\<acute> \<and> $abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>II\<rceil>\<^sub>C)"

subsection{*Conditional*}

abbreviation If_c::"'\<alpha> cond \<Rightarrow>('t::ordered_cancel_monoid_diff,'f,'\<alpha>) hrel_cp \<Rightarrow> ('t,'f,'\<alpha>) hrel_cp \<Rightarrow> 
                    ('t,'f,'\<alpha>) hrel_cp" ("bif (_)/ then (_) else (_) eif")where
  "If_c b P Q \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>C\<^sub>< \<triangleright> Q)"

subsection{*GUARD*}

abbreviation guard_c :: "'f \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t::ordered_cancel_monoid_diff,'f,'\<alpha>) hrel_cp"  
where "guard_c f b \<equiv> (bif b 
                        then SKIP 
                        else Simpl ($tr\<acute> =\<^sub>u $tr \<and> \<not>$wait\<acute> \<and> \<not>$abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>Some f\<guillemotright> \<and> \<lceil>II\<rceil>\<^sub>C) 
                      eif)"

subsection{*Synchronisation*}

abbreviation sync_c :: "'\<alpha> cond \<Rightarrow> ('t::ordered_cancel_monoid_diff,'f,'\<alpha>) hrel_cp"  
where "sync_c b \<equiv> (bif b 
                     then SKIP 
                     else Simpl ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<and> \<not>$abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>II\<rceil>\<^sub>C) 
                   eif)"

subsection{*assert and assume*}

definition rassume_c :: "'\<alpha> upred \<Rightarrow> ('t::ordered_cancel_monoid_diff,'f,'\<alpha>) hrel_cp" ("_\<^sup>\<top>\<^sup>C" [999] 999) where
[urel_defs]: "rassume_c c = (bif c then SKIP else \<top>\<^sub>D eif)"

definition rassert_c :: "'\<alpha> upred \<Rightarrow> ('t::ordered_cancel_monoid_diff,'f,'\<alpha>) hrel_cp" ("_\<^sub>\<bottom>\<^sub>C" [999] 999) where
[urel_defs]: "rassert_c c = (bif c then SKIP else \<bottom>\<^sub>D eif)"

subsection{*Exceptions*}

abbreviation catch_c :: "('t::ordered_cancel_monoid_diff,'f,'\<alpha>) hrel_cp \<Rightarrow> ('t,'f,'\<alpha>) hrel_cp \<Rightarrow> 
                         ('t,'f,'\<alpha>) hrel_cp" ("try (_) catch /(_) end")
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

definition While :: "'\<alpha> cond \<Rightarrow> ('t::ordered_cancel_monoid_diff,'f,'\<alpha>) hrel_cp \<Rightarrow> 
                     ('t,'f,'\<alpha>) hrel_cp" ("while\<^sup>\<top> _ do _ od") where
"While b C = (\<nu> X \<bullet> bif b then (C ;; X) else SKIP eif)"

purge_notation while_top ("while _ do _ od")

abbreviation While_top :: "'\<alpha> cond \<Rightarrow> ('t::ordered_cancel_monoid_diff,'f,'\<alpha>) hrel_cp \<Rightarrow>  
                           ('t,'f,'\<alpha>) hrel_cp" ("while _ do _ od") where
"while b do P od \<equiv> while\<^sup>\<top> b do P od"

purge_notation while_bot ("while\<^sub>\<bottom> _ do _ od")

definition While_bot :: "'\<alpha> cond \<Rightarrow> ('t::ordered_cancel_monoid_diff,'f,'\<alpha>) hrel_cp \<Rightarrow> 
                         ('t,'f,'\<alpha>) hrel_cp" ("while\<^sub>\<bottom> _ do _ od") where
"while\<^sub>\<bottom> b do P od =  (\<mu> X \<bullet> bif b then (P ;; X) else SKIP eif)"

subsection{*While-loop inv*}
text {* While loops with invariant decoration *}

purge_notation while_inv ("while _ invr _ do _ od" 70)

definition While_inv :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t::ordered_cancel_monoid_diff,'f,'\<alpha>) hrel_cp \<Rightarrow> 
                         ('t,'f,'\<alpha>) hrel_cp" ("while _ invr _ do _ od" 70) where
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