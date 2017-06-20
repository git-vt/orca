theory utp_abrupt_designs
imports   "../utp/utp" utp_designs
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

alphabet  'a cp_abr = des_vars +
  abrupt:: bool
  abrupt_aux :: "'a option" (*store the reason of the abrupt termination*)
  (*wait :: bool*)

declare cp_abr.splits [alpha_splits]

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

interpretation cp_abr:
  lens_interp "\<lambda> (ok, r) . (ok, abrupt\<^sub>v r, abrupt_aux\<^sub>v r, more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation cp_abr_rel: lens_interp "\<lambda>(ok, ok', r, r').
  (ok, ok', abrupt\<^sub>v r, abrupt\<^sub>v r', abrupt_aux\<^sub>v r, abrupt_aux\<^sub>v r', more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done


subsubsection {*Type lifting*}

type_synonym  ('a, '\<alpha>) cpa = "('a, '\<alpha>) cp_abr_scheme des"
type_synonym ('a,'\<alpha>,'\<beta>) rel_cpa  = "(('a, '\<alpha>) cpa, ('a, '\<beta>) cpa) rel"
type_synonym ('a, '\<alpha>) hrel_cpa  = "(('a, '\<alpha>) cpa) hrel"

subsubsection {*Syntactic type setup*}

translations
  (type) "('a, '\<alpha>) cpa" <= (type) " ('a, '\<alpha>) cp_abr_scheme des"
  (type) "('a, '\<alpha>) cpa" <= (type) " ('a, '\<alpha>) cp_abr_ext des"
  (type) "('a,'\<alpha>,'\<beta>) rel_cpa" <= (type) "(('a, '\<alpha>) cpa, (_, '\<beta>) cpa) rel"

notation cp_abr_child_lens\<^sub>a ("\<Sigma>\<^sub>a\<^sub>b\<^sub>r")
notation cp_abr_child_lens ("\<Sigma>\<^sub>A\<^sub>B\<^sub>R")

syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>A\<^sub>B\<^sub>R")
  "_svid_st_a"  :: "svid" ("\<Sigma>\<^sub>a\<^sub>b\<^sub>r")
translations
  "_svid_st_alpha" => "CONST cp_abr_child_lens"
   "_svid_st_a" => "CONST cp_abr_child_lens\<^sub>a"

lemma cvars_ord [usubst]:
  "$ok \<prec>\<^sub>v $ok\<acute>" "$abrupt \<prec>\<^sub>v $abrupt\<acute>" 
  "$ok \<prec>\<^sub>v $abrupt\<acute>" "$ok \<prec>\<^sub>v $abrupt" "$ok\<acute> \<prec>\<^sub>v $abrupt\<acute>" "$ok\<acute> \<prec>\<^sub>v $abrupt" 
  "$ok \<prec>\<^sub>v $abrupt_aux\<acute>" "$ok \<prec>\<^sub>v $abrupt_aux" "$ok\<acute> \<prec>\<^sub>v $abrupt_aux\<acute>" "$ok\<acute> \<prec>\<^sub>v $abrupt_aux"
  "$abrupt \<prec>\<^sub>v $abrupt_aux\<acute>" "$abrupt \<prec>\<^sub>v $abrupt_aux" "$abrupt\<acute> \<prec>\<^sub>v $abrupt_aux\<acute>" "$abrupt\<acute> \<prec>\<^sub>v $abrupt_aux"
  by (simp_all add: var_name_ord_def)

abbreviation abrupt_f::"('a,'\<alpha>, '\<beta>) rel_cpa \<Rightarrow> ('a, '\<alpha>, '\<beta>) rel_cpa"
where "abrupt_f R \<equiv> R\<lbrakk>false/$abrupt\<rbrakk>"

abbreviation abrupt_t::"('a,'\<alpha>, '\<beta>) rel_cpa \<Rightarrow> ('a,'\<alpha>, '\<beta>) rel_cpa"
where "abrupt_t R \<equiv> R\<lbrakk>true/$abrupt\<rbrakk>"

syntax
  "_abrupt_f"  :: "logic \<Rightarrow> logic" ("_\<^sub>a\<^sub>f" [1000] 1000)
  "_abrupt_t"  :: "logic \<Rightarrow> logic" ("_\<^sub>a\<^sub>t" [1000] 1000)
  "_top_abr" :: "logic" ("\<top>\<^sub>A\<^sub>B\<^sub>R")
  "_bot_abr" :: "logic" ("\<bottom>\<^sub>A\<^sub>B\<^sub>R")

translations
  "P \<^sub>a\<^sub>f" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST abrupt) false) P"
  "P \<^sub>a\<^sub>t" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST abrupt) true) P"
  "\<top>\<^sub>A\<^sub>B\<^sub>R" => "CONST conj_upred 
            (CONST not_upred (CONST utp_expr.var (CONST ivar CONST ok))) 
            (CONST conj_upred (CONST not_upred (CONST utp_expr.var (CONST ivar CONST abrupt)))
                              (CONST eq_upred  (CONST utp_expr.var (CONST ivar CONST abrupt_aux))
                                               (CONST utp_expr.lit (CONST None))))"
  "\<bottom>\<^sub>A\<^sub>B\<^sub>R" => "true"

lemma "\<top>\<^sub>A\<^sub>B\<^sub>R = ((\<not> $ok) \<and> (\<not> $abrupt) \<and> ($abrupt_aux =\<^sub>u \<guillemotleft>None\<guillemotright>))"
  by auto

subsection {*UTP-Relations lift and drop*}

abbreviation lift_desr ("\<lceil>_\<rceil>\<^sub>A\<^sub>B\<^sub>R")
where "\<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>A\<^sub>B\<^sub>R \<times>\<^sub>L \<Sigma>\<^sub>A\<^sub>B\<^sub>R)"

abbreviation lift_pre_desr ("\<lceil>_\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><")
where "\<lceil>p\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub><\<rceil>\<^sub>A\<^sub>B\<^sub>R"

abbreviation lift_post_desr ("\<lceil>_\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>>")
where "\<lceil>p\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>> \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub>>\<rceil>\<^sub>A\<^sub>B\<^sub>R"

abbreviation drop_desr ("\<lfloor>_\<rfloor>\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>P\<rfloor>\<^sub>A\<^sub>B\<^sub>R \<equiv> P \<restriction>\<^sub>p (\<Sigma>\<^sub>A\<^sub>B\<^sub>R \<times>\<^sub>L \<Sigma>\<^sub>A\<^sub>B\<^sub>R)"


subsection {* Reactive lemmas *}

lemma unrest_ok_lift_rea [unrest]:
  "$ok \<sharp> \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R" "$ok\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  by (pred_auto)+

lemma unrest_abrupt_lift_rea [unrest]:
  "$abrupt \<sharp> \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R" "$abrupt\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  by (pred_auto)+

lemma seqr_abrupt_true [usubst]: "(P ;; Q) \<^sub>a\<^sub>t = (P \<^sub>a\<^sub>t ;; Q)"
  by (rel_auto)

lemma seqr_abrupt_false [usubst]: "(P ;; Q) \<^sub>a\<^sub>f = (P \<^sub>a\<^sub>f ;; Q)"
  by (rel_auto)

subsection{*Healthiness conditions*}

text {*Programs in fault or abrupt or stuck state do not progress*}
definition C3_abr_def [upred_defs]: 
  "C3_abr(P) = (P \<triangleleft> \<not>$abrupt \<and> $abrupt_aux =\<^sub>u \<guillemotleft>None\<guillemotright> \<triangleright> II)"

abbreviation
 "Simpl\<^sub>A\<^sub>B\<^sub>R P \<equiv> C3_abr(\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (P))"

subsection{*Control flow statements*}

text{*We introduce the known control-flow statements for C. Our semantics is restricted
      to @{const C3_abr}. In other words It assumes:
     \begin{itemize}   
       \<^item>  an execution starting from initial stable state ie,@{term "$ok"},   
       \<^item>  terminates a final state ie,@{term "$ok\<acute>"},
       \<^item>  the final state is a normal state ie,
          @{term "\<not>$abrupt"} and @{term "$fault_tr =\<^sub>u \<guillemotleft>None\<guillemotright>"},
     \end{itemize}
    Thus it capture Simpl semantics.
    *}


definition skip_abr :: "('a, '\<alpha>) hrel_cpa" ("SKIP\<^sub>A\<^sub>B\<^sub>R")
where [urel_defs]:
  "SKIP\<^sub>A\<^sub>B\<^sub>R = Simpl\<^sub>A\<^sub>B\<^sub>R (\<not>$abrupt\<acute> \<and> $abrupt_aux\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R)"

definition assigns_c :: " '\<alpha> usubst \<Rightarrow> ('a, '\<alpha>) hrel_cpa" ("\<langle>_\<rangle>\<^sub>A\<^sub>B\<^sub>R")
where [urel_defs]: 
  "assigns_c \<sigma> = Simpl\<^sub>A\<^sub>B\<^sub>R(\<not>$abrupt\<acute> \<and> $abrupt_aux\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R)"

subsection{*THROW*}

definition throw_abr :: "('a, '\<alpha>) hrel_cpa" ("THROW\<^sub>A\<^sub>B\<^sub>R")
where [urel_defs]: 
  "THROW\<^sub>A\<^sub>B\<^sub>R = Simpl\<^sub>A\<^sub>B\<^sub>R ($abrupt\<acute> \<and> $abrupt_aux\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R)"

subsection{*Conditional*}

abbreviation If_abr :: "'\<alpha> cond \<Rightarrow> ('a, '\<alpha>) hrel_cpa \<Rightarrow> ('a, '\<alpha>) hrel_cpa \<Rightarrow> ('a, '\<alpha>) hrel_cpa" ("bif (_)/ then (_) else (_) eif")where
  "bif b then P else Q eif \<equiv> Simpl\<^sub>A\<^sub>B\<^sub>R (P \<triangleleft> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<triangleright> Q)"

subsection{*assert and assume*}

definition rassume_abr :: "'\<alpha> upred \<Rightarrow> ('a, '\<alpha>) hrel_cpa" ("_\<^sup>\<top>\<^sup>C" [999] 999) where
[urel_defs]: "rassume_abr c = (bif c then SKIP\<^sub>A\<^sub>B\<^sub>R else \<top>\<^sub>A\<^sub>B\<^sub>R eif)"

definition rassert_abr :: "'\<alpha> upred \<Rightarrow> ('a, '\<alpha>) hrel_cpa" ("_\<^sub>\<bottom>\<^sub>C" [999] 999) where
[urel_defs]: "rassert_abr c = (bif c then SKIP\<^sub>A\<^sub>B\<^sub>R else \<bottom>\<^sub>A\<^sub>B\<^sub>R eif)"

subsection{*Exceptions*}

abbreviation catch_abr :: "('a, '\<alpha>) hrel_cpa \<Rightarrow> ('a, '\<alpha>) hrel_cpa \<Rightarrow> ('a, '\<alpha>) hrel_cpa" ("try (_) catch /(_) end")
where "try P catch Q end \<equiv> Simpl\<^sub>A\<^sub>B\<^sub>R (P ;; ((abrupt:== (\<not> &abrupt) ;;Q) \<triangleleft> $abrupt \<triangleright> II))"

subsection{*Scoping*}

definition block_abr ("bob INIT (_) BODY /(_) RESTORE /(_) RETURN/(_) eob") where
[urel_defs]:
  "bob INIT init BODY body RESTORE restore RETURN return eob= 
    Simpl\<^sub>A\<^sub>B\<^sub>R (Abs_uexpr (\<lambda>(s, s'). 
     \<lbrakk>init ;; body ;; Abs_uexpr (\<lambda>(t, t').
                       \<lbrakk>(abrupt:== (\<not> &abrupt) ;;restore (s, s') (t, t');; THROW\<^sub>A\<^sub>B\<^sub>R) \<triangleleft> $abrupt \<triangleright> II;; 
         restore (s, s') (t, t');; return(s, s') (t, t')\<rbrakk>\<^sub>e (t, t'))\<rbrakk>\<^sub>e (s, s')))" 

subsection{*Loops*}
purge_notation while ("while\<^sup>\<top> _ do _ od")

definition While :: "'\<alpha> cond \<Rightarrow> ('a, '\<alpha>) hrel_cpa \<Rightarrow> ('a, '\<alpha>) hrel_cpa" ("while\<^sup>\<top> _ do _ od") where
"While b C = (\<nu> X \<bullet> bif b then (C ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"

purge_notation while_top ("while _ do _ od")

abbreviation While_top :: "'\<alpha> cond \<Rightarrow> ('a, '\<alpha>) hrel_cpa \<Rightarrow> ('a, '\<alpha>) hrel_cpa" ("while _ do _ od") where
"while b do P od \<equiv> while\<^sup>\<top> b do P od"

purge_notation while_bot ("while\<^sub>\<bottom> _ do _ od")

definition While_bot :: "'\<alpha> cond \<Rightarrow> ('a, '\<alpha>) hrel_cpa \<Rightarrow> ('a, '\<alpha>) hrel_cpa" ("while\<^sub>\<bottom> _ do _ od") where
"while\<^sub>\<bottom> b do P od =  (\<mu> X \<bullet> bif b then (P ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"

subsection{*While-loop inv*}
text {* While loops with invariant decoration *}

purge_notation while_inv ("while _ invr _ do _ od" 70)

definition While_inv :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('a, '\<alpha>) hrel_cpa \<Rightarrow> ('a, '\<alpha>) hrel_cpa" ("while _ invr _ do _ od" 70) where
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