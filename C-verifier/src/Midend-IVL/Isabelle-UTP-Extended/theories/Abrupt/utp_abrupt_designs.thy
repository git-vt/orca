theory utp_abrupt_designs
imports   "../Design/utp_designs_more"

begin
subsection {*Sequential C-program alphabet*}

text 
{* In order to capture exceptions, we extend the alphabet of UTP by an additional global 
   state variables:
   \begin{itemize}   
      \<^item> abrupt: a boolean variable used to specify if the program is in an abrupt state or not.
   \end{itemize}
*}

alphabet abr_vars = des_vars +
  abrupt :: bool

declare  abr_vars.splits [alpha_splits]

text \<open>This abbreviation reduces verbosity for restore/return functions in blocks.\<close>
abbreviation \<open>cp_des v s \<equiv> \<guillemotleft>\<lbrakk>v\<rbrakk>\<^sub>e ((abr_vars.more \<circ> des_vars.more) s)\<guillemotright>\<close>

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
  lens_interp "\<lambda> (ok, r) . (ok, abrupt\<^sub>v r, more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation cp_abr_rel: lens_interp "\<lambda>(ok, ok', r, r').
  (ok, ok', abrupt\<^sub>v r, abrupt\<^sub>v r', more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

subsubsection {*Type lifting*}

type_synonym  '\<alpha> cpa = "'\<alpha> abr_vars_scheme des"
type_synonym ('\<alpha>, '\<beta>) rel_cpa  = "('\<alpha> cpa, '\<beta> cpa) rel"
type_synonym '\<alpha> hrel_cpa  = "'\<alpha> cpa hrel"

subsubsection {*Syntactic type setup*}

translations
  (type) "'\<alpha> cpa" <= (type) "'\<alpha> abr_vars_scheme des"
  (type) "'\<alpha> cpa" <= (type) "'\<alpha> abr_vars_ext des"
  (type) "('\<alpha>, '\<beta>) rel_cpa" <= (type) "('\<alpha> cpa, '\<beta> cpa) rel"

notation abr_vars_child_lens\<^sub>a ("\<Sigma>\<^sub>a\<^sub>b\<^sub>r")
notation abr_vars_child_lens ("\<Sigma>\<^sub>A\<^sub>B\<^sub>R")

syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>A\<^sub>B\<^sub>R")
  "_svid_st_a"  :: "svid" ("\<Sigma>\<^sub>a\<^sub>b\<^sub>r")
translations
  "_svid_st_alpha" => "CONST abr_vars_child_lens"
   "_svid_st_a" => "CONST abr_vars_child_lens\<^sub>a"

abbreviation abrupt_f::"('\<alpha>, '\<beta>) rel_cpa \<Rightarrow> ('\<alpha>, '\<beta>) rel_cpa"
where "abrupt_f R \<equiv> R\<lbrakk>false/$abrupt\<rbrakk>"

abbreviation abrupt_t::"('\<alpha>, '\<beta>) rel_cpa \<Rightarrow> ('\<alpha>, '\<beta>) rel_cpa"
where "abrupt_t R \<equiv> R\<lbrakk>true/$abrupt\<rbrakk>"

syntax
  "_abrupt_f"  :: "logic \<Rightarrow> logic" ("_\<^sub>a\<^sub>f" [1000] 1000)
  "_abrupt_t"  :: "logic \<Rightarrow> logic" ("_\<^sub>a\<^sub>t" [1000] 1000)
  "_top_abr" :: "logic" ("\<top>\<^sub>A\<^sub>B\<^sub>R")
  "_bot_abr" :: "logic" ("\<bottom>\<^sub>A\<^sub>B\<^sub>R")

translations
  "P \<^sub>a\<^sub>f" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST abrupt) false) P"
  "P \<^sub>a\<^sub>t" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST abrupt) true) P"
  "\<top>\<^sub>A\<^sub>B\<^sub>R" => "(CONST not_upred (CONST utp_expr.var (CONST ivar CONST ok)))"
  "\<bottom>\<^sub>A\<^sub>B\<^sub>R" => "true"

lemma "\<top>\<^sub>A\<^sub>B\<^sub>R = ((\<not> $ok))"
  by auto

subsection {*Substitution lift and drop*}

abbreviation lift_rel_usubst_cpa ("\<lceil>_\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R")
where "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<equiv> \<sigma> \<oplus>\<^sub>s (\<Sigma>\<^sub>A\<^sub>B\<^sub>R \<times>\<^sub>L \<Sigma>\<^sub>A\<^sub>B\<^sub>R)"

abbreviation lift_usubst_cpa ("\<lceil>_\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R")
where "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<equiv> \<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R"

abbreviation drop_cpa_rel_usubst ("\<lfloor>_\<rfloor>\<^sub>S\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>\<sigma>\<rfloor>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<equiv> \<sigma> \<restriction>\<^sub>s (\<Sigma>\<^sub>A\<^sub>B\<^sub>R \<times>\<^sub>L \<Sigma>\<^sub>A\<^sub>B\<^sub>R)"

abbreviation drop_cpa_usubst ("\<lfloor>_\<rfloor>\<^sub>s\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>\<sigma>\<rfloor>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<equiv> \<lfloor>\<lfloor>\<sigma>\<rfloor>\<^sub>S\<^sub>A\<^sub>B\<^sub>R\<rfloor>\<^sub>s"

subsection {*UTP-Relations lift and drop*}

abbreviation lift_rel_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>A\<^sub>B\<^sub>R")
where "\<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>A\<^sub>B\<^sub>R \<times>\<^sub>L \<Sigma>\<^sub>A\<^sub>B\<^sub>R)"

abbreviation lift_pre_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><")
where "\<lceil>p\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub><\<rceil>\<^sub>A\<^sub>B\<^sub>R"

abbreviation lift_post_uexpr_cpa ("\<lceil>_\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>>")
where "\<lceil>p\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>> \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub>>\<rceil>\<^sub>A\<^sub>B\<^sub>R"

abbreviation drop_cpa_rel_uexpr ("\<lfloor>_\<rfloor>\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>P\<rfloor>\<^sub>A\<^sub>B\<^sub>R \<equiv> P \<restriction>\<^sub>p (\<Sigma>\<^sub>A\<^sub>B\<^sub>R \<times>\<^sub>L \<Sigma>\<^sub>A\<^sub>B\<^sub>R)"

abbreviation drop_cpa_pre_uexpr ("\<lfloor>_\<rfloor>\<^sub><\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>P\<rfloor>\<^sub><\<^sub>A\<^sub>B\<^sub>R \<equiv> \<lfloor>\<lfloor>P\<rfloor>\<^sub>A\<^sub>B\<^sub>R\<rfloor>\<^sub><"

abbreviation drop_cpa_post_uexpr ("\<lfloor>_\<rfloor>\<^sub>>\<^sub>A\<^sub>B\<^sub>R")
where "\<lfloor>P\<rfloor>\<^sub>>\<^sub>A\<^sub>B\<^sub>R \<equiv> \<lfloor>\<lfloor>P\<rfloor>\<^sub>A\<^sub>B\<^sub>R\<rfloor>\<^sub>>"

subsection {* Reactive lemmas *}


subsection{*Healthiness conditions*}

text {*Programs in abrupt state do not progress*}   
abbreviation
 "Simpl\<^sub>A\<^sub>B\<^sub>R P \<equiv> ((\<not>$abrupt \<turnstile> P) \<squnion> ($abrupt  \<turnstile> II))"

subsection{*Control flow statements*}

text {**}

definition skip_abr :: "('\<alpha>) hrel_cpa" ("SKIP\<^sub>A\<^sub>B\<^sub>R")
where [urel_defs]:
  "SKIP\<^sub>A\<^sub>B\<^sub>R = Simpl\<^sub>A\<^sub>B\<^sub>R (\<not>$abrupt\<acute> \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R)"

subsection{*THROW*}

definition throw_abr :: "('\<alpha>) hrel_cpa" ("THROW\<^sub>A\<^sub>B\<^sub>R")
where [urel_defs]: 
  "THROW\<^sub>A\<^sub>B\<^sub>R = Simpl\<^sub>A\<^sub>B\<^sub>R($abrupt\<acute> \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R)"

definition assigns_abr :: "'\<alpha> usubst \<Rightarrow> ('\<alpha>) hrel_cpa" ("\<langle>_\<rangle>\<^sub>A\<^sub>B\<^sub>R")
where [urel_defs]: 
  "assigns_abr \<sigma> = Simpl\<^sub>A\<^sub>B\<^sub>R (\<not>$abrupt\<acute> \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R)"

subsection{*Conditional*}

abbreviation If_abr :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_cpa \<Rightarrow> ('\<alpha>) hrel_cpa \<Rightarrow> ('\<alpha>) hrel_cpa" ("bif (_)/ then (_) else (_) eif")
where "bif b then P else Q eif \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<triangleright> Q)"

subsection{*assert and assume*}

definition rassume_abr :: "'\<alpha> upred \<Rightarrow> ('\<alpha>) hrel_cpa" ("_\<^sup>\<top>\<^sup>C" [999] 999) where
[urel_defs]: "rassume_abr c = (bif c then SKIP\<^sub>A\<^sub>B\<^sub>R else \<top>\<^sub>A\<^sub>B\<^sub>R eif)"

definition rassert_abr :: "'\<alpha> upred \<Rightarrow> ('\<alpha>) hrel_cpa" ("_\<^sub>\<bottom>\<^sub>C" [999] 999) where
[urel_defs]: "rassert_abr c = (bif c then SKIP\<^sub>A\<^sub>B\<^sub>R else \<bottom>\<^sub>A\<^sub>B\<^sub>R eif)"

subsection{*Exceptions*}

abbreviation catch_abr :: "('\<alpha>) hrel_cpa \<Rightarrow> ('\<alpha>) hrel_cpa \<Rightarrow> ('\<alpha>) hrel_cpa" ("try (_) catch /(_) end")
where "try P catch Q end \<equiv> (P ;; ((abrupt:== (\<not> &abrupt) ;; Q) \<triangleleft> $abrupt \<triangleright> II))"

subsection{*Scoping*}

definition block_abr ("bob INIT (_) BODY /(_) RESTORE /(_) RETURN/(_) eob") where
[urel_defs]:
  "bob INIT init BODY body RESTORE restore RETURN return eob= 
    (Abs_uexpr (\<lambda>(s, s'). 
     \<lbrakk>init ;; body ;; Abs_uexpr (\<lambda>(t, t').
                       \<lbrakk>(abrupt:== (\<not> &abrupt) ;;restore (s, s') (t, t');; THROW\<^sub>A\<^sub>B\<^sub>R) \<triangleleft> $abrupt \<triangleright> II;; 
         restore (s, s') (t, t');; return(s, s') (t, t')\<rbrakk>\<^sub>e (t, t'))\<rbrakk>\<^sub>e (s, s')))" 

subsection{*Loops*}

purge_notation while ("while\<^sup>\<top> _ do _ od")

definition While_abr_top :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_cpa \<Rightarrow> ('\<alpha>) hrel_cpa" ("while\<^sup>\<top> _ do _ od") where
"While b C = (\<nu>\<^sub>D X \<bullet> bif b then (C ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"

purge_notation while_top ("while _ do _ od")

abbreviation While_top :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_cpa \<Rightarrow> ('\<alpha>) hrel_cpa" ("while _ do _ od") where
"while b do P od \<equiv> while\<^sup>\<top> b do P od"

purge_notation while_bot ("while\<^sub>\<bottom> _ do _ od")

definition While_bot :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_cpa \<Rightarrow> ('\<alpha>) hrel_cpa" ("while\<^sub>\<bottom> _ do _ od") where
"while\<^sub>\<bottom> b do P od =  (\<mu> X \<bullet> bif b then (P ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"

subsection{*While-loop inv*}
text {*While loops with invariant decoration*}

purge_notation while_inv ("while _ invr _ do _ od" 71)

definition While_inv :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_cpa \<Rightarrow> ('\<alpha>) hrel_cpa" ("while _ invr _ do _ od") where
"while b invr p do S od = while b do S od"

declare While_def [urel_defs]
declare While_inv_def [urel_defs]
declare While_bot_def [urel_defs]

syntax
  "_assignmentabr" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr "\<Midarrow>" 72)

translations
  "_assignmentabr xs vs" => "CONST assigns_abr (_mk_usubst (CONST id) xs vs)"
  "x \<Midarrow> v" <= "CONST assigns_abr (CONST subst_upd (CONST id) (CONST svar x) v)"
  "x \<Midarrow> v" <= "CONST assigns_abr (CONST subst_upd (CONST id) x v)"
  "x,y \<Midarrow> u,v" <= "CONST assigns_abr (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"


subsection {* UTP theories *}

typedecl ABR

abbreviation "ABR \<equiv> UTHY(ABR, '\<alpha> cpa)"

overloading
  abr_hcond == "utp_hcond :: (ABR, '\<alpha> cpa) uthy \<Rightarrow> ('\<alpha> cpa \<times> '\<alpha> cpa) health"
  abr_unit == "utp_unit :: (ABR, '\<alpha> cpa) uthy \<Rightarrow>  '\<alpha> hrel_cpa" (unchecked)

begin
  definition abr_hcond :: "(ABR, '\<alpha> cpa) uthy \<Rightarrow> ('\<alpha> cpa \<times> '\<alpha> cpa) health" where
  [upred_defs]: "abr_hcond t = undefined"

  definition abr_unit :: "(ABR, '\<alpha> cpa) uthy \<Rightarrow> '\<alpha> hrel_cpa" where
  [upred_defs]: "abr_unit t = undefined"


end  
end