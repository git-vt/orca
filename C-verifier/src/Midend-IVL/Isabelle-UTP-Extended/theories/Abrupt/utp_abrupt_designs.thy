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

type_synonym  '\<alpha> abr_des = "'\<alpha> abr_vars_scheme des"
type_synonym ('\<alpha>, '\<beta>) rel_abr_des  = "('\<alpha> abr_des, '\<beta> abr_des) rel"
type_synonym '\<alpha> hrel_abr_des  = "'\<alpha> abr_des hrel"

subsubsection {*Syntactic type setup*}

translations
  (type) "'\<alpha> abr_des" <= (type) "'\<alpha> abr_vars_scheme des"
  (type) "'\<alpha> abr_des" <= (type) "'\<alpha> abr_vars_ext des"
  (type) "('\<alpha>, '\<beta>) rel_abr_des" <= (type) "('\<alpha> abr_des, '\<beta> abr_des) rel"

notation abr_vars_child_lens\<^sub>a ("\<Sigma>\<^sub>a\<^sub>b\<^sub>r")
notation abr_vars_child_lens ("\<Sigma>\<^sub>A\<^sub>B\<^sub>R")

find_theorems "\<Sigma>\<^sub>a\<^sub>b\<^sub>r"  term "\<Sigma>\<^sub>a\<^sub>b\<^sub>r"  term "\<Sigma>\<^sub>A\<^sub>B\<^sub>R"
syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>A\<^sub>B\<^sub>R")
  "_svid_st_a"  :: "svid" ("\<Sigma>\<^sub>a\<^sub>b\<^sub>r")
translations
  "_svid_st_alpha" => "CONST abr_vars_child_lens"
   "_svid_st_a" => "CONST abr_vars_child_lens\<^sub>a"

abbreviation abrupt_f::"('\<alpha>, '\<beta>) rel_abr_des \<Rightarrow> ('\<alpha>, '\<beta>) rel_abr_des"
where "abrupt_f R \<equiv> R\<lbrakk>false/$abrupt\<rbrakk>"

abbreviation abrupt_t::"('\<alpha>, '\<beta>) rel_abr_des \<Rightarrow> ('\<alpha>, '\<beta>) rel_abr_des"
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
 "Simpl\<^sub>A\<^sub>B\<^sub>R P \<equiv> (P \<triangleleft> \<not>$abrupt \<triangleright> II)"

subsection{*Control flow statements*}

text {**}

(*
  des_state
  abr_state

  des :: abr_state \<Rightarrow> des_state
  abrupt ::  abr_state \<Rightarrow> bool

  c : des_state hrel

  lift :: des_state hrel \<Rightarrow> abr_state hrel


 
definition "lift c \<equiv> (s, s') such that 
  (if not abrupt s then c (des s) (des s') 
    else II\<^sub>D (des s) (des s')) 
  and abrupt s = abrupt s'

 "*)

definition skip_abr'' :: "('\<alpha>) hrel_abr_des" where
skip_abr''_def [urel_defs]: "skip_abr''= ($id_lens\<acute> =\<^sub>u $id_lens)"

definition skip_abr' :: "('\<alpha>) hrel_abr_des" ("II\<^sub>a\<^sub>b\<^sub>r") where
skip_abr'_def [urel_defs]: "II\<^sub>a\<^sub>b\<^sub>r = ($\<Sigma>\<^sub>A\<^sub>B\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>A\<^sub>B\<^sub>R)"

definition skip_abr_des :: "('\<alpha>) hrel_abr_des" ("II\<^sub>A\<^sub>B\<^sub>R") where
skip_abr_des_def [urel_defs]: "II\<^sub>A\<^sub>B\<^sub>R = (II \<or> (\<not>$ok))"

definition abrh_def [upred_defs]: 
  "abrh(P) = (II\<^sub>A\<^sub>B\<^sub>R \<triangleleft> $abrupt \<triangleright> P)"

lemma skip_abr_des_def': "II\<^sub>A\<^sub>B\<^sub>R = abrh(true \<turnstile> ((\<not>$abrupt\<acute>) \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R))"
  by (rel_auto)    
    
definition skip_abr :: "('\<alpha>) hrel_abr_des" ("SKIP\<^sub>A\<^sub>B\<^sub>R")
where [urel_defs]:
  "SKIP\<^sub>A\<^sub>B\<^sub>R = Simpl\<^sub>A\<^sub>B\<^sub>R (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> ((\<not>$abrupt\<acute>) \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R))"
  
definition RR  where
[upred_defs]: "RR(P) = (\<exists> {$ok,$ok\<acute>,$abrupt,$abrupt\<acute>} \<bullet> (P))"

lemma "RR(abrh(P)) = abrh(RR(P))" (*do they commute?*)
  oops
    
lemma  1:
 "(II\<^sub>a\<^sub>b\<^sub>r ;; RR (P)) = RR (P)"
 "(RR (P) ;; II\<^sub>a\<^sub>b\<^sub>r) = RR (P)" 
  by (rel_auto)+

lemma  2:
  "(II\<^sub>A\<^sub>B\<^sub>R ;; RR(abrh(P))) = RR(abrh(P))"
  "(RR(abrh(P)) ;; II\<^sub>A\<^sub>B\<^sub>R) = RR(abrh(P))" 
  by (rel_auto+; (metis (full_types)))+

lemma "RR(II\<^sub>A\<^sub>B\<^sub>R) is (RR o abrh)"
  apply pred_simp
  apply rel_simp
  apply (metis (full_types))
  done   

lemma  3:
  "(RR (II\<^sub>A\<^sub>B\<^sub>R) ;; RR(abrh(P))) = RR(abrh(P))"
  "(RR(abrh(P)) ;; RR(II\<^sub>A\<^sub>B\<^sub>R)) = RR(abrh(P))" 
  by rel_blast+

lemma 
  assumes "P is RR"
  shows "(P ;; II\<^sub>a\<^sub>b\<^sub>r) = P"  "( II\<^sub>a\<^sub>b\<^sub>r ;;P  ) = P"
  proof -
  have 1: "RR(P) ;; II\<^sub>a\<^sub>b\<^sub>r = RR(P)"
    by (rel_auto)
  have 2: "II\<^sub>a\<^sub>b\<^sub>r ;; RR(P) = RR(P)"
    by (rel_auto)
  from 1 2 show "P ;; II\<^sub>a\<^sub>b\<^sub>r = P" "II\<^sub>a\<^sub>b\<^sub>r ;; P = P"
    by (simp_all add: Healthy_if assms)
qed  
     
term "(\<exists> {$v1} \<bullet> undefined)"
term "(\<^bold>\<exists> (v1, v2, v3, v4) \<bullet> undefined)"  
term "(\<exists> v1 v2. x)"    
lemma "(\<exists> {$ok,$ok\<acute>,$abrupt,$abrupt\<acute>} \<bullet> (P)) = 
       undefined"
  apply rel_simp
  oops 
  find_theorems "uex"    

subsection{*THROW*}

definition throw_abr :: "('\<alpha>) hrel_abr_des" ("THROW\<^sub>A\<^sub>B\<^sub>R")
where [urel_defs]: 
  "THROW\<^sub>A\<^sub>B\<^sub>R = Simpl\<^sub>A\<^sub>B\<^sub>R(\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> ($abrupt\<acute> \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R))"

definition assigns_abr :: "'\<alpha> usubst \<Rightarrow> ('\<alpha>) hrel_abr_des" ("\<langle>_\<rangle>\<^sub>A\<^sub>B\<^sub>R")
where [urel_defs]: 
  "assigns_abr \<sigma> = Simpl\<^sub>A\<^sub>B\<^sub>R (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<not>$abrupt\<acute> \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R))"

syntax
  "_assignmentabr" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=\<^sub>A\<^sub>B\<^sub>R" 72)

translations
  "_assignmentabr xs vs" => "CONST assigns_abr (_mk_usubst (CONST id) xs vs)"
  "x :=\<^sub>A\<^sub>B\<^sub>R v" <= "CONST assigns_abr (CONST subst_upd (CONST id) (CONST svar x) v)"
  "x :=\<^sub>A\<^sub>B\<^sub>R v" <= "CONST assigns_abr (CONST subst_upd (CONST id) x v)"
  "x,y :=\<^sub>A\<^sub>B\<^sub>R u,v" <= "CONST assigns_abr (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"


subsection{*Conditional*}

abbreviation If_abr :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_abr_des \<Rightarrow> ('\<alpha>) hrel_abr_des \<Rightarrow> ('\<alpha>) hrel_abr_des" ("bif\<^sub>A\<^sub>B\<^sub>R (_)/ then (_) else (_) eif")
where "bif\<^sub>A\<^sub>B\<^sub>R b then P else Q eif \<equiv> Simpl\<^sub>A\<^sub>B\<^sub>R (P \<triangleleft> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<triangleright> Q)"

subsection{*assert and assume*}

definition rassume_abr :: "'\<alpha> upred \<Rightarrow> ('\<alpha>) hrel_abr_des" ("_\<^sup>\<top>\<^sup>C" [999] 999) where
[urel_defs]: "rassume_abr c = (bif\<^sub>A\<^sub>B\<^sub>R c then SKIP\<^sub>A\<^sub>B\<^sub>R else \<top>\<^sub>A\<^sub>B\<^sub>R eif)"

definition rassert_abr :: "'\<alpha> upred \<Rightarrow> ('\<alpha>) hrel_abr_des" ("_\<^sub>\<bottom>\<^sub>C" [999] 999) where
[urel_defs]: "rassert_abr c = (bif\<^sub>A\<^sub>B\<^sub>R c then SKIP\<^sub>A\<^sub>B\<^sub>R else \<bottom>\<^sub>A\<^sub>B\<^sub>R eif)"

subsection{*Exceptions*}

abbreviation catch_abr :: "('\<alpha>) hrel_abr_des \<Rightarrow> ('\<alpha>) hrel_abr_des \<Rightarrow> ('\<alpha>) hrel_abr_des" ("try\<^sub>A\<^sub>B\<^sub>R (_) catch /(_) end")
where "try\<^sub>A\<^sub>B\<^sub>R P catch Q end \<equiv> Simpl\<^sub>A\<^sub>B\<^sub>R (P ;; ((abrupt:== (\<not> &abrupt) ;; Q) \<triangleleft> $abrupt \<triangleright> II))"

subsection{*Scoping*}

definition block_abr ("bob\<^sub>A\<^sub>B\<^sub>R INIT (_) BODY /(_) RESTORE /(_) RETURN/(_) eob") where
[urel_defs]:
  "bob\<^sub>A\<^sub>B\<^sub>R INIT init BODY body RESTORE restore RETURN return eob=
    Simpl\<^sub>A\<^sub>B\<^sub>R 
    (Abs_uexpr (\<lambda>(s, s'). 
     \<lbrakk>init ;; body ;; Abs_uexpr (\<lambda>(t, t').
                       \<lbrakk>(abrupt:== (\<not> &abrupt) ;;restore (s, s') (t, t');; THROW\<^sub>A\<^sub>B\<^sub>R) \<triangleleft> $abrupt \<triangleright> II;; 
         restore (s, s') (t, t');; return(s, s') (t, t')\<rbrakk>\<^sub>e (t, t'))\<rbrakk>\<^sub>e (s, s')))" 

subsection{*Abrupt Design Iterations*}
  
definition While_gfp_abr_des :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_abr_des \<Rightarrow> '\<alpha> hrel_abr_des" ("while\<^sup>\<top>\<^sup>D\<^sup>A _ do _ od")
where "while\<^sup>\<top>\<^sup>D\<^sup>A b do B od = (\<nu>\<^sub>D X \<bullet> bif\<^sub>A\<^sub>B\<^sub>R b then (B ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"

definition While_lfp_abr_des :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_abr_des \<Rightarrow> '\<alpha> hrel_abr_des" ("while\<^sub>\<bottom>\<^sub>D\<^sub>A _ do _ od") 
where "while\<^sub>\<bottom>\<^sub>D\<^sub>A b do B od =  (\<mu>\<^sub>D X \<bullet> bif\<^sub>A\<^sub>B\<^sub>R b then (B ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"

abbreviation While_bot_abr_des :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_abr_des \<Rightarrow> '\<alpha> hrel_abr_des" ("while\<^sub>D\<^sub>A\<^sub>B\<^sub>R _ do _ od") 
where "while\<^sub>D\<^sub>A\<^sub>B\<^sub>R b do B od \<equiv> while\<^sub>\<bottom>\<^sub>D\<^sub>A b do B od"  

text {*While loops with invariant decoration*}

definition While_inv_abr_des :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_abr_des \<Rightarrow> '\<alpha> hrel_abr_des" ("while\<^sub>D\<^sub>A\<^sub>B\<^sub>R _ invr _ do _ od") 
where "while\<^sub>D\<^sub>A\<^sub>B\<^sub>R b invr p do S od = while\<^sub>D\<^sub>A\<^sub>B\<^sub>R b do S od"

text {*While loops with invariant and variant decoration*}
  
definition While_inv_vrt_abr_des :: 
  "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow>'\<alpha> hrel_abr_des \<Rightarrow> '\<alpha> hrel_abr_des" ("while\<^sub>D\<^sub>A\<^sub>B\<^sub>R _ invr _ vrt _ do _ od") 
where "while\<^sub>D\<^sub>A\<^sub>B\<^sub>R b invr p vrt e do S od = while\<^sub>D\<^sub>A\<^sub>B\<^sub>R b do S od"
  
declare While_gfp_abr_des_def [urel_defs]
declare While_inv_abr_des_def [urel_defs]
declare While_lfp_abr_des_def [urel_defs]
declare While_inv_vrt_abr_des_def [urel_defs]

subsection{*Normal Design Iterations*}   
  
definition While_gfp_abr_ndes :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_abr_des \<Rightarrow> '\<alpha> hrel_abr_des" ("while\<^sup>\<top>\<^sup>N\<^sup>A _ do _ od")
where "while\<^sup>\<top>\<^sup>N\<^sup>A b do B od = (\<nu>\<^sub>N X \<bullet> bif\<^sub>A\<^sub>B\<^sub>R b then (B ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"

definition While_lfp_abr_ndes :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_abr_des \<Rightarrow> '\<alpha> hrel_abr_des" ("while\<^sub>\<bottom>\<^sub>N\<^sub>A _ do _ od") 
  where "while\<^sub>\<bottom>\<^sub>N\<^sub>A b do B od =  (\<mu>\<^sub>N X \<bullet> bif\<^sub>A\<^sub>B\<^sub>R b then (B ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"

abbreviation While_bot_abr_ndes :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel_abr_des \<Rightarrow> '\<alpha> hrel_abr_des" ("while\<^sub>N\<^sub>A\<^sub>B\<^sub>R _ do _ od") 
where "while\<^sub>N\<^sub>A\<^sub>B\<^sub>R b do B od \<equiv> while\<^sub>\<bottom>\<^sub>N\<^sub>A b do B od"

text {*While loops with invariant decoration*}

definition While_inv_abr_ndes :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel_abr_des \<Rightarrow> '\<alpha> hrel_abr_des" ("while\<^sub>N\<^sub>A\<^sub>B\<^sub>R _ invr _ do _ od") 
where "while\<^sub>N\<^sub>A\<^sub>B\<^sub>R b invr p do S od = while\<^sub>N\<^sub>A\<^sub>B\<^sub>R b do S od"
    
text {*While loops with invariant and variant decoration*}

definition While_inv_vrt_abr_ndes :: 
  "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel_abr_des \<Rightarrow> '\<alpha> hrel_abr_des" ("while\<^sub>N\<^sub>A\<^sub>B\<^sub>R _ invr _ vrt _ do _ od") 
where "while\<^sub>N\<^sub>A\<^sub>B\<^sub>R b invr p vrt e do S od = while\<^sub>N\<^sub>A\<^sub>B\<^sub>R b do S od"

declare While_gfp_ndes_def [urel_defs]
declare While_inv_ndes_def [urel_defs]
declare While_lfp_ndes_def [urel_defs]
declare While_inv_vrt_ndes_def [urel_defs]
  
subsection {* UTP theories for abrupt *}

typedecl ABR

abbreviation "ABR \<equiv> UTHY(ABR, '\<alpha> abr_des)"

overloading
  abr_hcond == "utp_hcond :: (ABR, '\<alpha> abr_des) uthy \<Rightarrow> ('\<alpha> abr_des \<times> '\<alpha> abr_des) health"
  abr_unit == "utp_unit :: (ABR, '\<alpha> abr_des) uthy \<Rightarrow>  '\<alpha> hrel_abr_des" (unchecked)
begin
  definition abr_hcond :: "(ABR, '\<alpha> abr_des) uthy \<Rightarrow> ('\<alpha> abr_des \<times> '\<alpha> abr_des) health" where
  [upred_defs]: "abr_hcond t = undefined"

  definition abr_unit :: "(ABR, '\<alpha> abr_des) uthy \<Rightarrow> '\<alpha> hrel_abr_des" where
  [upred_defs]: "abr_unit t = undefined"
end 
  
end

