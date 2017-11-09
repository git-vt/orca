theory utp_hoare_ndes_prog

imports "../../../../impl/utp_prog_des_more"

begin
section {*Hoare logic for designs*}  
named_theorems hoare_prog

subsection {*Hoare triple definition*}

lift_definition hoare ::   "'\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>P") 
 is  hoare_d .

declare hoare.rep_eq [prog_rep_eq]

lemma hoare_true_assisgns[hoare_prog]: 
  "\<lbrace>p\<rbrace> \<langle>\<sigma>\<rangle>\<^sub>p \<lbrace>true\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma hoare_true_skip_d_t [hoare_prog]: 
  "\<lbrace>p\<rbrace>skip\<lbrace>true\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma hoare_false_d_t [hoare_prog]: 
  "\<lbrace>false\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

subsection {*Precondition weakening*}

lemma hoare_pre_str_d_t[hoare_prog]:
  assumes "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" and "\<lbrace>p\<^sub>2\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<^sub>1\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P" 
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Post-condition strengthening*}

lemma hoare_post_weak_d_t[hoare_prog]:
  assumes "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>2\<rbrace>\<^sub>P" and "`q\<^sub>2 \<Rightarrow> q\<^sub>1`"
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>1\<rbrace>\<^sub>P" 
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Hoare and assertion logic*}

lemma hoare_r_conj_d_t [hoare_prog]: 
  assumes"\<lbrace>p\<rbrace>C\<lbrace>r\<rbrace>\<^sub>P" and "\<lbrace>p\<rbrace>C\<lbrace>s\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>C\<lbrace>r \<and> s\<rbrace>\<^sub>P"
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Hoare SKIP*}

lemma skip_d_hoare_d_t [hoare_prog]: 
  "\<lbrace>p\<rbrace>SKIP\<lbrace>p\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

subsection {*Hoare for assignment*}

lemma assigns_d_hoare_d_t [hoare_prog]: 
  assumes"`p \<Rightarrow> \<sigma> \<dagger> q`" 
  shows  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>p\<lbrace>q\<rbrace>\<^sub>P"
  using assms  
  by (simp add: prog_rep_eq hoare_des)

lemma assigns_d_hoare_d'_t [hoare_prog]: 
  "\<lbrace>\<sigma> \<dagger> p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>p\<lbrace>p\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma assigns_d_floyd_d_t [hoare_prog]:
  assumes \<open>vwb_lens x\<close>
  shows \<open>\<lbrace>p\<rbrace>x :== e\<lbrace>\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrace>\<^sub>P\<close>
  using assms
  by (simp add: prog_rep_eq hoare_des)

subsection {*Hoare for Sequential Composition*}

lemma seq_hoare_d_t [hoare_prog]: 
  assumes"\<lbrace>p\<rbrace>C\<^sub>1\<lbrace>s\<rbrace>\<^sub>P" and "\<lbrace>s\<rbrace>C\<^sub>2\<lbrace>r\<rbrace>\<^sub>P" 
  shows"\<lbrace>p\<rbrace>C\<^sub>1 ; C\<^sub>2\<lbrace>r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)  

subsection {*Hoare for Conditional*}

lemma cond_d_hoare_d_t [hoare_prog]: 
  assumes "\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>P" and "\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>IF b THEN C\<^sub>1 ELSE C\<^sub>2 FI\<lbrace>q\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des) 
    
subsection {*Hoare for While-loop*}   

lemma normal_design_is_H1:
  "P is \<^bold>N \<Longrightarrow> P is H1"
  by (metis  H3_ndesign Healthy_def' ndesign_form)     

lemma while_hoare_r_t [hoare_prog]:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`" 
  assumes induct_step:"\<And> st. \<lbrace>b \<and> I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>I \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"  
  assumes PHI:"`(\<not> b \<and> I) \<Rightarrow> Post`"  
  shows "\<lbrace>Pre\<rbrace>WHILE b INVR  I DO  body OD \<lbrace>Post\<rbrace>\<^sub>P"
  by (simp add:  prog_rep_eq  
                 while_hoare_ndesign_t[OF WF I0 Rep_prog_H1_H3_closed [of body, THEN normal_design_is_H1]
                                        induct_step [unfolded prog_rep_eq] PHI])

section {*Abrupt*}
subsection {*Sequential C-program alphabet*}

text 
{* In order to capture exceptions, we extend the alphabet of UTP by an additional global 
   state variables:
   \begin{itemize}   
      \<^item> abrupt: a boolean variable used to specify if the program is in an abrupt state or not.
   \end{itemize}
*}

alphabet abr_vars = 
  abrupt :: bool

declare  abr_vars.splits [alpha_splits]
  
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

type_synonym '\<alpha> hrel_abr_des  = "'\<alpha> abr_vars_scheme prog"

subsubsection {*Syntactic type setup*}

notation abr_vars_child_lens ("\<Sigma>\<^sub>A\<^sub>B\<^sub>R")

syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>A\<^sub>B\<^sub>R")
translations
  "_svid_st_alpha" => "CONST abr_vars_child_lens"

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
term "\<lceil>p\<rceil>\<^sub>A\<^sub>B\<^sub>R" 
term "SKIP"
find_theorems "\<Sigma>\<^sub>D"  
term " \<lparr>lens_get = des_vars.more,
       lens_put = \<lambda>\<sigma> u. \<sigma>\<lparr>des_vars.more := u\<rparr>\<rparr>"


term "des_vars.more"  
term " \<lparr>lens_get = des_vars.more,
       lens_put = \<lambda>\<sigma> u. undefined\<rparr>"   
term "\<lbrakk>v\<rbrakk>\<^sub>e ((abr_vars.more \<circ> des_vars.more) s)"
term "\<lbrakk>v\<rbrakk>\<^sub>e"  
term "abr_vars.more"  
term "des_vars.more"
term "Rep_uexpr o Rep_prog  "
term "Abs_prog  o Abs_uexpr "  
term "Abs_prog o des_vars.more "
term "Rep_prog "
term "Abs_prog"  
term "Abs_prog o abr_vars.more "
term "Rep_prog o abr_vars.more "  
term "abr_vars.more "
  
definition abrh_def [upred_defs]: 
  "abrh(P) = (IF &abrupt THEN SKIP ELSE  P FI)"

section{*Control flow statements*}

subsection{*SKIP*}
definition  
skip_abr_def [urel_defs]: "skip_abr=  abrh(SKIP)"

subsection{*Assign*}

definition  
assigns_abr_def [urel_defs]: "assigns_abr \<sigma> =  abrh(\<langle>\<sigma>\<rangle>\<^sub>p)"

subsection{*Throw*}

definition  
throw_abr_def [urel_defs]: "throw_abr  =  assigns_abr [&abrupt \<mapsto>\<^sub>s true]"

subsection{*Sequential composition*}
text {*It does not need a definition. We get it by type inference.*}  
term "(throw_abr) ; (p )"  
subsection{*Conditional composition*}

definition  
if_abr_def [urel_defs]: "if_abr b P Q  =  IF (b \<oplus>\<^sub>p \<Sigma>\<^sub>A\<^sub>B\<^sub>R) THEN P ELSE Q FI"

subsection{*Iterations*}

definition  
while_abr_def [urel_defs]: "while_abr b I C  =  WHILE (b \<oplus>\<^sub>p \<Sigma>\<^sub>A\<^sub>B\<^sub>R) \<and> \<not>&abrupt INVR I DO C OD"

subsection{*Recursion*}
(*TODO @Yakoub*)
  
section {*algebraic laws*} 

lemma [Algebraic_Laws_prog]:"IF b THEN P ELSE P FI = P"
  by (simp add: prog_rep_eq Algebraic_Laws.cond_idem)

lemma [Algebraic_Laws_prog]:"skip_abr ;  P =  P" "P ; skip_abr = P"
  unfolding skip_abr_def abrh_def
  by (simp add: Algebraic_Laws_prog)+  

lemma [Algebraic_Laws_prog]:"throw_abr ;  (abrh P) = throw_abr"     
  unfolding throw_abr_def abrh_def assigns_abr_def skip_abr_def
  apply (simp add: prog_rep_eq) 
   apply rel_auto
  done

lemma "(abrh P) ;  \<langle>[&abrupt \<mapsto>\<^sub>s true]\<rangle>\<^sub>p = (abrh P)"
    unfolding throw_abr_def abrh_def assigns_abr_def skip_abr_def
    apply (simp add: prog_rep_eq) 
      
    apply rel_simp
    apply transfer
    unfolding Healthy_def H1_def H3_def
    apply rel_simp
      apply auto
    apply metis
          apply metis
         apply metis
        apply metis

    oops
lemma "abrh(\<langle>a\<rangle>\<^sub>p) ; abrh (throw_abr ;  IF &abrupt THEN (abrupt:== (\<not> &abrupt) ; abrh(\<langle>b\<rangle>\<^sub>p)) ELSE skip_abr FI) = 
         (abrh(\<langle>a\<rangle>\<^sub>p); abrh(\<langle>b\<rangle>\<^sub>p))"
  unfolding throw_abr_def abrh_def assigns_abr_def skip_abr_def
    apply (simp add: prog_rep_eq) 
  apply rel_auto
  apply (smt abr_vars.ext_inject abr_vars_ext_def)+
  done  
 
lemma "abrh(P) ; abrh (throw_abr ;  IF &abrupt THEN (abrupt:== (\<not> &abrupt) ; abrh(Q)) ELSE skip_abr FI) = 
         (abrh(P); abrh(Q))"
  unfolding throw_abr_def abrh_def assigns_abr_def skip_abr_def
    apply (simp add: prog_rep_eq) 
  apply rel_auto
  apply transfer
  unfolding Healthy_def H1_def H3_def
    apply rel_simp
         apply blast
      apply transfer
    unfolding Healthy_def H1_def H3_def
    apply rel_simp
          apply blast
      apply transfer
    unfolding Healthy_def H1_def H3_def
    apply rel_simp
         apply blast
      apply transfer
    unfolding Healthy_def H1_def H3_def
    apply rel_simp
    apply metis
   apply transfer
    unfolding Healthy_def H1_def H3_def
    apply rel_simp
       apply metis
      apply transfer
    unfolding Healthy_def H1_def H3_def
    apply rel_simp
      apply metis
      apply transfer
    unfolding Healthy_def H1_def H3_def
    apply rel_simp
     apply metis
    apply (smt abr_vars.select_convs(2))
done
end