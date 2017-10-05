theory utp_hoare_des

imports "../../../../../Isabelle-UTP/theories/utp_designs"
        "../../../../hoare/AlgebraicLaws/Rel&Des/Algebraic_Laws_aux"

begin

section {*Syntax setup*}
syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>D")
translations
  "_svid_st_alpha" => "CONST des_vars_child_lens"
 
section {*Type projections and injection*}

subsection {*Substitution lift and drop*}

abbreviation lift_rel_usubst_des ("\<lceil>_\<rceil>\<^sub>S\<^sub>D")
where "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<equiv> \<sigma> \<oplus>\<^sub>s (\<Sigma>\<^sub>D \<times>\<^sub>L \<Sigma>\<^sub>D)"

abbreviation lift_usubst_des ("\<lceil>_\<rceil>\<^sub>s\<^sub>D")
where "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>D \<equiv> \<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s\<rceil>\<^sub>S\<^sub>D"

abbreviation drop_cpa_rel_des ("\<lfloor>_\<rfloor>\<^sub>S\<^sub>D")
where "\<lfloor>\<sigma>\<rfloor>\<^sub>S\<^sub>D \<equiv> \<sigma> \<restriction>\<^sub>s (\<Sigma>\<^sub>D \<times>\<^sub>L \<Sigma>\<^sub>D)"

abbreviation drop_cpa_des ("\<lfloor>_\<rfloor>\<^sub>s\<^sub>D")
  where "\<lfloor>\<sigma>\<rfloor>\<^sub>s\<^sub>D \<equiv> \<lfloor>\<lfloor>\<sigma>\<rfloor>\<^sub>S\<^sub>D\<rfloor>\<^sub>s"

subsection {*UTP-Relations drop*}

abbreviation drop_cpa_pre_uexpr ("\<lfloor>_\<rfloor>\<^sub><\<^sub>D")
where "\<lfloor>P\<rfloor>\<^sub><\<^sub>D \<equiv> \<lfloor>\<lfloor>P\<rfloor>\<^sub>D\<rfloor>\<^sub><"

abbreviation drop_cpa_post_uexpr ("\<lfloor>_\<rfloor>\<^sub>>\<^sub>D")
  where "\<lfloor>P\<rfloor>\<^sub>>\<^sub>D \<equiv> \<lfloor>\<lfloor>P\<rfloor>\<^sub>D\<rfloor>\<^sub>>"    
    
section{*Control flow statements*}    
  
subsection{*SKIP design*}  

abbreviation skip_des :: "('\<alpha>) hrel_des" ("SKIP\<^sub>D")
where "SKIP\<^sub>D \<equiv> skip_d"

subsection{*assign design*}
  
term "x :=\<^sub>D s"

subsection{*Conditional design*}

abbreviation IfD :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_des \<Rightarrow> ('\<alpha>) hrel_des \<Rightarrow> ('\<alpha>) hrel_des" ("bif\<^sub>D (_)/ then (_) else (_) eif")
where "bif\<^sub>D b then P else Q eif \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>D\<^sub>< \<triangleright> Q)"

subsection{*assert and assume*}

abbreviation assume_des :: "'\<alpha> upred \<Rightarrow> ('\<alpha>) hrel_des" ("_\<^sup>\<top>\<^sup>D" [999] 999) where
 "assume_des c \<equiv> (bif\<^sub>D c then SKIP\<^sub>D else \<top>\<^sub>D eif)"

abbreviation assert_des :: "'\<alpha> upred \<Rightarrow> ('\<alpha>) hrel_des" ("_\<^sub>\<bottom>\<^sub>D" [999] 999) where
 "assert_des c \<equiv> (bif\<^sub>D c then SKIP\<^sub>D else \<bottom>\<^sub>D eif)"

subsection{*Scoping*}

definition blockD ("bob\<^sub>D INIT (_) BODY /(_) RESTORE /(_) RETURN/(_) eob") where
[urel_defs]:
  "bob\<^sub>D INIT init BODY body RESTORE restore RETURN return eob= 
    Abs_uexpr (\<lambda>(s, s'). 
        \<lbrakk>init ;; body ;; 
         Abs_uexpr (\<lambda>(t, t').\<lbrakk>restore (s, s') (t, t');; return(s, s') (t, t')\<rbrakk>\<^sub>e (t, t'))\<rbrakk>\<^sub>e (s, s'))" 

subsection{*Loops*}
  
definition While_gfp_des :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_des \<Rightarrow> ('\<alpha>) hrel_des" ("while\<^sup>\<top>\<^sup>D _ do _ od") where
"while\<^sup>\<top>\<^sup>D b do B od = (\<nu>\<^sub>D X \<bullet> bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)"


definition While_lfp_des :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_des \<Rightarrow> ('\<alpha>) hrel_des" ("while\<^sub>\<bottom>\<^sub>D _ do _ od") where
"while\<^sub>\<bottom>\<^sub>D b do B od =  (\<mu>\<^sub>D X \<bullet> bif\<^sub>D b then (B ;; X) else SKIP\<^sub>D eif)"

purge_notation while_top ("while _ do _ od")

abbreviation While_bot_des :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_des \<Rightarrow> ('\<alpha>) hrel_des" ("while _ do _ od") where
"while b do B od \<equiv> while\<^sub>\<bottom>\<^sub>D b do B od"

subsection{*While-loop inv*}
text {*While loops with invariant decoration*}

purge_notation while_inv ("while _ invr _ do _ od" 71)

definition While_inv_des :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_des \<Rightarrow> ('\<alpha>) hrel_des" ("while _ invr _ do _ od") where
"while b invr p do S od = while b do S od"

declare While_gfp_des_def [urel_defs]
declare While_inv_des_def [urel_defs]
declare While_lfp_des_def [urel_defs]
  
  
section \<open>Algebraic laws AUX\<close>

subsection \<open>simpset\<close>
named_theorems udes_comp and udes_cond 
declare urel_comp [udes_comp]
declare urel_cond [udes_cond]  

    
subsection \<open>ok alphabet behavior\<close>
 

lemma unrest_pre_out\<alpha>_abr[unrest]: "out\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>D\<^sub><"
  by (rel_auto)

lemma unrest_post_in\<alpha>_abr[unrest]: "in\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>D\<^sub>>"
  by (rel_auto)

lemma unrest_ok_abrupt_rel_uexpr_lift_cpa[unrest]:
  "$ok \<sharp> \<lceil>P\<rceil>\<^sub>D" "$ok\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>D"
  by (pred_auto)+

lemma unrest_ok_abrupt_rel_usubst_lift_cpa[unrest]:
  "$ok\<acute> \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D" "$ok \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D"
  by rel_auto+

lemma unrest_in_out_rel_ok_abrupt_res_abr [unrest]:
  "$ok \<sharp> (P \<restriction>\<^sub>\<alpha> ok)" "$ok\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> ok)"
  by (simp_all add: rel_var_res_def unrest)

lemma rel_usubst_lift_cpa_in_out_abrupt_ok[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> ($ok) = ($ok)" "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> (\<not>$ok) = (\<not>$ok)"
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> ($ok\<acute>) = ($ok\<acute>)"  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> (\<not>$ok\<acute>) = (\<not>$ok\<acute>)"
  by (simp_all add: usubst unrest)

lemma abrupt_ok_simpl[unrest]:
  "(\<not>$ok;; (P \<turnstile> Q)) = (\<not>$ok)" 
  by rel_auto+

lemma in_ok:
  "($ok) = (utp_expr.var (ok ;\<^sub>L fst\<^sub>L)) "
  by rel_auto
    
lemma out_ok:
  "($ok\<acute>) = (utp_expr.var (ok ;\<^sub>L snd\<^sub>L)) "
  by rel_auto
    
subsection \<open>Healthiness condition behavior\<close>

subsection \<open>Signature behavior\<close>

lemma skip_des_def:
  "II = (\<lceil>II\<rceil>\<^sub>D \<and> $abrupt =\<^sub>u $abrupt\<acute> \<and> $ok =\<^sub>u $ok\<acute>)"
  by rel_auto
   
lemma skip_lift_des_def:
  "\<lceil>II\<rceil>\<^sub>D = ($\<Sigma>\<^sub>D\<acute> =\<^sub>u $\<Sigma>\<^sub>D)"
  by rel_auto 

lemma rel_usubst_lift_des_uexpr_lift_des[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> \<lceil>P\<rceil>\<^sub>D = \<lceil>\<sigma> \<dagger> P\<rceil>\<^sub>D"
  by rel_auto

lemma usubst_lift_des_assigns_lift_des[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>D \<dagger> \<lceil>\<langle>\<rho>\<rangle>\<^sub>a\<rceil>\<^sub>D = \<lceil>\<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>D"
  by (simp add: usubst)

lemma usubst_lift_des_pre_uexpr_lift_des[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>D \<dagger> \<lceil>b\<rceil>\<^sub>D\<^sub>< = \<lceil>\<sigma> \<dagger> b\<rceil>\<^sub>D\<^sub><"
  by (simp add: usubst)

lemma rel_usubst_lift_des_design[usubst]:
  "(\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> (Q \<turnstile> P)) = (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> Q) \<turnstile> (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>D \<dagger> P)"
  by (simp add: usubst unrest)

lemma rel_usubst_des_skip_des[usubst]:
  "(\<sigma> \<dagger> II) = ((\<sigma> \<dagger> \<lceil>II\<rceil>\<^sub>D) \<and> (\<sigma> \<dagger> $ok) =\<^sub>u (\<sigma> \<dagger> $ok\<acute>))"
  by rel_auto

lemma usubst_lift_des_skip_lift_des[usubst]:
  "(\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>D \<dagger> \<lceil>II\<rceil>\<^sub>D) = \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>D"
  unfolding skip_r_def
  by (simp add: usubst_lift_des_assigns_lift_des)

declare utp_designs.design_top_left_zero[udes_comp]

lemma assigns_lift_cpa_comp_rel_cpa[udes_comp]:
  assumes "$ok \<sharp> P"
  shows  "(\<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>D;; P) = (\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>D \<dagger> P)"
  apply (insert assms)
  apply rel_auto
  apply blast
done

declare utp_designs.assigns_d_comp[udes_comp]

lemma usubst_cpa_des_cond_abr[usubst]:
  "\<lbrakk> $ok \<sharp> \<sigma>; $ok\<acute> \<sharp> \<sigma> \<rbrakk> \<Longrightarrow>
    \<sigma> \<dagger> (R \<turnstile> bif\<^sub>D b then P else Q eif) =
    (\<sigma> \<dagger> R \<turnstile> (\<sigma> \<dagger> P \<triangleleft> \<sigma> \<dagger> \<lceil>b\<rceil>\<^sub>D\<^sub>< \<triangleright> \<sigma> \<dagger> Q))"
  by (simp add: usubst)
    
section {*Algebraic laws for designs*}

subsection Skip

text \<open>In this section we introduce the algebraic laws of programming related to the SKIP
      statement.\<close>

lemma true_left_zero_skip_cpaD[udes_comp]:
  "(SKIP\<^sub>D;; true) = (true)"
  by rel_auto

lemma true_liftD_left_zero_skipD[udes_comp]:
  "(SKIP\<^sub>D;; \<lceil>true\<rceil>\<^sub>D) = (\<lceil>true\<rceil>\<^sub>D)"
  by rel_auto

lemma false_liftD_left_zero_skipD[udes_comp]:
  "(SKIP\<^sub>D;; \<lceil>false\<rceil>\<^sub>D) = (\<lceil>false\<rceil>\<^sub>D)"
  by rel_auto

lemma skipD_left_unit_assignsD[udes_comp]:
  "(SKIP\<^sub>D;; \<langle>\<sigma>\<rangle>\<^sub>D) = (\<langle>\<sigma>\<rangle>\<^sub>D)"
  by rel_auto

lemma skipD_topD_left_zero[udes_comp]:
  "(SKIP\<^sub>D;; \<top>\<^sub>D) = (\<top>\<^sub>D)"
  by rel_auto

lemma skipDDupt_left_zero[udes_comp]:
  "($x;; SKIP\<^sub>D) = $x"
  by rel_auto

lemma skipD_bot_left_zero[udes_comp]:
  "(\<top>\<^sub>D;; SKIP\<^sub>D) = (\<top>\<^sub>D)"
  by rel_auto

lemma skip_d_alpha_eq:
  "SKIP\<^sub>D =  ($ok \<Rightarrow> ($ok\<acute> \<and> ($\<Sigma>\<^sub>D\<acute> =\<^sub>u $\<Sigma>\<^sub>D)))"
   by rel_simp

lemma simpl_pre_skip_d_post:
  "(\<lceil>b\<rceil>\<^sub>D\<^sub>< \<and> SKIP\<^sub>D =\<^sub>u $ok) = (SKIP\<^sub>D =\<^sub>u $ok \<and> \<lceil>b\<rceil>\<^sub>D\<^sub>>)"
  by rel_auto

lemma simpl_pre_skip_d_var:
  fixes x :: "(bool \<Longrightarrow> 'b des)"
  shows "($x \<and> SKIP\<^sub>D =\<^sub>u $ok) = (SKIP\<^sub>D =\<^sub>u $ok \<and> $x\<acute>)"
  by rel_auto

lemma skip_d_post_left_unit[udes_comp]:
  "(S \<turnstile> (SKIP\<^sub>D;; Q)) = (S \<turnstile> Q)"
  apply pred_simp
  apply rel_simp
  apply fastforce
done

subsection \<open>Assignment Laws\<close>
text \<open>In this section we introduce the algebraic laws of programming related to the assignment
      statement.\<close>

lemma [urel_cond]:
  "S \<turnstile> (\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<lceil>R\<rceil>\<^sub>D \<and> $b\<acute>);; (P \<triangleleft> \<not> $b \<triangleright> Q)) =
   S \<turnstile> (\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<lceil>R\<rceil>\<^sub>D \<and> $b\<acute>);; Q)"
  apply rel_simp
  apply fastforce
done

lemma [urel_cond]:
  "S \<turnstile> (\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<lceil>R\<rceil>\<^sub>D \<and> $b\<acute>);; (P \<triangleleft> $b \<triangleright> Q)) =
   S \<turnstile> (\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<lceil>R\<rceil>\<^sub>D \<and> $b\<acute>);; P)"
  apply pred_simp
  apply fastforce
done

lemma usubst_d_cancel [usubst]:
  assumes 1:"weak_lens v"
  shows "($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub>D\<^sub></$v\<rbrakk> = \<lceil>expr\<rceil>\<^sub>D\<^sub><"
  using 1
  by  rel_auto

lemma usubst_d_lift_cancel[usubst]:
  assumes 1:"weak_lens v"
  shows "\<lceil>($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub></$v\<rbrakk>\<rceil>\<^sub>D = \<lceil>expr\<rceil>\<^sub>D\<^sub><"
  using 1
  by  rel_auto

lemma assigns_d_id : "SKIP\<^sub>D = \<langle>id\<rangle>\<^sub>D"
  unfolding skip_d_def assigns_d_def
  by (rel_auto)
    
lemma assign_test[udes_comp]:
  assumes 1:"mwb_lens x"
  shows     "(x :=\<^sub>D \<guillemotleft>u\<guillemotright>;; x :=\<^sub>D \<guillemotleft>v\<guillemotright>) = (x :=\<^sub>D \<guillemotleft>v\<guillemotright>)"
  using 1
  by (simp add: usubst udes_comp)

lemma assign_d_left_comp_subst[udes_comp]:
  "(x :=\<^sub>D u;; (\<lceil>P\<rceil>\<^sub>D \<turnstile> \<lceil>Q\<rceil>\<^sub>D)) = (\<lceil>P\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>D \<turnstile> \<lceil>Q\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>D)"
  by rel_blast

lemma assign_d_twice[udes_comp]:
  assumes "mwb_lens x" and  "x \<sharp> f"
  shows "(x :=\<^sub>D e;; x :=\<^sub>D f) = (x :=\<^sub>D f)"
  using assms
  by (simp add: udes_comp usubst)

lemma assign_d_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x :=\<^sub>D e ;; y :=\<^sub>D f) = (y :=\<^sub>D f ;; x :=\<^sub>D e)"
  using assms
  by (simp add: udes_comp usubst usubst_upd_comm)

lemma assign_d_cond_d[udes_comp]: (*needs more laws to be automatic*)
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "(x :=\<^sub>D e ;; (bif\<^sub>D b then P\<^sub>1 \<turnstile> Q\<^sub>1 else P\<^sub>2 \<turnstile> Q\<^sub>2 eif)) =
         (bif\<^sub>D (b\<lbrakk>e/x\<rbrakk>) then (x :=\<^sub>D e;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (x :=\<^sub>D e ;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif)"
  apply (simp add: usubst udes_comp)
  apply rel_auto
done

lemma assign_d_uop1[udes_comp]:
  assumes 1: "mwb_lens v"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (uop F (&v))) = (v :=\<^sub>D (uop F e1))"
  by (simp add: usubst  udes_comp assms)

lemma assign_d_bop1[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (bop bp (&v) e2)) = (v :=\<^sub>D (bop bp e1 e2))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_bop2[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (bop bp e2 (&v))) = (v :=\<^sub>D (bop bp e2 e1))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_trop1[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (trop tp (&v) e2 e3)) =
         (v :=\<^sub>D (trop tp e1 e2 e3))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_trop2[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (trop tp e2 (&v) e3)) =
         (v :=\<^sub>D (trop tp e2 e1 e3))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_trop3[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (trop tp e2 e3 (&v))) =
         (v :=\<^sub>D (trop tp e2 e3 e1))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_qtop1[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (qtop tp (&v) e2 e3 e4)) =
         (v :=\<^sub>D (qtop tp e1 e2 e3 e4))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_qtop2[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (qtop tp e2 (&v) e3 e4)) =
         (v :=\<^sub>D (qtop tp e2 e1 e3 e4))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_qtop3[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (qtop tp e2 e3 (&v) e4)) =
         (v :=\<^sub>D (qtop tp e2 e3 e1 e4))"
  by (simp add: usubst udes_comp assms)

lemma assign_d_qtop4[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :=\<^sub>D e1;; v :=\<^sub>D (qtop tp e2 e3 e4 (&v))) =
         (v :=\<^sub>D (qtop tp e2 e3 e4 e1))"
  by (simp add: usubst udes_comp assms)

text \<open>In the sequel we define assignment laws proposed by Hoare\<close>

lemma assign_d_vwb_skip_d[udes_comp]:
  assumes 1: "vwb_lens v"
  shows "(v :=\<^sub>D &v) = SKIP\<^sub>D"
  by (simp add: assms usubst)

lemma assign_c_simultaneous:
  assumes  1: "vwb_lens var2"
  and      2: "var1 \<bowtie> var2"
  shows "var1, var2 :=\<^sub>D expr, &var2 = var1 :=\<^sub>D expr"
  by (simp add: assms usubst_upd_comm usubst)

lemma assign_d_seq[udes_comp]:
  assumes  1: "vwb_lens var2"
  shows"(var1 :=\<^sub>D expr);; (var2 :=\<^sub>D &var2) = (var1 :=\<^sub>D expr)"
  using assms by rel_blast
    
lemma assign_d_cond_d_uop[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v"
  shows "bif\<^sub>D uop F expr then (v :=\<^sub>D expr;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr ;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
          v :=\<^sub>D expr;; bif\<^sub>D uop F (&v) then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms
  by (simp add: assign_d_cond_d subst_uop usubst_cancel)  

lemma assign_d_cond_bop1[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif\<^sub>D bop bp expr exp2 then (v :=\<^sub>D expr;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
          v :=\<^sub>D expr;; bif\<^sub>D bop bp (&v) exp2 then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms
  by (simp add: assign_d_cond_d subst_bop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_d_cond_bop2[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif\<^sub>D bop bp exp2 expr then (v :=\<^sub>D expr;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
          v :=\<^sub>D expr;; bif\<^sub>D bop bp exp2 (&v) then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_bop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_cond_trop1[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif\<^sub>D trop bp expr exp2 exp3 then (v :=\<^sub>D expr;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
         v :=\<^sub>D expr;; bif\<^sub>D trop bp (&v) exp2 exp3 then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_trop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_cond_trop2[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif\<^sub>D trop bp exp2 expr exp3 then (v :=\<^sub>D expr;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
         v :=\<^sub>D expr;; bif\<^sub>D trop bp  exp2 (&v) exp3 then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_trop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_cond_trop3[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif\<^sub>D trop bp exp2 exp3 expr then (v :=\<^sub>D expr;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
         v :=\<^sub>D expr;; bif\<^sub>D trop bp exp2 exp3 (&v) then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_trop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_cond_qtop1[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif\<^sub>D qtop bp expr exp2 exp3 exp4 then (v :=\<^sub>D expr;; (P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
         v :=\<^sub>D expr;; bif\<^sub>D qtop bp (&v) exp2 exp3 exp4 then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_qtop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_d_cond_qtop2[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4:"v \<sharp> exp4"
  shows "bif\<^sub>D qtop bp exp2 expr  exp3 exp4 then (v :=\<^sub>D expr;;(P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
         v :=\<^sub>D expr;; bif\<^sub>D qtop bp exp2 (&v) exp3 exp4 then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_qtop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_d_cond_qtop3[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif\<^sub>D qtop bp exp2 exp3 expr exp4 then (v :=\<^sub>D expr;;(P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
         v :=\<^sub>D expr;; bif\<^sub>D qtop bp exp2 exp3 (&v) exp4 then(P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_qtop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_d_cond_qtop4[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif\<^sub>D qtop bp exp2 exp3 exp4 expr then (v :=\<^sub>D expr;;(P\<^sub>1 \<turnstile> Q\<^sub>1)) else (v :=\<^sub>D expr;; (P\<^sub>2 \<turnstile> Q\<^sub>2)) eif =
         v :=\<^sub>D expr;; bif\<^sub>D qtop bp exp2  exp3 exp4 (&v) then (P\<^sub>1 \<turnstile> Q\<^sub>1) else (P\<^sub>2 \<turnstile> Q\<^sub>2) eif"
  using assms  
  by (simp add: assign_d_cond_d subst_qtop subst_to_singleton(2) subst_unrest usubst_cancel)

lemma assign_d_cond_If [udes_cond]:
  "(bif\<^sub>D bexp then (v :=\<^sub>D exp1) else (v :=\<^sub>D exp2) eif) =
   (v :=\<^sub>D (exp1 \<triangleleft> bexp \<triangleright> exp2))"
  by rel_auto

subsection \<open>While laws\<close>
text \<open>In this section we introduce the algebraic laws of programming related to the while
      statement.\<close>

theorem while_unfold:
  "while b do P od = (bif b then (P;; while b do P od) else SKIP\<^sub>D eif)"
proof -
  have m:"mono (\<lambda>X. bif b then (P;; X) else SKIP\<^sub>D eif)"
    by (auto intro: monoI seqr_mono if_mono)
  have "(while b do P od) = (\<nu> X \<bullet> bif b then (P;; X) else SKIP\<^sub>D eif)"
    by (simp add: While_def)
  also have "... = (bif b then (P;; (\<nu> X \<bullet> bif b then (P;; X) else SKIP\<^sub>D eif)) else SKIP\<^sub>D eif)"
    by (subst lfp_unfold,simp_all add:m)
  also have "... = (bif b then (P;; while b do P od) else SKIP\<^sub>D eif)"
    by (simp add: While_def)
  finally show ?thesis .
qed

lemma while_true:
  shows "(while true do (P\<turnstile>Q) od) = false"(*it should eq to \<top>\<^sub>D*)
  apply (simp add: While_def alpha)
   apply (rule antisym)
  apply (simp_all)
  apply (rule lfp_lowerbound)
  apply (simp)
  done
    
lemma while_false:
  shows "(while false do P od) = SKIP\<^sub>D"
proof -
  have "(while false do P od) = bif false then (P;; while false do P od) else SKIP\<^sub>D eif"
    using while_unfold[of _ P] by simp
  also have "... = SKIP\<^sub>D" by rel_blast
  finally show ?thesis .
qed

lemma while_inv_unfold:
  "(while b invr p do P od) = (bif b then (P ;; (while b invr p do P od)) else SKIP\<^sub>D eif)"
  unfolding While_inv_def using while_unfold
  by auto

theorem while_bot_unfold:
  "while\<^sub>\<bottom> b do P od = (bif b then (P;; while\<^sub>\<bottom> b do P od) else SKIP\<^sub>D eif)"
proof -
  have m:"mono (\<lambda>X. bif b then (P;; X) else SKIP\<^sub>D eif)"
    by (auto intro: monoI seqr_mono if_mono)
  have "(while\<^sub>\<bottom> b do P od) = (\<mu> X \<bullet> bif b then (P;; X) else SKIP\<^sub>D eif)"
    by (simp add: While_bot_def)
  also have "... = (bif b then (P;; (\<mu> X \<bullet> bif b then (P;; X) else SKIP\<^sub>D eif)) else SKIP\<^sub>D eif)"
    by (subst gfp_unfold, simp_all add: m)
  also have "... = (bif b then (P;; while\<^sub>\<bottom> b do P od) else SKIP\<^sub>D eif)"
    by (simp add: While_bot_def)
  finally show ?thesis .
qed

theorem while_bot_false: "while\<^sub>\<bottom> false do P od = SKIP\<^sub>D"
  by (simp add: While_bot_def mu_const alpha)

theorem while_bot_true: "while\<^sub>\<bottom> true do P od = (\<mu> X \<bullet> (P;; X))"
  by (simp add: While_bot_def alpha)

subsection \<open>assume laws\<close>

lemma assume_twice[udes_comp]: "(b\<^sup>\<top>\<^sup>C;; c\<^sup>\<top>\<^sup>C) = (b \<and> c)\<^sup>\<top>\<^sup>C"
  apply pred_simp
  apply auto
  apply (rel_simp)+
  apply blast
  apply (rel_simp)+
  apply (metis (full_types))
done

lemma assert_twice[udes_comp]: "(b\<^sub>\<bottom>\<^sub>C;; c\<^sub>\<bottom>\<^sub>C) = (b \<and> c)\<^sub>\<bottom>\<^sub>C"
  apply pred_simp
  apply auto
  apply (rel_simp)+
  apply blast
  apply (rel_simp)+
  apply (metis (full_types))
done

subsection \<open>Try Catch laws\<close>
(*see utp_hoare_helper*)
section {*Hoare logic for designs*}  
  
end