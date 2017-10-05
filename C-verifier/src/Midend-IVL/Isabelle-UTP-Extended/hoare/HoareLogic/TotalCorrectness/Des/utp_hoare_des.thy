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

abbreviation If_abr :: "'\<alpha> cond \<Rightarrow> ('\<alpha>) hrel_des \<Rightarrow> ('\<alpha>) hrel_des \<Rightarrow> ('\<alpha>) hrel_des" ("bif\<^sub>D (_)/ then (_) else (_) eif")
where "bif\<^sub>D b then P else Q eif \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>D\<^sub>< \<triangleright> Q)"

subsection{*assert and assume*}

abbreviation assume_des :: "'\<alpha> upred \<Rightarrow> ('\<alpha>) hrel_des" ("_\<^sup>\<top>\<^sup>D" [999] 999) where
 "assume_des c \<equiv> (bif\<^sub>D c then SKIP\<^sub>D else \<top>\<^sub>D eif)"

abbreviation assert_des :: "'\<alpha> upred \<Rightarrow> ('\<alpha>) hrel_des" ("_\<^sub>\<bottom>\<^sub>D" [999] 999) where
 "assert_des c \<equiv> (bif\<^sub>D c then SKIP\<^sub>D else \<bottom>\<^sub>D eif)"

subsection{*Scoping*}

definition block_abr ("bob\<^sub>D INIT (_) BODY /(_) RESTORE /(_) RETURN/(_) eob") where
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
  
lemma skip_lift_des_def:
  "\<lceil>II\<rceil>\<^sub>D = ($\<Sigma>\<^sub>D\<acute> =\<^sub>u $\<Sigma>\<^sub>D)"
  by rel_auto  
    
section {*Algebraic laws for designs*}
subsection \<open>simpset\<close>
named_theorems udes_comp  
subsection Skip

text \<open>In this section we introduce the algebraic laws of programming related to the SKIP
      statement.\<close>

lemma true_left_zero_skip_cpa_abr[udes_comp]:
  "(SKIP\<^sub>D;; true) = (true)"
  by rel_auto

lemma true_lift_abr_left_zero_skip_abr[udes_comp]:
  "(SKIP\<^sub>D;; \<lceil>true\<rceil>\<^sub>D) = (\<lceil>true\<rceil>\<^sub>D)"
  by rel_auto

lemma false_lift_abr_left_zero_skip_abr[udes_comp]:
  "(SKIP\<^sub>D;; \<lceil>false\<rceil>\<^sub>D) = (\<lceil>false\<rceil>\<^sub>D)"
  by rel_auto

lemma skip_abr_left_unit_assigns_abr[udes_comp]:
  "(SKIP\<^sub>D;; \<langle>\<sigma>\<rangle>\<^sub>D) = (\<langle>\<sigma>\<rangle>\<^sub>D)"
  by rel_auto

lemma skip_abr_top_abr_left_zero[udes_comp]:
  "(SKIP\<^sub>D;; \<top>\<^sub>D) = (\<top>\<^sub>D)"
  by rel_auto

lemma skip_abr_abrupt_left_zero[udes_comp]:
  "($x;; SKIP\<^sub>D) = $x"
  by rel_auto

lemma skip_abr_bot_left_zero[udes_comp]:
  "(\<top>\<^sub>D;; SKIP\<^sub>D) = (\<top>\<^sub>D)"
  by rel_auto

lemma skip_abr_idem [udes_comp]:
  "(SKIP\<^sub>D;; SKIP\<^sub>D) = SKIP\<^sub>D"
  by rel_auto

lemma skip_abr_alpha_eq:
  "SKIP\<^sub>D =  ($ok \<Rightarrow> ($ok\<acute> \<and> ($\<Sigma>\<^sub>D\<acute> =\<^sub>u $\<Sigma>\<^sub>D)))"
   by rel_simp

lemma simpl_pre_skip_abr_post:
  "(\<lceil>b\<rceil>\<^sub>D\<^sub>< \<and> SKIP\<^sub>D) = (SKIP\<^sub>D \<and> \<lceil>b\<rceil>\<^sub>D\<^sub>>)"
  by rel_auto

lemma simpl_pre_skip_abr_var:
  fixes x :: "(bool \<Longrightarrow> 'b cpa)"
  shows "(Simpl\<^sub>D $x \<and> SKIP\<^sub>D) = (SKIP\<^sub>D \<and> Simpl\<^sub>D $x\<acute>)"
  by rel_auto

lemma skip_abr_post_left_unit[udes_comp]:
  "(S \<turnstile> (SKIP\<^sub>D;; Q)) = (S \<turnstile> Q)"
  apply pred_simp
  apply rel_simp
  apply fastforce
done

lemma simpl_post_left_unit[udes_comp]:
  "(S \<turnstile> (Simpl\<^sub>D (\<not>$abrupt\<acute> \<and> \<lceil>II\<rceil>\<^sub>D);; Q)) = (S \<turnstile> Q)"
  apply pred_simp
  apply rel_simp
  apply transfer
  apply auto
done

subsection \<open>Assignment Laws\<close>
text \<open>In this section we introduce the algebraic laws of programming related to the assignment
      statement.\<close>

lemma [urel_cond]:
  "S \<turnstile> (\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<lceil>R\<rceil>\<^sub>D \<and> $abrupt\<acute>);; (P \<triangleleft> \<not> $abrupt \<triangleright> Q)) =
   S \<turnstile> (\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<lceil>R\<rceil>\<^sub>D \<and> $abrupt\<acute>);; Q)"
  apply rel_simp
  apply fastforce
done

lemma [urel_cond]:
  "S \<turnstile> (\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<lceil>R\<rceil>\<^sub>D \<and> $abrupt\<acute>);; (P \<triangleleft> $abrupt \<triangleright> Q)) =
   S \<turnstile> (\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<lceil>R\<rceil>\<^sub>D \<and> $abrupt\<acute>);; P)"
  apply pred_simp
  apply fastforce
done

lemma not_abrupt_assigns_abr_L6_left_des[urel_cond]:
  "((S \<turnstile> (\<langle>a\<rangle>\<^sub>D;; (P \<triangleleft> $abrupt \<triangleright> Q))) \<triangleleft> \<not> $abrupt \<triangleright> R) =
   ((S \<turnstile> (\<langle>a\<rangle>\<^sub>D;; Q)) \<triangleleft> \<not> $abrupt \<triangleright> R)"
  unfolding assigns_abr_def
  apply pred_simp
  apply fastforce
done

lemma abrupt_assigns_abr_L6_left_des[urel_cond]:
  "((S \<turnstile> (\<langle>a\<rangle>\<^sub>D;; (P \<triangleleft> \<not> $abrupt \<triangleright> Q))) \<triangleleft> $abrupt \<triangleright> R) =
   ((S \<turnstile> (\<langle>a\<rangle>\<^sub>D;; Q)) \<triangleleft> $abrupt \<triangleright> R)"
  unfolding assigns_abr_def
  apply pred_simp
  apply rel_simp
  apply fastforce
done

lemma not_abrupt_assigns_abr_L6_right_des[urel_cond]:
  "(R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>D;; (P \<triangleleft> $abrupt \<triangleright> Q)))) =
   (R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>D;; P)))"
  unfolding assigns_abr_def
  apply pred_simp
  apply rel_simp
  apply fastforce
done

lemma abrupt_assigns_abr_L6_right_des[urel_cond]:
 "(R \<triangleleft> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>D;; (P \<triangleleft> \<not> $abrupt \<triangleright> Q)))) =
  (R \<triangleleft> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>D;; P)))"
  apply pred_simp
  apply rel_simp
  apply fastforce
done

lemma not_abrupt_left_assigns_abr_post_des[urel_cond]:
  "R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>D;; P)) =
   R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> ((\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<lceil>II\<rceil>\<^sub>D \<and> $abrupt\<acute>));; P))"
  unfolding assigns_abr_def
  apply pred_simp
  apply rel_simp 
done

lemma  not_abrupt_left_throw_abr_post_des[urel_cond]:
  "R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> (THROW\<^sub>D;; P))  =
   R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> ((\<not>$abrupt) \<turnstile> (\<lceil>II\<rceil>\<^sub>D \<and> $abrupt\<acute>));; P)"
  unfolding assigns_abr_def
  apply pred_simp
  apply rel_simp
done

lemma usubst_abr_cancel [usubst]:
  assumes 1:"weak_lens v"
  shows "($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub>D\<^sub></$v\<rbrakk> = \<lceil>expr\<rceil>\<^sub>D\<^sub><"
  using 1
  by  rel_auto

lemma usubst_abr_lift_cancel[usubst]:
  assumes 1:"weak_lens v"
  shows "\<lceil>($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub></$v\<rbrakk>\<rceil>\<^sub>D = \<lceil>expr\<rceil>\<^sub>D\<^sub><"
  using 1
  by  rel_auto

lemma assigns_abr_id [uabr_simpl]: "SKIP\<^sub>D = \<langle>id\<rangle>\<^sub>D"
  unfolding skip_abr_def assigns_abr_def
  by (rel_auto)

lemma assign_test[udes_comp]:
  assumes 1:"mwb_lens x"
  shows     "(x \<Midarrow> \<guillemotleft>u\<guillemotright>;; x \<Midarrow> \<guillemotleft>v\<guillemotright>) = (x \<Midarrow> \<guillemotleft>v\<guillemotright>)"
  using 1
  by (simp add: usubst udes_comp)

lemma assign_abr_left_comp_subst[udes_comp]:
  "(x \<Midarrow> u;; Simpl\<^sub>D(\<lceil>P\<rceil>\<^sub>D \<turnstile> \<lceil>Q\<rceil>\<^sub>D)) = Simpl\<^sub>D(\<lceil>P\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>D \<turnstile> \<lceil>Q\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>D)"
  by (simp add: udes_comp usubst)

lemma assign_abr_twice[udes_comp]:
  assumes "mwb_lens x" and  "x \<sharp> f"
  shows "(x \<Midarrow> e;; x \<Midarrow> f) = (x \<Midarrow> f)"
  using assms
  by (simp add: udes_comp usubst)

lemma assign_abr_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x \<Midarrow> e;; y \<Midarrow> f) = (y \<Midarrow> f;; x \<Midarrow> e)"
  using assms
  by (simp add: udes_comp usubst usubst_upd_comm)

lemma assign_abr_cond_abr[udes_comp]: (*needs more laws to be automatic*)
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "(x \<Midarrow> e;; (bif b then Simpl\<^sub>D P else Simpl\<^sub>D Q eif)) =
         (bif (b\<lbrakk>e/x\<rbrakk>) then (x \<Midarrow> e;; Simpl\<^sub>D P)  else (x \<Midarrow> e;; Simpl\<^sub>D Q) eif)"
  apply (simp add: usubst udes_comp)
  apply rel_auto
done

lemma assign_c_uop1[udes_comp]:
  assumes 1: "mwb_lens v"
  shows "(v \<Midarrow> e1;; v \<Midarrow> (uop F (&v))) = (v \<Midarrow> (uop F e1))"
  by (simp add: usubst  udes_comp assms)

lemma assign_c_bop1[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v \<Midarrow> e1;; v \<Midarrow>(bop bp (&v) e2)) = (v \<Midarrow> (bop bp e1 e2))"
  by (simp add: usubst udes_comp assms)

lemma assign_c_bop2[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v \<Midarrow> e1;; v \<Midarrow> (bop bp e2 (&v))) = (v \<Midarrow> (bop bp e2 e1))"
  by (simp add: usubst udes_comp assms)

lemma assign_c_trop1[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1;; v \<Midarrow> (trop tp (&v) e2 e3)) =
         (v \<Midarrow> (trop tp e1 e2 e3))"
  by (simp add: usubst udes_comp assms)

lemma assign_c_trop2[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1;; v \<Midarrow> (trop tp e2 (&v) e3)) =
         (v \<Midarrow> (trop tp e2 e1 e3))"
  by (simp add: usubst udes_comp assms)

lemma assign_c_trop3[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1;; v \<Midarrow> (trop tp e2 e3 (&v))) =
         (v \<Midarrow> (trop tp e2 e3 e1))"
  by (simp add: usubst udes_comp assms)

lemma assign_c_qtop1[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1;; v \<Midarrow> (qtop tp (&v) e2 e3 e4)) =
         (v \<Midarrow> (qtop tp e1 e2 e3 e4))"
  by (simp add: usubst udes_comp assms)

lemma assign_c_qtop2[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1;; v \<Midarrow> (qtop tp e2 (&v) e3 e4)) =
         (v \<Midarrow> (qtop tp e2 e1 e3 e4))"
  by (simp add: usubst udes_comp assms)

lemma assign_c_qtop3[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1;; v \<Midarrow> (qtop tp e2 e3 (&v) e4)) =
         (v \<Midarrow> (qtop tp e2 e3 e1 e4))"
  by (simp add: usubst udes_comp assms)

lemma assign_c_qtop4[udes_comp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1;; v \<Midarrow> (qtop tp e2 e3 e4 (&v))) =
         (v \<Midarrow> (qtop tp e2 e3 e4 e1))"
  by (simp add: usubst udes_comp assms)

text \<open>In the sequel we define assignment laws proposed by Hoare\<close>

lemma assign_abr_vwb_skip_abr[udes_comp]:
  assumes 1: "vwb_lens v"
  shows "(v \<Midarrow> &v) = SKIP\<^sub>D"
  by (simp add: assms usubst uabr_simpl)

lemma assign_c_simultaneous:
  assumes  1: "vwb_lens var2"
  and      2: "var1 \<bowtie> var2"
  shows "var1, var2 \<Midarrow> expr, &var2 = var1 \<Midarrow> expr"
  by (simp add: assms usubst_upd_comm usubst)

lemma assign_c_seq[udes_comp]:
  assumes  1: "vwb_lens var2"
  shows"(var1 \<Midarrow> expr);; (var2 \<Midarrow> &var2) = (var1 \<Midarrow> expr)"
  by (simp add: assms usubst udes_comp)

lemma assign_c_cond_c_uop[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v"
  shows "bif uop F expr then (v \<Midarrow> expr;; Simpl\<^sub>D C1) else (v \<Midarrow> expr;; Simpl\<^sub>D C2) eif =
          v \<Midarrow> expr;; bif uop F (&v) then Simpl\<^sub>D C1 else Simpl\<^sub>D C2 eif"
  apply (simp add: assms usubst udes_comp uabr_simpl)
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms weak_lens.put_get)+
done

lemma assign_c_cond_bop1[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif bop bp expr exp2 then (v \<Midarrow> expr;; Simpl\<^sub>D C1) else (v \<Midarrow> expr;; Simpl\<^sub>D C2) eif =
          v \<Midarrow> expr;; bif bop bp (&v) exp2 then Simpl\<^sub>D C1 else Simpl\<^sub>D C2 eif"
  apply (simp add: assms usubst udes_comp uabr_simpl)
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis "1" "2" unrest_uexpr.rep_eq weak_lens.put_get)+
done

lemma assign_c_cond_bop2[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif bop bp exp2 expr then (v \<Midarrow> expr;; Simpl\<^sub>D C1) else (v \<Midarrow> expr;; Simpl\<^sub>D C2) eif =
          v \<Midarrow> expr;; bif bop bp  exp2 (&v) then Simpl\<^sub>D C1 else Simpl\<^sub>D C2 eif"
  apply (simp add: assms usubst udes_comp uabr_simpl)
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_uexpr.rep_eq weak_lens.put_get)+
done

lemma assign_cond_trop1[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif trop bp expr exp2 exp3 then (v \<Midarrow> expr;; Simpl\<^sub>D C1) else (v \<Midarrow> expr;; Simpl\<^sub>D C2) eif =
         v \<Midarrow> expr;; bif trop bp (&v) exp2 exp3 then Simpl\<^sub>D C1 else Simpl\<^sub>D C2 eif"
  apply (simp add: assms usubst udes_comp uabr_simpl)
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_uexpr.rep_eq weak_lens.put_get)+
done

lemma assign_cond_trop2[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif trop bp exp2 expr exp3 then (v \<Midarrow> expr;; Simpl\<^sub>D C1) else (v \<Midarrow> expr;; Simpl\<^sub>D C2) eif =
         v \<Midarrow> expr;; bif trop bp  exp2 (&v) exp3 then Simpl\<^sub>D C1 else Simpl\<^sub>D C2 eif"
  apply (simp add: assms usubst udes_comp uabr_simpl)
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_uexpr.rep_eq weak_lens.put_get)+
done

lemma assign_cond_trop3[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif trop bp exp2 exp3 expr then (v \<Midarrow> expr;; Simpl\<^sub>D C1) else (v \<Midarrow> expr;; Simpl\<^sub>D C2) eif =
         v \<Midarrow> expr;; bif trop bp exp2 exp3 (&v) then Simpl\<^sub>D C1 else Simpl\<^sub>D C2 eif"
  apply (simp add: assms usubst udes_comp uabr_simpl)
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_uexpr.rep_eq weak_lens.put_get)+
done

lemma assign_cond_qtop1[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif qtop bp expr exp2 exp3 exp4 then (v \<Midarrow> expr;; Simpl\<^sub>D C1) else (v \<Midarrow> expr;; Simpl\<^sub>D C2) eif =
         v \<Midarrow> expr;; bif qtop bp (&v) exp2 exp3 exp4 then Simpl\<^sub>D C1 else Simpl\<^sub>D C2 eif"
  apply (simp add: assms usubst udes_comp uabr_simpl)
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_uexpr.rep_eq weak_lens.put_get)+
done

lemma assign_c_cond_qtop2[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4:"v \<sharp> exp4"
  shows "bif qtop bp exp2 expr  exp3 exp4 then (v \<Midarrow> expr;; Simpl\<^sub>D C1) else (v \<Midarrow> expr;; Simpl\<^sub>D C2) eif =
         v \<Midarrow> expr;; bif qtop bp exp2 (&v) exp3 exp4 then Simpl\<^sub>D C1 else Simpl\<^sub>D C2 eif"
  apply (simp add: assms usubst udes_comp uabr_simpl)
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_uexpr.rep_eq weak_lens.put_get)+
done

lemma assign_c_cond_qtop3[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif qtop bp exp2 exp3 expr exp4 then (v \<Midarrow> expr;; Simpl\<^sub>D C1) else (v \<Midarrow> expr;; Simpl\<^sub>D C2) eif =
         v \<Midarrow> expr;; bif qtop bp exp2 exp3 (&v) exp4 then Simpl\<^sub>D C1 else Simpl\<^sub>D C2 eif"
  apply (simp add: assms usubst udes_comp uabr_simpl)
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_uexpr.rep_eq weak_lens.put_get)+
done

lemma assign_c_cond_qtop4[udes_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif qtop bp exp2 exp3 exp4 expr then (v \<Midarrow> expr;; Simpl\<^sub>D C1) else (v \<Midarrow> expr;; Simpl\<^sub>D C2) eif =
         v \<Midarrow> expr;; bif qtop bp exp2  exp3 exp4 (&v) then Simpl\<^sub>D C1 else Simpl\<^sub>D C2 eif"
  apply (simp add: assms usubst udes_comp uabr_simpl)
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_uexpr.rep_eq weak_lens.put_get)+
done

lemma assign_c_cond_If [uabr_cond]:
  "(bif bexp then (v \<Midarrow> exp1) else (v \<Midarrow> exp2) eif) =
   (v \<Midarrow> (exp1 \<triangleleft> bexp \<triangleright> exp2))"
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