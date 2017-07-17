
section "Algebraic laws for abrupt designs"
theory algebraic_laws_abrupt
imports algebraic_laws_abrupt_aux

begin
(*TODO: add laws for assigns when composed with try catch...*)
subsection"Simpset configuration"

declare urel_comp [uabr_comp]
declare urel_cond [uabr_cond]

subsection"Throw"

lemma throw_cpa_left_zero_true_abr[uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R ;; true) = (true)"
  by rel_auto

lemma throw_cpa_left_zero_true_lift_abr[uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R ;; \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R) = (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma throw_cpa_left_zero_false_lift_abr[uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R ;; \<lceil>false\<rceil>\<^sub>A\<^sub>B\<^sub>R) = (\<lceil>false\<rceil>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma throw_cpa_left_zero_skip_abr[uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R ;; SKIP\<^sub>A\<^sub>B\<^sub>R) = (THROW\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma throw_cpa_left_zero_assigns_abr[uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R ;; \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R) = (THROW\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

(*lemma throw_cpa_left_zero_top_abr[uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R ;; \<top>\<^sub>A\<^sub>B\<^sub>R) = (\<top>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto*)

lemma not_abrupt_left_zero_throw_abr[uabr_comp]: 
  "(($x) ;; THROW\<^sub>A\<^sub>B\<^sub>R) = ($x)" 
  by rel_auto 

lemma abrupt_left_zero_throw_abr[uabr_comp]: 
  "($aburpt ;; THROW\<^sub>A\<^sub>B\<^sub>R) = $aburpt" 
  by rel_auto 

lemma bot_left_zero_throw_abr[uabr_comp]: 
  "(\<top>\<^sub>A\<^sub>B\<^sub>R ;; THROW\<^sub>A\<^sub>B\<^sub>R) = (\<top>\<^sub>A\<^sub>B\<^sub>R)" 
  by rel_auto

(*lemma throw_abr_idem [uabr_comp]: 
  "(THROW\<^sub>A\<^sub>B\<^sub>R ;; THROW\<^sub>A\<^sub>B\<^sub>R) = THROW\<^sub>A\<^sub>B\<^sub>R" 
  by rel_auto*)

lemma throw_abr_right_zero_skip_abr[uabr_comp]: 
  "(SKIP\<^sub>A\<^sub>B\<^sub>R ;; THROW\<^sub>A\<^sub>B\<^sub>R) = THROW\<^sub>A\<^sub>B\<^sub>R" 
  by rel_auto 

(*lemma assigns_abr_throw_abr_right[uabr_comp]:
  "\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R;; THROW\<^sub>A\<^sub>B\<^sub>R = (C3_abr(\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> ($abrupt\<acute> \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R)))"
  by rel_auto

lemma assigns_abr_throw_abr_right[uabr_comp]:
  "\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R;; THROW\<^sub>A\<^sub>B\<^sub>R = (C3_abr(\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> ($abrupt\<acute> \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R))))"
  by rel_auto*)

subsection"Skip"

text{*In this section we introduce the algebraic laws of programming related to the SKIP
      statement.*}

lemma true_left_zero_skip_cpa_abr[uabr_comp]:
  "(SKIP\<^sub>A\<^sub>B\<^sub>R ;; true) = (true)"
  by rel_auto

lemma true_lift_abr_left_zero_skip_abr[uabr_comp]:
  "(SKIP\<^sub>A\<^sub>B\<^sub>R ;; \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R) = (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma false_lift_abr_left_zero_skip_abr[uabr_comp]:
  "(SKIP\<^sub>A\<^sub>B\<^sub>R ;; \<lceil>false\<rceil>\<^sub>A\<^sub>B\<^sub>R) = (\<lceil>false\<rceil>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma skip_abr_left_unit_assigns_abr[uabr_comp]:
  "(SKIP\<^sub>A\<^sub>B\<^sub>R ;; \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R) = (\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma skip_abr_top_abr_left_zero[uabr_comp]:
  "(SKIP\<^sub>A\<^sub>B\<^sub>R ;; \<top>\<^sub>A\<^sub>B\<^sub>R) = (\<top>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma skip_abr_abrupt_left_zero[uabr_comp]: 
  "($x ;; SKIP\<^sub>A\<^sub>B\<^sub>R) = $x" 
  by rel_auto 

lemma skip_abr_bot_left_zero[uabr_comp]: 
  "(\<top>\<^sub>A\<^sub>B\<^sub>R ;; SKIP\<^sub>A\<^sub>B\<^sub>R) = (\<top>\<^sub>A\<^sub>B\<^sub>R)" 
  by rel_auto

lemma skip_abr_idem [uabr_comp]:
  "(SKIP\<^sub>A\<^sub>B\<^sub>R ;; SKIP\<^sub>A\<^sub>B\<^sub>R) = SKIP\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto

lemma skip_abr_alpha_eq:
  "SKIP\<^sub>A\<^sub>B\<^sub>R = Simpl\<^sub>A\<^sub>B\<^sub>R (\<not>$abrupt\<acute> \<and> ($\<Sigma>\<^sub>A\<^sub>B\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>A\<^sub>B\<^sub>R))"
  by (simp add: skip_lift_cpa_def skip_abr_def)

lemma simpl_pre_skip_abr_post:
  "(Simpl\<^sub>A\<^sub>B\<^sub>R \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<and> SKIP\<^sub>A\<^sub>B\<^sub>R) = (SKIP\<^sub>A\<^sub>B\<^sub>R \<and> Simpl\<^sub>A\<^sub>B\<^sub>R \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>>)"
  by rel_auto 

lemma simpl_pre_skip_abr_var:
  fixes x :: "(bool,  ('b) cpa) uvar"
  shows "(Simpl\<^sub>A\<^sub>B\<^sub>R $x \<and> SKIP\<^sub>A\<^sub>B\<^sub>R) = (SKIP\<^sub>A\<^sub>B\<^sub>R \<and> Simpl\<^sub>A\<^sub>B\<^sub>R $x\<acute>)"
  by rel_auto

lemma  skip_abr_post_left_unit[uabr_comp]:
  "(S \<turnstile> (SKIP\<^sub>A\<^sub>B\<^sub>R;; Q)) = (S \<turnstile> Q)"
  apply pred_simp 
  apply rel_simp
  apply fastforce
done

lemma  simpl_post_left_unit[uabr_comp]:
  "(S \<turnstile> (Simpl\<^sub>A\<^sub>B\<^sub>R (\<not>$abrupt\<acute> \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R);; Q)) = (S \<turnstile> Q)"
  apply pred_simp 
  apply rel_simp
  apply transfer
  apply auto
done


subsection {*Assignment Laws*}
text{*In this section we introduce the algebraic laws of programming related to the assignment
      statement.*}

lemma [urel_cond]:
  "S \<turnstile> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>R\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and> $abrupt\<acute>) ;; P \<triangleleft> \<not> $abrupt \<triangleright> Q) = 
   S \<turnstile> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>R\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and> $abrupt\<acute>);; Q)"
  apply pred_simp
  apply fastforce 
done

lemma [urel_cond]:
  "S \<turnstile> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>R\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and>  $abrupt\<acute>) ;; P \<triangleleft> $abrupt \<triangleright> Q) = 
   S \<turnstile> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>R\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and>  $abrupt\<acute>);; P)"
  apply pred_simp
  apply fastforce 
done

lemma not_abrupt_assigns_abr_L6_left_des[urel_cond]:
  "((S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; (P \<triangleleft> $abrupt \<triangleright> Q))) \<triangleleft> \<not> $abrupt \<triangleright> R) = 
   ((S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; Q)) \<triangleleft> \<not> $abrupt \<triangleright> R)"
  unfolding assigns_abr_def 
  apply pred_simp 
  apply fastforce
done

lemma abrupt_assigns_abr_L6_left_des[urel_cond]:
  "((S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; (P \<triangleleft> \<not> $abrupt \<triangleright> Q))) \<triangleleft> $abrupt \<triangleright> R) = 
   ((S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; Q)) \<triangleleft> $abrupt \<triangleright> R)"
  unfolding assigns_abr_def 
  apply pred_simp 
  apply rel_simp
  apply fastforce
done

lemma not_abrupt_assigns_abr_L6_right_des[urel_cond]:
  "(R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; (P \<triangleleft> $abrupt \<triangleright> Q))) ) = 
   ( R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; P)))"
  unfolding assigns_abr_def 
  apply pred_simp 
  apply rel_simp
  apply fastforce
done

lemma abrupt_assigns_abr_L6_right_des[urel_cond]:
 "( R \<triangleleft> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; (P \<triangleleft> \<not> $abrupt \<triangleright> Q))) ) = 
  ( R \<triangleleft> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; P)) )"
  apply pred_simp 
  apply rel_simp
  apply fastforce
done

lemma not_abrupt_left_assigns_abr_post_des[urel_cond]:
  "R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; P))  = 
   R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and> $abrupt\<acute>) ;; P))"
  unfolding assigns_abr_def 
  apply pred_simp 
  apply rel_simp
done

lemma  not_abrupt_left_throw_abr_post_des[urel_cond]:
  "R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> (THROW\<^sub>A\<^sub>B\<^sub>R;; P))  = 
   R \<triangleleft> \<not> $abrupt \<triangleright> (S \<turnstile> ((\<not>$abrupt) \<turnstile> (\<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and> $abrupt\<acute>) ;; P))"  
  unfolding assigns_abr_def 
  apply pred_simp 
  apply rel_simp
done

lemma usubst_abr_cancel [usubst]: 
  assumes 1:"weak_lens v" 
  shows "($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub></$v\<rbrakk>= \<lceil>expr\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><"
  using 1
  by  rel_auto

lemma usubst_abr_lift_cancel[usubst]: 
  assumes 1:"weak_lens v" 
  shows "\<lceil>($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub></$v\<rbrakk>\<rceil>\<^sub>A\<^sub>B\<^sub>R= \<lceil>expr\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><"
  using 1
  by  rel_auto

lemma assigns_abr_id [uabr_simpl]: "SKIP\<^sub>A\<^sub>B\<^sub>R = \<langle>id\<rangle>\<^sub>A\<^sub>B\<^sub>R"
  unfolding skip_abr_def assigns_abr_def
  by (rel_auto)

lemma assign_test[uabr_comp]:
  assumes 1:"mwb_lens x" 
  shows     "(x \<Midarrow> \<guillemotleft>u\<guillemotright> ;; x \<Midarrow> \<guillemotleft>v\<guillemotright>) = (x \<Midarrow> \<guillemotleft>v\<guillemotright>)"
  using 1   
  by (simp add: usubst uabr_comp )

lemma assign_abr_left_comp_subst[uabr_comp]: 
  "(x \<Midarrow> u ;; Simpl\<^sub>A\<^sub>B\<^sub>R(\<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> \<lceil>Q\<rceil>\<^sub>A\<^sub>B\<^sub>R)) = Simpl\<^sub>A\<^sub>B\<^sub>R(\<lceil>P\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> \<lceil>Q\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>A\<^sub>B\<^sub>R)" 
  by (simp add: uabr_comp usubst)

lemma assign_abr_twice[uabr_comp]: 
  assumes "mwb_lens x" and  "x \<sharp> f" 
  shows "(x \<Midarrow> e ;; x \<Midarrow> f) = (x \<Midarrow> f)" 
  using assms
  by (simp add: uabr_comp usubst)
   
lemma assign_abr_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x \<Midarrow> e ;; y \<Midarrow> f) = (y \<Midarrow> f ;; x \<Midarrow> e)"
  using assms
  by (simp add: uabr_comp usubst usubst_upd_comm)

lemma assign_abr_cond_abr[uabr_comp]: (*needs more laws to be automatic*)
  fixes x :: "('a, '\<alpha>) uvar"
  shows "(x \<Midarrow> e ;; (bif b then Simpl\<^sub>A\<^sub>B\<^sub>R P else Simpl\<^sub>A\<^sub>B\<^sub>R Q eif)) = 
         (bif (b\<lbrakk>e/x\<rbrakk>) then (x \<Midarrow> e ;; Simpl\<^sub>A\<^sub>B\<^sub>R P)  else (x \<Midarrow> e ;; Simpl\<^sub>A\<^sub>B\<^sub>R Q) eif)"
  apply (simp add: usubst uabr_comp)
  apply rel_auto
done

lemma assign_c_uop1[uabr_comp]: 
  assumes 1: "mwb_lens v"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (uop F (&v))) = (v \<Midarrow> (uop F e1))"
  by (simp add: usubst  uabr_comp assms)

lemma assign_c_bop1[uabr_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow>(bop bp (&v) e2)) = (v \<Midarrow> (bop bp e1 e2))"
  by (simp add: usubst uabr_comp assms)
 
lemma assign_c_bop2[uabr_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (bop bp e2 (&v))) = (v \<Midarrow> (bop bp e2 e1))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_trop1[uabr_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (trop tp (&v) e2 e3)) = 
         (v \<Midarrow> (trop tp e1 e2 e3))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_trop2[uabr_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (trop tp e2 (&v) e3)) = 
         (v \<Midarrow> (trop tp e2 e1 e3))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_trop3[uabr_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (trop tp e2 e3 (&v))) = 
         (v \<Midarrow> (trop tp e2 e3 e1))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_qtop1[uabr_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp (&v) e2 e3 e4)) = 
         (v \<Midarrow> (qtop tp e1 e2 e3 e4))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_qtop2[uabr_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp e2 (&v) e3 e4)) = 
         (v \<Midarrow> (qtop tp e2 e1 e3 e4))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_qtop3[uabr_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp e2 e3 (&v) e4)) = 
         (v \<Midarrow> (qtop tp e2 e3 e1 e4))"
  by (simp add: usubst uabr_comp assms)

lemma assign_c_qtop4[uabr_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp e2 e3 e4 (&v))) = 
         (v \<Midarrow> (qtop tp e2 e3 e4 e1))"
  by (simp add: usubst uabr_comp assms)
                   
text {*In the sequel we define assignment laws proposed by Hoare*}

lemma assign_abr_vwb_skip_abr[uabr_comp]:
  assumes 1: "vwb_lens v"
  shows "(v \<Midarrow> &v) = SKIP\<^sub>A\<^sub>B\<^sub>R"
  by (simp add: assms usubst uabr_simpl)

lemma assign_c_simultaneous:
  assumes  1: "vwb_lens var2"
  and      2: "var1 \<bowtie> var2"
  shows "var1, var2 \<Midarrow> exp, &var2 = var1 \<Midarrow> exp"
  by (simp add: assms usubst_upd_comm usubst)

lemma assign_c_seq[uabr_comp]:
  assumes  1: "vwb_lens var2"
  shows"(var1 \<Midarrow> exp);; (var2 \<Midarrow> &var2) = (var1 \<Midarrow> exp)"
  by (simp add: assms usubst uabr_comp)

lemma assign_c_cond_c_uop[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v"
  shows "bif uop F exp then (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif = 
          v \<Midarrow> exp ;; bif uop F (&v) then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else  Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  apply (simp add: assms usubst uabr_comp uabr_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms weak_lens.put_get)+
done

lemma assign_c_cond_bop1[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif bop bp exp exp2 then (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif = 
          v \<Midarrow> exp ;; bif bop bp (&v) exp2 then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  apply (simp add: assms usubst uabr_comp uabr_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_c_cond_bop2[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif bop bp exp2 exp then (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif = 
          v \<Midarrow> exp ;; bif bop bp  exp2 (&v) then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  apply (simp add: assms usubst uabr_comp uabr_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_cond_trop1[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif trop bp exp exp2 exp3 then (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif = 
         v \<Midarrow> exp ;; bif trop bp (&v) exp2 exp3 then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  apply (simp add: assms usubst uabr_comp uabr_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_cond_trop2[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif trop bp exp2 exp  exp3 then (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif = 
         v \<Midarrow> exp ;; bif trop bp  exp2 (&v) exp3 then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  apply (simp add: assms usubst uabr_comp uabr_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_cond_trop3[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif trop bp exp2 exp3 exp then (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v \<Midarrow> exp ;;Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif = 
         v \<Midarrow> exp ;; bif trop bp exp2 exp3 (&v)  then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  apply (simp add: assms usubst uabr_comp uabr_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_cond_qtop1[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif qtop bp exp exp2 exp3 exp4 then (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif = 
         v \<Midarrow> exp ;; bif qtop bp (&v) exp2 exp3 exp4 then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  apply (simp add: assms usubst uabr_comp uabr_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_c_cond_qtop2[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4:"v \<sharp> exp4"
  shows "bif qtop bp exp2 exp  exp3 exp4 then (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif = 
         v \<Midarrow> exp ;; bif qtop bp exp2 (&v) exp3 exp4 then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  apply (simp add: assms usubst uabr_comp uabr_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_c_cond_qtop3[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif qtop bp exp2 exp3 exp exp4 then (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif = 
         v \<Midarrow> exp ;; bif qtop bp exp2  exp3 (&v) exp4 then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  apply (simp add: assms usubst uabr_comp uabr_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_c_cond_qtop4[uabr_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif qtop bp exp2 exp3 exp4 exp then (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C1) else (v \<Midarrow> exp ;; Simpl\<^sub>A\<^sub>B\<^sub>R C2) eif = 
         v \<Midarrow> exp ;; bif qtop bp exp2  exp3 exp4 (&v)  then Simpl\<^sub>A\<^sub>B\<^sub>R C1 else Simpl\<^sub>A\<^sub>B\<^sub>R C2 eif"
  apply (simp add: assms usubst uabr_comp uabr_simpl)
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_c_cond_If [uabr_cond]: 
  "(bif bexp then (v \<Midarrow> exp1) else (v \<Midarrow> exp2) eif) = 
   (v \<Midarrow> (exp1 \<triangleleft> bexp \<triangleright> exp2))" 
  by rel_auto

subsection {*While laws*}
text{*In this section we introduce the algebraic laws of programming related to the while
      statement.*}

theorem while_unfold:
  "while b do P od = (bif b then (P ;; while b do P od) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"
proof -
  have m:"mono (\<lambda>X. bif b then (P ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"
    by (auto intro: monoI seqr_mono if_mono)
  have "(while b do P od) = (\<nu> X \<bullet> bif b then (P ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"
    by (simp add: While_def)
  also have "... = (bif b then (P ;; (\<nu> X \<bullet> bif b then (P ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"
    by (subst lfp_unfold,simp_all add:m )
  also have "... = (bif b then (P ;; while b do P od) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"
    by (simp add: While_def)
  finally show ?thesis .
qed


(*lemma while_true:
  shows "(while true do P od) = \<top>\<^sub>A\<^sub>B\<^sub>R"
  apply (simp add: While_def alpha)
  apply (rule antisym)
  apply (simp_all)
  apply (rule conjI)
  apply (rule lfp_lowerbound)
  apply (simp add: C3_abr_def design_def cond_def)
  apply rel_auto
  apply (frule cond_mono)
done*)

lemma while_false:
  shows "(while false do P od) = SKIP\<^sub>A\<^sub>B\<^sub>R"
proof -
  have "(while false do P od) = bif false then (P ;; while false do P od) else SKIP\<^sub>A\<^sub>B\<^sub>R eif" 
    using while_unfold[of _ P] by simp
  also have "... = SKIP\<^sub>A\<^sub>B\<^sub>R" by rel_blast
  finally show ?thesis . 
qed

lemma while_inv_unfold:
  "while b invr p do P od = (bif b then (P ;; while b invr p do P od) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"
  unfolding While_inv_def using while_unfold
  by auto

theorem while_bot_unfold:
  "while\<^sub>\<bottom> b do P od = (bif b then (P ;; while\<^sub>\<bottom> b do P od) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"
proof -
  have m:"mono (\<lambda>X. bif b then (P ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"
    by (auto intro: monoI seqr_mono if_mono)
  have "(while\<^sub>\<bottom> b do P od) = (\<mu> X \<bullet> bif b then (P ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"
    by (simp add: While_bot_def)
  also have "... = (bif b then (P ;; (\<mu> X \<bullet> bif b then (P ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"
    by (subst gfp_unfold, simp_all add: m)
  also have "... = (bif b then (P ;; while\<^sub>\<bottom> b do P od) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"
    by (simp add: While_bot_def)
  finally show ?thesis .
qed

theorem while_bot_false: "while\<^sub>\<bottom> false do P od = SKIP\<^sub>A\<^sub>B\<^sub>R"
  by (simp add: While_bot_def mu_const alpha)

theorem while_bot_true: "while\<^sub>\<bottom> true do P od = (\<mu> X \<bullet> (P ;; X))"
  by (simp add: While_bot_def alpha)

subsection {*assume laws*}

lemma assume_twice[uabr_comp]: "(b\<^sup>\<top>\<^sup>C ;; c\<^sup>\<top>\<^sup>C) = (b \<and> c)\<^sup>\<top>\<^sup>C"
  apply pred_simp 
  apply auto
  apply (rel_simp)+
  apply blast
  apply (rel_simp)+
  apply (metis (full_types))
done

lemma assert_twice[uabr_comp]: "(b\<^sub>\<bottom>\<^sub>C ;; c\<^sub>\<bottom>\<^sub>C) = (b \<and> c)\<^sub>\<bottom>\<^sub>C" 
  apply pred_simp 
  apply auto
  apply (rel_simp)+
  apply blast
  apply (rel_simp)+
  apply (metis (full_types))
done

subsection {*Try Catch laws*}
(*see utp_hoare_helper*)


end