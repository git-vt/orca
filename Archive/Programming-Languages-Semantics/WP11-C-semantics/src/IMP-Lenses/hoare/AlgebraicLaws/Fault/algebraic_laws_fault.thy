
section "Algebraic laws for abrupt designs"
theory algebraic_laws_fault
imports algebraic_laws_fault_aux

begin
(*TODO: add laws for assigns when composed with try catch...*)
subsection"Simpset configuration"

declare urel_comp [uflt_comp]
declare urel_cond [uflt_cond]

subsection"Skip"

text{*In this section we introduce the algebraic laws of programming related to the SKIP
      statement.*}

lemma true_left_zero_skip_cpf_abr[uflt_comp]:
  "(SKIP\<^sub>F\<^sub>L\<^sub>T ;; true) = (true)"
  by rel_auto

lemma true_lift_flt_right_zero_skip_flt[uflt_comp]:
  "(SKIP\<^sub>F\<^sub>L\<^sub>T ;; \<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T) = (\<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T)"
  by rel_auto

lemma false_lift_flt_right_zero[uflt_comp]:
  "(P ;; \<lceil>false\<rceil>\<^sub>F\<^sub>L\<^sub>T) = (\<lceil>false\<rceil>\<^sub>F\<^sub>L\<^sub>T)"
  by rel_auto

lemma skip_flt_left_unit_assigns_flt[uflt_comp]:
  "(SKIP\<^sub>F\<^sub>L\<^sub>T ;; \<langle>\<sigma>\<rangle>\<^sub>F\<^sub>L\<^sub>T) = (\<langle>\<sigma>\<rangle>\<^sub>F\<^sub>L\<^sub>T)"
  by rel_auto

lemma top_flt_right_zero_skip_flt[uflt_comp]:
  "(SKIP\<^sub>F\<^sub>L\<^sub>T ;; \<top>\<^sub>F\<^sub>L\<^sub>T) = (\<top>\<^sub>F\<^sub>L\<^sub>T)"
  by rel_auto

lemma ivar_left_zero_skip_flt[uflt_comp]: 
  "($x ;; SKIP\<^sub>F\<^sub>L\<^sub>T) = $x" 
  by rel_auto 

lemma top_flt_left_zero_skip_flt[uflt_comp]: 
  "(\<top>\<^sub>F\<^sub>L\<^sub>T ;; SKIP\<^sub>F\<^sub>L\<^sub>T) = (\<top>\<^sub>F\<^sub>L\<^sub>T)" 
  by rel_auto

lemma skip_flt_idem [uflt_comp]:
  "(SKIP\<^sub>F\<^sub>L\<^sub>T ;; SKIP\<^sub>F\<^sub>L\<^sub>T) = SKIP\<^sub>F\<^sub>L\<^sub>T"
  by rel_auto

lemma skip_flt_alpha_eq:
  "SKIP\<^sub>F\<^sub>L\<^sub>T = Simpl\<^sub>F\<^sub>L\<^sub>T (\<not>$fault\<acute> \<and> ($\<Sigma>\<^sub>F\<^sub>L\<^sub>T\<acute> =\<^sub>u $\<Sigma>\<^sub>F\<^sub>L\<^sub>T))"
  by rel_auto

lemma simpl_pre_skip_flt_post:
  "(Simpl\<^sub>F\<^sub>L\<^sub>T \<lceil>b\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub>< \<and> SKIP\<^sub>F\<^sub>L\<^sub>T) = (SKIP\<^sub>F\<^sub>L\<^sub>T \<and> Simpl\<^sub>F\<^sub>L\<^sub>T \<lceil>b\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub>>)"
  by rel_auto 

lemma simpl_pre_skip_flt_var:
  fixes x :: "(bool,  ('b) cpf) uvar"
  shows "(Simpl\<^sub>F\<^sub>L\<^sub>T $x \<and> SKIP\<^sub>F\<^sub>L\<^sub>T) = (SKIP\<^sub>F\<^sub>L\<^sub>T \<and> Simpl\<^sub>F\<^sub>L\<^sub>T $x\<acute>)"
  by rel_auto

lemma skip_flt_post_left_unit[uflt_comp]:
  "(S \<turnstile> (SKIP\<^sub>F\<^sub>L\<^sub>T;; Q)) = (S \<turnstile> Q)"
  apply pred_simp 
  apply rel_simp
  apply fastforce
done

lemma simpl_flt_post_left_unit[uflt_comp]:
  "(S \<turnstile> (Simpl\<^sub>F\<^sub>L\<^sub>T (\<not>$fault\<acute> \<and> \<lceil>II\<rceil>\<^sub>F\<^sub>L\<^sub>T);; Q)) = (S \<turnstile> Q)"
  apply pred_simp 
  apply rel_simp
  apply transfer
  apply auto
done


subsection {*Assignment Laws*}
text{*In this section we introduce the algebraic laws of programming related to the assignment
      statement.*}


lemma design_post_seqr_assigns_flt_condr_fault_L6_left[urel_cond]:
  "((S \<turnstile> (\<langle>a\<rangle>\<^sub>F\<^sub>L\<^sub>T;; (P \<triangleleft> $fault \<triangleright> Q))) \<triangleleft> \<not> $fault \<triangleright> R) = 
   ((S \<turnstile> (\<langle>a\<rangle>\<^sub>F\<^sub>L\<^sub>T;; Q)) \<triangleleft> \<not> $fault \<triangleright> R)"
  unfolding assigns_flt_def 
  apply pred_simp 
  apply fastforce
done

lemma  design_post_seqr_assigns_flt_condr_not_fault_L6_left[urel_cond]:
  "((S \<turnstile> (\<langle>a\<rangle>\<^sub>F\<^sub>L\<^sub>T;; (P \<triangleleft> \<not> $fault \<triangleright> Q))) \<triangleleft> $fault \<triangleright> R) = 
   ((S \<turnstile> (\<langle>a\<rangle>\<^sub>F\<^sub>L\<^sub>T;; Q)) \<triangleleft> $fault \<triangleright> R)"
  unfolding assigns_flt_def 
  apply pred_simp 
  apply rel_simp
  apply fastforce
done

lemma design_post_seqr_assigns_flt_condr_fault_L6_right[urel_cond]:
  "(R \<triangleleft> \<not> $fault \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>F\<^sub>L\<^sub>T;; (P \<triangleleft> $fault \<triangleright> Q)))) = 
   (R \<triangleleft> \<not> $fault \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>F\<^sub>L\<^sub>T;; P)))"
  unfolding assigns_flt_def 
  apply pred_simp 
  apply rel_simp
  apply fastforce
done

lemma design_post_seqr_assigns_flt_condr_not_fault_L6_right[urel_cond]:
 "(R \<triangleleft> $fault \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>F\<^sub>L\<^sub>T;; (P \<triangleleft> \<not> $fault \<triangleright> Q)))) = 
  (R \<triangleleft> $fault \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>F\<^sub>L\<^sub>T;; P)) )"
  apply pred_simp 
  apply rel_simp
  apply fastforce
done

lemma rcond_not_fault_subst_cancel_design_post_right[urel_cond]:
  "R \<triangleleft> \<not> $fault \<triangleright> (S \<turnstile> (\<langle>a\<rangle>\<^sub>F\<^sub>L\<^sub>T;; P))  = 
   R \<triangleleft> \<not> $fault \<triangleright> (S \<turnstile> (\<lceil>true\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> (\<lceil>II\<rceil>\<^sub>F\<^sub>L\<^sub>T \<and> $fault\<acute>) ;; P))"
  apply pred_simp 
  apply rel_simp
done

lemma usubst_flt_cancel [usubst]: 
  assumes 1:"weak_lens v" 
  shows "($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub></$v\<rbrakk>= \<lceil>expr\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub><"
  using 1
  by  rel_auto

lemma usubst_flt_lift_cancel[usubst]: 
  assumes 1:"weak_lens v" 
  shows "\<lceil>($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub></$v\<rbrakk>\<rceil>\<^sub>F\<^sub>L\<^sub>T= \<lceil>expr\<rceil>\<^sub>F\<^sub>L\<^sub>T\<^sub><"
  using 1
  by  rel_auto

lemma assigns_flt_id [uflt_simpl]: 
  "SKIP\<^sub>F\<^sub>L\<^sub>T = \<langle>id\<rangle>\<^sub>F\<^sub>L\<^sub>T"
  by (rel_auto)

lemma assign_test[uflt_comp]:
  assumes 1:"mwb_lens x" 
  shows     "(x \<Midarrow> \<guillemotleft>u\<guillemotright> ;; x \<Midarrow> \<guillemotleft>v\<guillemotright>) = (x \<Midarrow> \<guillemotleft>v\<guillemotright>)"
  using 1   
  by (simp add: usubst uflt_comp )

lemma assign_flt_left_comp_subst[uflt_comp]: 
  "(x \<Midarrow> u ;; Simpl\<^sub>F\<^sub>L\<^sub>T(\<lceil>P\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> \<lceil>Q\<rceil>\<^sub>F\<^sub>L\<^sub>T)) = Simpl\<^sub>F\<^sub>L\<^sub>T(\<lceil>P\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>F\<^sub>L\<^sub>T \<turnstile> \<lceil>Q\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>F\<^sub>L\<^sub>T)" 
  by (simp add: uflt_comp usubst)

lemma assign_flt_twice[uflt_comp]: 
  assumes "mwb_lens x" and  "x \<sharp> f" 
  shows "(x \<Midarrow> e ;; x \<Midarrow> f) = (x \<Midarrow> f)" 
  using assms
  by (simp add: uflt_comp usubst)
   
lemma assign_flt_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x \<Midarrow> e ;; y \<Midarrow> f) = (y \<Midarrow> f ;; x \<Midarrow> e)"
  using assms
  by (simp add: uflt_comp usubst usubst_upd_comm)

lemma assign_flt_cond_flt[uflt_comp]: (*needs more laws to be automatic*)
  fixes x :: "('a, '\<alpha>) uvar"
  shows "(x \<Midarrow> e ;; (bif b then Simpl\<^sub>F\<^sub>L\<^sub>T P else Simpl\<^sub>F\<^sub>L\<^sub>T Q eif)) = 
         (bif (b\<lbrakk>e/x\<rbrakk>) then (x \<Midarrow> e ;; Simpl\<^sub>F\<^sub>L\<^sub>T P)  else (x \<Midarrow> e ;; Simpl\<^sub>F\<^sub>L\<^sub>T Q) eif)"
  apply (simp add: usubst uflt_comp)
  apply rel_auto
done

lemma assign_flt_uop1[uflt_comp]: 
  assumes 1: "mwb_lens v"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (uop F (&v))) = (v \<Midarrow> (uop F e1))"
  by (simp add: usubst  uflt_comp assms)

lemma assign_flt_bop1[uflt_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow>(bop bp (&v) e2)) = (v \<Midarrow> (bop bp e1 e2))"
  by (simp add: usubst uflt_comp assms)
 
lemma assign_flt_bop2[uflt_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (bop bp e2 (&v))) = (v \<Midarrow> (bop bp e2 e1))"
  by (simp add: usubst uflt_comp assms)

lemma assign_flt_trop1[uflt_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (trop tp (&v) e2 e3)) = 
         (v \<Midarrow> (trop tp e1 e2 e3))"
  by (simp add: usubst uflt_comp assms)

lemma assign_flt_trop2[uflt_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (trop tp e2 (&v) e3)) = 
         (v \<Midarrow> (trop tp e2 e1 e3))"
  by (simp add: usubst uflt_comp assms)

lemma assign_flt_trop3[uflt_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (trop tp e2 e3 (&v))) = 
         (v \<Midarrow> (trop tp e2 e3 e1))"
  by (simp add: usubst uflt_comp assms)

lemma assign_flt_qtop1[uflt_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp (&v) e2 e3 e4)) = 
         (v \<Midarrow> (qtop tp e1 e2 e3 e4))"
  by (simp add: usubst uflt_comp assms)

lemma assign_flt_qtop2[uflt_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp e2 (&v) e3 e4)) = 
         (v \<Midarrow> (qtop tp e2 e1 e3 e4))"
  by (simp add: usubst uflt_comp assms)

lemma assign_flt_qtop3[uflt_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp e2 e3 (&v) e4)) = 
         (v \<Midarrow> (qtop tp e2 e3 e1 e4))"
  by (simp add: usubst uflt_comp assms)

lemma assign_flt_qtop4[uflt_comp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp e2 e3 e4 (&v))) = 
         (v \<Midarrow> (qtop tp e2 e3 e4 e1))"
  by (simp add: usubst uflt_comp assms)
                   
text {*In the sequel we define assignment laws proposed by Hoare*}

lemma assign_flt_vwb_skip_flt[uflt_comp]:
  assumes 1: "vwb_lens v"
  shows "(v \<Midarrow> &v) = SKIP\<^sub>F\<^sub>L\<^sub>T"
  by (simp add: assms usubst uflt_simpl)

lemma assign_flt_simultaneous:
  assumes  1: "vwb_lens var2"
  and      2: "var1 \<bowtie> var2"
  shows "var1, var2 \<Midarrow> exp, &var2 = var1 \<Midarrow> exp"
  by (simp add: assms usubst_upd_comm usubst)

lemma assign_flt_seq[uflt_comp]:
  assumes  1: "vwb_lens var2"
  shows"(var1 \<Midarrow> exp);; (var2 \<Midarrow> &var2) = (var1 \<Midarrow> exp)"
  by (simp add: assms usubst uflt_comp)

lemma assign_flt_cond_flt_uop[uflt_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v"
  shows "bif uop F exp then (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C1) else (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C2) eif = 
          v \<Midarrow> exp ;; bif uop F (&v) then Simpl\<^sub>F\<^sub>L\<^sub>T C1 else  Simpl\<^sub>F\<^sub>L\<^sub>T C2 eif"
  apply (simp add: assms usubst uflt_comp uflt_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms weak_lens.put_get)+
done

lemma assign_flt_cond_bop1[uflt_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif bop bp exp exp2 then (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C1) else (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C2) eif = 
          v \<Midarrow> exp ;; bif bop bp (&v) exp2 then Simpl\<^sub>F\<^sub>L\<^sub>T C1 else Simpl\<^sub>F\<^sub>L\<^sub>T C2 eif"
  apply (simp add: assms usubst uflt_comp uflt_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_flt_cond_bop2[uflt_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif bop bp exp2 exp then (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C1) else (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C2) eif = 
          v \<Midarrow> exp ;; bif bop bp  exp2 (&v) then Simpl\<^sub>F\<^sub>L\<^sub>T C1 else Simpl\<^sub>F\<^sub>L\<^sub>T C2 eif"
  apply (simp add: assms usubst uflt_comp uflt_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_flt_cond_trop1[uflt_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif trop bp exp exp2 exp3 then (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C1) else (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C2) eif = 
         v \<Midarrow> exp ;; bif trop bp (&v) exp2 exp3 then Simpl\<^sub>F\<^sub>L\<^sub>T C1 else Simpl\<^sub>F\<^sub>L\<^sub>T C2 eif"
  apply (simp add: assms usubst uflt_comp uflt_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_flt_cond_trop2[uflt_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif trop bp exp2 exp  exp3 then (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C1) else (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C2) eif = 
         v \<Midarrow> exp ;; bif trop bp  exp2 (&v) exp3 then Simpl\<^sub>F\<^sub>L\<^sub>T C1 else Simpl\<^sub>F\<^sub>L\<^sub>T C2 eif"
  apply (simp add: assms usubst uflt_comp uflt_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_flt_cond_trop3[uflt_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif trop bp exp2 exp3 exp then (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C1) else (v \<Midarrow> exp ;;Simpl\<^sub>F\<^sub>L\<^sub>T C2) eif = 
         v \<Midarrow> exp ;; bif trop bp exp2 exp3 (&v)  then Simpl\<^sub>F\<^sub>L\<^sub>T C1 else Simpl\<^sub>F\<^sub>L\<^sub>T C2 eif"
  apply (simp add: assms usubst uflt_comp uflt_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_flt_cond_qtop1[uflt_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif qtop bp exp exp2 exp3 exp4 then (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C1) else (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C2) eif = 
         v \<Midarrow> exp ;; bif qtop bp (&v) exp2 exp3 exp4 then Simpl\<^sub>F\<^sub>L\<^sub>T C1 else Simpl\<^sub>F\<^sub>L\<^sub>T C2 eif"
  apply (simp add: assms usubst uflt_comp uflt_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_flt_cond_qtop2[uflt_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4:"v \<sharp> exp4"
  shows "bif qtop bp exp2 exp  exp3 exp4 then (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C1) else (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C2) eif = 
         v \<Midarrow> exp ;; bif qtop bp exp2 (&v) exp3 exp4 then Simpl\<^sub>F\<^sub>L\<^sub>T C1 else Simpl\<^sub>F\<^sub>L\<^sub>T C2 eif"
  apply (simp add: assms usubst uflt_comp uflt_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_flt_cond_qtop3[uflt_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif qtop bp exp2 exp3 exp exp4 then (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C1) else (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C2) eif = 
         v \<Midarrow> exp ;; bif qtop bp exp2  exp3 (&v) exp4 then Simpl\<^sub>F\<^sub>L\<^sub>T C1 else Simpl\<^sub>F\<^sub>L\<^sub>T C2 eif"
  apply (simp add: assms usubst uflt_comp uflt_simpl )
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_flt_cond_qtop4[uflt_comp]: (*needs more laws to be automatic*)
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif qtop bp exp2 exp3 exp4 exp then (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C1) else (v \<Midarrow> exp ;; Simpl\<^sub>F\<^sub>L\<^sub>T C2) eif = 
         v \<Midarrow> exp ;; bif qtop bp exp2  exp3 exp4 (&v)  then Simpl\<^sub>F\<^sub>L\<^sub>T C1 else Simpl\<^sub>F\<^sub>L\<^sub>T C2 eif"
  apply (simp add: assms usubst uflt_comp uflt_simpl)
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis assms unrest_upred.rep_eq weak_lens.put_get)+
done

lemma assign_flt_cond_If [uflt_cond]: 
  "(bif bexp then (v \<Midarrow> exp1) else (v \<Midarrow> exp2) eif) = 
   (v \<Midarrow> (exp1 \<triangleleft> bexp \<triangleright> exp2))" 
  by rel_auto

subsection {*While laws*}
text{*In this section we introduce the algebraic laws of programming related to the while
      statement.*}

theorem while_unfold:
  "while b do P od = (bif b then (P ;; while b do P od) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)"
proof -
  have m:"mono (\<lambda>X. bif b then (P ;; X) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)"
    by (auto intro: monoI seqr_mono if_mono)
  have "(while b do P od) = (\<nu> X \<bullet> bif b then (P ;; X) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)"
    by (simp add: While_def)
  also have "... = (bif b then (P ;; (\<nu> X \<bullet> bif b then (P ;; X) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)"
    by (subst lfp_unfold,simp_all add:m )
  also have "... = (bif b then (P ;; while b do P od) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)"
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
  shows "(while false do P od) = SKIP\<^sub>F\<^sub>L\<^sub>T"
proof -
  have "(while false do P od) = bif false then (P ;; while false do P od) else SKIP\<^sub>F\<^sub>L\<^sub>T eif" 
    using while_unfold[of _ P] by simp
  also have "... = SKIP\<^sub>F\<^sub>L\<^sub>T" by rel_blast
  finally show ?thesis . 
qed

lemma while_inv_unfold:
  "while b invr p do P od = (bif b then (P ;; while b invr p do P od) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)"
  unfolding While_inv_def using while_unfold
  by auto

theorem while_bot_unfold:
  "while\<^sub>\<bottom> b do P od = (bif b then (P ;; while\<^sub>\<bottom> b do P od) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)"
proof -
  have m:"mono (\<lambda>X. bif b then (P ;; X) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)"
    by (auto intro: monoI seqr_mono if_mono)
  have "(while\<^sub>\<bottom> b do P od) = (\<mu> X \<bullet> bif b then (P ;; X) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)"
    by (simp add: While_bot_def)
  also have "... = (bif b then (P ;; (\<mu> X \<bullet> bif b then (P ;; X) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)"
    by (subst gfp_unfold, simp_all add: m)
  also have "... = (bif b then (P ;; while\<^sub>\<bottom> b do P od) else SKIP\<^sub>F\<^sub>L\<^sub>T eif)"
    by (simp add: While_bot_def)
  finally show ?thesis .
qed

theorem while_bot_false: "while\<^sub>\<bottom> false do P od = SKIP\<^sub>F\<^sub>L\<^sub>T"
  by (simp add: While_bot_def mu_const alpha)

theorem while_bot_true: "while\<^sub>\<bottom> true do P od = (\<mu> X \<bullet> (P ;; X))"
  by (simp add: While_bot_def alpha)

subsection {*assume laws*}

lemma assume_twice[uflt_comp]: "(b\<^sup>\<top>\<^sup>C ;; c\<^sup>\<top>\<^sup>C) = (b \<and> c)\<^sup>\<top>\<^sup>C"
  apply pred_simp 
  apply auto
  apply (rel_simp)+
  apply blast
  apply (rel_simp)+
  apply (metis (full_types))
done

lemma assert_twice[uflt_comp]: "(b\<^sub>\<bottom>\<^sub>C ;; c\<^sub>\<bottom>\<^sub>C) = (b \<and> c)\<^sub>\<bottom>\<^sub>C" 
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