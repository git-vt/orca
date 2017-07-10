
section "Algebraic laws for designs"
theory algebraic_laws_designs
imports "../theories/utp_fault_designs"

begin
named_theorems symbolic_exec_cp

subsection"Throw"

lemma throw_left_zero[simp]: 
  "(THROW ;; Simpl P) = THROW" 
  by rel_auto blast+

lemma throw_right_zero_skip[simp]: 
  "(SKIP ;; THROW) = THROW " 
  by rel_auto blast+

lemma throw_idem [simp]: 
  "(THROW ;; THROW) = THROW " 
  by rel_auto blast+

subsection"Skip"

text{*In this section we introduce the algebraic laws of programming related to the SKIP
      statement.*}

lemma skip_c_idem [simp]:
  "(SKIP ;; SKIP) = SKIP"
  by rel_auto blast+

lemma skip_c_left_unit[simp]: 
  "(SKIP ;;  Simpl P) =  Simpl P"
  by rel_auto (blast, metis) 

lemma skip_c_right_unit[simp]: 
  "(Simpl P  ;;  SKIP) =  Simpl P"  
  by rel_auto (metis option.exhaust_sel)+

lemma skip_c_lift_alpha_eq:
  "\<lceil>II\<rceil>\<^sub>C = ($\<Sigma>\<^sub>C\<acute> =\<^sub>u $\<Sigma>\<^sub>C)"
  by rel_auto

lemma skip_c_alpha_eq:
  "SKIP = Simpl (\<not>$abrupt\<acute> \<and> \<not>$stuck\<acute> \<and> \<not>$fault\<acute> \<and>$fault_tr\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> ($\<Sigma>\<^sub>C\<acute> =\<^sub>u $\<Sigma>\<^sub>C))"
  by (simp add: skip_c_lift_alpha_eq skip_c_def)

lemma pre_skip_c_post: 
  "(Simpl \<lceil>b\<rceil>\<^sub>C\<^sub>< \<and> SKIP) = (SKIP \<and> Simpl \<lceil>b\<rceil>\<^sub>C\<^sub>>)"
  by rel_auto 

lemma skip_c_var:
  fixes x :: "(bool, ('a, 'b) cp) uvar"
  shows "(Simpl $x \<and> SKIP) = (SKIP \<and> Simpl $x\<acute>)"
  by rel_auto

lemma assigns_c_id [simp]: "\<langle>id\<rangle>\<^sub>C = SKIP"
  by (rel_auto)

lemma assign_c_alt_def [symbolic_exec_cp]: 
  "\<langle>\<sigma>\<rangle>\<^sub>C = Simpl (\<not>$abrupt\<acute> \<and>\<not>$stuck\<acute> \<and> \<not>$fault\<acute> \<and>$fault_tr\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> II\<rceil>\<^sub>C)"
  by rel_auto

subsection {*Assignment Laws*}
text{*In this section we introduce the algebraic laws of programming related to the assignment
      statement.*}

lemma usubst_c_cancel [usubst,symbolic_exec_cp]: 
  assumes 1:"weak_lens v" 
  shows "($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub>C\<^sub></$v\<rbrakk>= \<lceil>expr\<rceil>\<^sub>C\<^sub><"
  using 1
  by  rel_auto

lemma usubst_c_lift_cancel[usubst,symbolic_exec_cp]: 
  assumes 1:"weak_lens v" 
  shows "\<lceil>($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub></$v\<rbrakk>\<rceil>\<^sub>C= \<lceil>expr\<rceil>\<^sub>C\<^sub><"
  using 1
  by  rel_auto

lemma assigns_c_comp: "(\<langle>f\<rangle>\<^sub>C ;; \<langle>g\<rangle>\<^sub>C) = \<langle>g \<circ> f\<rangle>\<^sub>C"
  by rel_auto blast+

lemma assign_test[symbolic_exec_cp]:
  assumes 1:"mwb_lens x" 
  shows     "(x \<Midarrow> \<guillemotleft>u\<guillemotright> ;; x \<Midarrow> \<guillemotleft>v\<guillemotright>) = (x \<Midarrow> \<guillemotleft>v\<guillemotright>)"
  using 1   
  by (simp add: assigns_c_comp subst_upd_comp subst_lit usubst_upd_idem)

lemma assign_c_left_comp: 
  "(\<langle>\<sigma>\<rangle>\<^sub>C ;; Simpl(\<lceil>P\<rceil>\<^sub>C \<turnstile> \<lceil>Q\<rceil>\<^sub>C)) = Simpl(\<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P\<rceil>\<^sub>C \<turnstile> \<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> Q\<rceil>\<^sub>C)"
  by rel_auto blast+

lemma assign_c_left_comp_subst[symbolic_exec_cp]: 
  "(x \<Midarrow> u ;; Simpl(\<lceil>P\<rceil>\<^sub>C \<turnstile> \<lceil>Q\<rceil>\<^sub>C)) = Simpl(\<lceil>P\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>C \<turnstile> \<lceil>Q\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>\<rceil>\<^sub>C)" 
  by rel_auto blast+

lemma assign_c_twice[symbolic_exec_cp]: 
  assumes "mwb_lens x" and  "x \<sharp> f" 
  shows "(x \<Midarrow> e ;; x \<Midarrow> f) = (x \<Midarrow> f)" 
  using assms
  by (simp add: assigns_c_comp usubst)

lemma assign_c_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x \<Midarrow> e ;; y \<Midarrow> f) = (y \<Midarrow> f ;; x \<Midarrow> e)"
proof -
  have "(x :== e ;; y :== f ) = y :== f ;; x :== e"
    using assms assign_commute by auto 
  then show ?thesis
    using assigns_c_comp assigns_c_def utp_urel_laws.assigns_comp
    by metis
qed

lemma assign_c_cond_c[symbolic_exec_cp]:
   fixes x :: "('a, '\<alpha>) uvar"
  shows "(x \<Midarrow> e ;; (bif b then Simpl P else Simpl Q eif)) = 
         (bif (b\<lbrakk>e/x\<rbrakk>) then (x \<Midarrow> e ;; Simpl P)  else (x \<Midarrow> e ;; Simpl Q) eif)"
   
  (*apply rel_auto  apply (metis option.distinct(1)*)
oops


lemma assign_c_uop1[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (uop F (&v))) = (v \<Midarrow> (uop F e1))"
  by (simp add: assigns_c_comp assms subst_uop subst_upd_comp subst_var 
                usubst_lookup_upd usubst_upd_idem)


lemma assign_c_bop1[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow>(bop bp (&v) e2)) = (v \<Midarrow> (bop bp e1 e2))"
  using 1 2  
  by rel_auto (blast, metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_bop2[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (bop bp e2 (&v))) = (v \<Midarrow> (bop bp e2 e1))"
  using 1 2  
  by rel_auto (blast, metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_trop1[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (trop tp (&v) e2 e3)) = 
         (v \<Midarrow> (trop tp e1 e2 e3))"
  using 1 2 3
  by rel_auto (blast, metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_trop2[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (trop tp e2 (&v) e3)) = 
         (v \<Midarrow> (trop tp e2 e1 e3))"
  using 1 2 3
  by rel_auto (blast, metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_trop3[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (trop tp e2 e3 (&v))) = 
         (v \<Midarrow> (trop tp e2 e3 e1))"
  using 1 2 3
  by rel_auto (blast, metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_qtop1[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp (&v) e2 e3 e4)) = 
         (v \<Midarrow> (qtop tp e1 e2 e3 e4))"
  using 1 2 3 4
  by rel_auto (blast, metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_qtop2[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp e2 (&v) e3 e4)) = 
         (v \<Midarrow> (qtop tp e2 e1 e3 e4))"
  using 1 2 3 4
  by rel_auto (blast, metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_qtop3[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp e2 e3 (&v) e4)) = 
         (v \<Midarrow> (qtop tp e2 e3 e1 e4))"
  using 1 2 3 4
  by rel_auto (blast, metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_qtop4[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp e2 e3 e4 (&v))) = 
         (v \<Midarrow> (qtop tp e2 e3 e4 e1))"
  using 1 2 3 4
  by rel_auto (blast, metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)
 
lemma assign_c_cond_seqr_dist[symbolic_exec_cp]:
  "(bif (b\<lbrakk>e/v\<rbrakk>) then (v \<Midarrow> e ;; Simpl P) else (v \<Midarrow> e ;; Simpl Q) eif) = 
   (v \<Midarrow> e ;; bif b then Simpl P else Simpl Q eif)"
  by (metis assign_c_cond_c) 

text {*In the sequel we define assignment laws proposed by Hoare*}

lemma assign_c_vwb_skip_c:
  assumes 1: "vwb_lens v"
  shows "(v \<Midarrow> &v) = SKIP"
  by (simp add: assms  usubst_upd_var_id)

lemma assign_c_simultaneous:
  assumes  1: "vwb_lens var2"
  and      2: "var1 \<bowtie> var2"
  shows "var1, var2 \<Midarrow> exp, &var2 = var1 \<Midarrow> exp"
  by (simp add: "1" "2" usubst_upd_comm usubst_upd_var_id)

lemma assign_c_seq:
  assumes  1: "vwb_lens var2"
  shows"(var1 \<Midarrow> exp);; (var2 \<Midarrow> &var2) = (var1 \<Midarrow> exp)"
  using 1 by rel_auto (blast, metis)

lemma assign_c_cond_c_uop[symbolic_exec_cp]:
  assumes 1: "weak_lens v"
  shows "bif uop F exp then (v \<Midarrow> exp ;; Simpl C1) else (v \<Midarrow> exp ;; Simpl C2) eif = 
          v \<Midarrow> exp ;; bif uop F (&v) then Simpl C1 else Simpl C2 eif"
proof -
  have "uop F exp = uop F ((&v::('a, 'b) uexpr)\<lbrakk>exp/v\<rbrakk>)"
    by (metis (no_types) assms  usubst_cancel)
  then show ?thesis
  by (smt assign_c_cond_seqr_dist subst_uop)  
qed

lemma assign_c_cond_bop1[symbolic_exec_cp]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif bop bp exp exp2 then (v \<Midarrow> exp ;; Simpl C1) else (v \<Midarrow> exp ;; Simpl C2) eif = 
          v \<Midarrow> exp ;; bif bop bp (&v) exp2 then Simpl C1 else Simpl C2 eif"
 proof -
  have "bop bp exp exp2 = bop bp ((&v::('a, 'b) uexpr)\<lbrakk>exp/v\<rbrakk>) exp2"
    by (metis (no_types) assms(1)  usubst_cancel)
  then show ?thesis
    using assign_c_cond_seqr_dist subst_bop
    by (metis (no_types, hide_lams) "2" id_subst pr_var_def subst_unrest)
qed

lemma assign_c_cond_bop2[symbolic_exec_cp]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "bif bop bp exp2 exp then (v \<Midarrow> exp ;; Simpl C1) else (v \<Midarrow> exp ;; Simpl C2) eif = 
          v \<Midarrow> exp ;; bif bop bp  exp2 (&v) then Simpl C1 else Simpl C2 eif"
 proof -
  have "bop bp exp2 exp  = bop bp  exp2 ((&v::('a, 'b) uexpr)\<lbrakk>exp/v\<rbrakk>)"
    by (metis (no_types) assms(1)  usubst_cancel)
  then show ?thesis
    using assign_c_cond_seqr_dist subst_bop
    by (metis (no_types, hide_lams) "2" id_subst pr_var_def subst_unrest)
qed

lemma assign_cond_trop1[symbolic_exec_cp]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif trop bp exp exp2 exp3 then (v \<Midarrow> exp ;; Simpl C1) else (v \<Midarrow> exp ;; Simpl C2) eif = 
         v \<Midarrow> exp ;; bif trop bp (&v) exp2 exp3 then Simpl C1 else Simpl C2 eif"
 proof -
  have "trop bp exp exp2 exp3 = trop bp ((&v::('a, 'b) uexpr)\<lbrakk>exp/v\<rbrakk>) exp2 exp3"
    by (metis (no_types) assms(1)  usubst_cancel)
  then show ?thesis
    using assign_c_cond_seqr_dist subst_trop
    by (metis (no_types, hide_lams) "2" "3" id_subst pr_var_def subst_unrest)
qed

lemma assign_cond_trop2[symbolic_exec_cp]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif trop bp exp2 exp  exp3 then (v \<Midarrow> exp ;; Simpl C1) else (v \<Midarrow> exp ;; Simpl C2) eif = 
         v \<Midarrow> exp ;; bif trop bp  exp2 (&v) exp3 then Simpl C1 else Simpl C2 eif"
 proof -
  have "trop bp exp2 exp exp3 = trop bp exp2 ((&v::('a, 'b) uexpr)\<lbrakk>exp/v\<rbrakk>) exp3"
    by (metis (no_types) assms(1)  usubst_cancel)
  then show ?thesis
    using assign_c_cond_seqr_dist subst_trop
    by (metis (no_types, hide_lams) "2" "3" id_subst pr_var_def subst_unrest)
qed

lemma assign_cond_trop3[symbolic_exec_cp]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "bif trop bp exp2 exp3 exp then (v \<Midarrow> exp ;; Simpl C1) else (v \<Midarrow> exp ;; Simpl C2) eif = 
         v \<Midarrow> exp ;; bif trop bp exp2 exp3 (&v)  then Simpl C1 else Simpl C2 eif"
 proof -
  have "trop bp exp2 exp3 exp  = trop bp exp2 exp3 ((&v::('a, 'b) uexpr)\<lbrakk>exp/v\<rbrakk>)"
    by (metis (no_types) assms(1)  usubst_cancel)
  then show ?thesis
    using assign_c_cond_seqr_dist subst_trop
    by (metis (no_types, hide_lams) "2" "3" id_subst pr_var_def subst_unrest)
qed

lemma assign_cond_qtop1[symbolic_exec_cp]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif qtop bp exp exp2 exp3 exp4 then (v \<Midarrow> exp ;; Simpl C1) else (v \<Midarrow> exp ;; Simpl C2) eif = 
         v \<Midarrow> exp ;; bif qtop bp (&v) exp2 exp3 exp4 then Simpl C1 else Simpl C2 eif"
 proof -
  have "qtop bp exp exp2 exp3 exp4 = qtop bp ((&v::('a, 'b) uexpr)\<lbrakk>exp/v\<rbrakk>) exp2 exp3 exp4"
    by (metis (no_types) assms(1)  usubst_cancel)
  then show ?thesis
    using assign_c_cond_seqr_dist subst_qtop
    by (metis (no_types, hide_lams) "2" "3" "4" id_subst pr_var_def subst_unrest)
qed

lemma assign_c_cond_qtop2[symbolic_exec_cp]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4:"v \<sharp> exp4"
  shows "bif qtop bp exp2 exp  exp3 exp4 then (v \<Midarrow> exp ;; Simpl C1) else (v \<Midarrow> exp ;; Simpl C2) eif = 
         v \<Midarrow> exp ;; bif qtop bp exp2 (&v) exp3 exp4 then Simpl C1 else Simpl C2 eif"
 proof -
  have "qtop bp exp2 exp exp3 exp4 = qtop bp exp2 ((&v::('a, 'b) uexpr)\<lbrakk>exp/v\<rbrakk>) exp3 exp4"
    by (metis (no_types) assms(1)  usubst_cancel)
  then show ?thesis
    using assign_c_cond_seqr_dist subst_qtop
    by (metis (no_types, hide_lams) "2" "3" "4" id_subst pr_var_def subst_unrest)
qed


lemma assign_c_cond_qtop3[symbolic_exec_cp]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif qtop bp exp2 exp3 exp exp4 then (v \<Midarrow> exp ;; Simpl C1) else (v \<Midarrow> exp ;; Simpl C2) eif = 
         v \<Midarrow> exp ;; bif qtop bp exp2  exp3 (&v) exp4 then Simpl C1 else Simpl C2 eif"
 proof -
  have "qtop bp exp2 exp3 exp  exp4 = qtop bp exp2  exp3 ((&v::('a, 'b) uexpr)\<lbrakk>exp/v\<rbrakk>) exp4"
    by (metis (no_types) assms(1)  usubst_cancel)
  then show ?thesis
    using assign_c_cond_seqr_dist subst_qtop
    by (metis (no_types, hide_lams) "2" "3" "4" id_subst pr_var_def subst_unrest)
qed

lemma assign_c_cond_qtop4[symbolic_exec_cp]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "bif qtop bp exp2 exp3 exp4 exp then (v \<Midarrow> exp ;; Simpl C1) else (v \<Midarrow> exp ;; Simpl C2) eif = 
         v \<Midarrow> exp ;; bif qtop bp exp2  exp3 exp4 (&v)  then Simpl C1 else Simpl C2 eif"
 proof -
  have "qtop bp exp2 exp3 exp4 exp = qtop bp exp2 exp3 exp4 ((&v::('a, 'b) uexpr)\<lbrakk>exp/v\<rbrakk>)"
    by (metis (no_types) assms(1)  usubst_cancel)
  then show ?thesis
    using assign_c_cond_seqr_dist subst_qtop
    by (metis (no_types, hide_lams) "2" "3" "4" id_subst pr_var_def subst_unrest)
qed

lemma assign_c_cond_If [symbolic_exec_cp]:
  "(bif bexp then (v \<Midarrow> exp1) else (v \<Midarrow> exp2) eif) = 
   (v \<Midarrow> (trop If bexp exp1 exp2))" 
  by rel_auto

subsection {*While laws*}
text{*In this section we introduce the algebraic laws of programming related to the while
      statement.*}

theorem while_unfold:
  "while b do P od = (bif b then (P ;; while b do P od) else SKIP eif)"
proof -
  have m:"mono (\<lambda>X. bif b then (P ;; X) else SKIP eif)"
    by (auto intro: monoI seqr_mono cond_mono)
  have "(while b do P od) = (\<nu> X \<bullet> bif b then (P ;; X) else SKIP eif)"
    by (simp add: While_def)
  also have "... = (bif b then (P ;; (\<nu> X \<bullet> bif b then (P ;; X) else SKIP eif)) else SKIP eif)"
    by (subst lfp_unfold, simp_all add: m)
  also have "... = (bif b then (P ;; while b do P od) else SKIP eif)"
    by (simp add: While_def)
  finally show ?thesis .
qed

lemma while_true:
  shows "(while true do P od) = false"
  apply (simp add: While_def alpha)
  apply (rule antisym)
  apply (simp_all)
  apply (rule lfp_lowerbound)
  apply (simp)
done

lemma while_false:
  shows "(while false do P od) = SKIP"
proof -
  have "(while false do P od) = bif false then (P ;; while false do P od) else SKIP eif" 
    using while_unfold[of _ P] by simp
  also have "... = SKIP" by (simp add: aext_false)
  finally show ?thesis . 
qed

lemma while_inv_unfold:
  "while b invr p do P od = (bif b then (P ;; while b invr p do P od) else SKIP eif)"
  unfolding While_inv_def using while_unfold
  by auto

theorem while_bot_unfold:
  "while\<^sub>\<bottom> b do P od = (bif b then (P ;; while\<^sub>\<bottom> b do P od) else SKIP eif)"
proof -
  have m:"mono (\<lambda>X. bif b then (P ;; X) else SKIP eif)"
    by (auto intro: monoI seqr_mono cond_mono)
  have "(while\<^sub>\<bottom> b do P od) = (\<mu> X \<bullet> bif b then (P ;; X) else SKIP eif)"
    by (simp add: While_bot_def)
  also have "... = (bif b then (P ;; (\<mu> X \<bullet> bif b then (P ;; X) else SKIP eif)) else SKIP eif)"
    by (subst gfp_unfold, simp_all add: m)
  also have "... = (bif b then (P ;; while\<^sub>\<bottom> b do P od) else SKIP eif)"
    by (simp add: While_bot_def)
  finally show ?thesis .
qed

theorem while_bot_false: "while\<^sub>\<bottom> false do P od = SKIP"
  by (simp add: While_bot_def mu_const alpha)

theorem while_bot_true: "while\<^sub>\<bottom> true do P od = (\<mu> X \<bullet> P ;; X)"
  by (simp add: While_bot_def alpha)

subsection {*assume laws*}

lemma assume_twice: "(b\<^sup>\<top>\<^sup>C ;; c\<^sup>\<top>\<^sup>C) = (b \<and> c)\<^sup>\<top>\<^sup>C"
  by (rel_auto) (blast, blast, blast, metis not_None_eq)




end