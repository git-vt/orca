
section "Algebraic laws for designs"
theory algebraic_laws_designs
imports "../theories/utp_fault_designs"

begin
named_theorems symbolic_exec_cp
subsection"Throw"

lemma throw_left_zero[simp]: 
  "(THROW ;; Simpl P) = THROW" 
  by rel_auto

lemma throw_right_zero_skip[simp]: 
  "(SKIP ;; THROW) = THROW " 
  by rel_auto

lemma throw_c_idem [simp]: 
  "(THROW ;; THROW) = THROW " 
  by rel_auto

subsection"Skip"

text{*In this section we introduce the algebraic laws of programming related to the SKIP
      statement.*}
theorem design_skip_c_idem [simp]:
  "(SKIP ;; SKIP) = SKIP"
  by (rel_auto)

lemma skip_c_left_unit[simp]: 
  "(SKIP ;;  Simpl P) =  Simpl P"
  by rel_auto

lemma skip_lift_alpha_eq:
  "\<lceil>II\<rceil>\<^sub>C = ($\<Sigma>\<^sub>C\<acute> =\<^sub>u $\<Sigma>\<^sub>C)"
  by rel_auto

lemma skip_c_alpha_eq:
  "SKIP = Simpl (\<not>$abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> ($\<Sigma>\<^sub>C\<acute> =\<^sub>u $\<Sigma>\<^sub>C))"
  by (simp add: skip_lift_alpha_eq skip_c_def)

lemma skip_c_right_unit[simp]: 
  "(Simpl P  ;;  SKIP) =  Simpl P"  
  by rel_auto (metis option.exhaust_sel)

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
  "\<langle>\<sigma>\<rangle>\<^sub>C = Simpl (\<not>$abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> II\<rceil>\<^sub>C)"
  by rel_auto

subsection {*Assignment Laws*}
text{*In this section we introduce the algebraic laws of programming related to the assignment
      statement.*}

lemma usubst_cancel_c[usubst,symbolic_exec_cp]: 
  assumes 1:"weak_lens v" 
  shows "($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub>C\<^sub></$v\<rbrakk>= \<lceil>expr\<rceil>\<^sub>C\<^sub><"
  using 1
  by  rel_auto
thm assigns_comp
lemma assigns_c_comp: "(\<langle>f\<rangle>\<^sub>C ;; \<langle>g\<rangle>\<^sub>C) = \<langle>g \<circ> f\<rangle>\<^sub>C"
  by rel_auto

lemma assign_test[symbolic_exec_cp]:
  assumes 1:"mwb_lens x" 
  shows     "(x \<Midarrow> \<guillemotleft>u\<guillemotright> ;; x \<Midarrow> \<guillemotleft>v\<guillemotright>) = (x \<Midarrow> \<guillemotleft>v\<guillemotright>)"
  using 1   
  by (simp add: assigns_c_comp subst_upd_comp subst_lit usubst_upd_idem)

lemma assign_c_left_comp: 
  "(\<langle>\<sigma>\<rangle>\<^sub>C ;; Simpl(\<lceil>P\<rceil>\<^sub>C \<turnstile> \<lceil>Q\<rceil>\<^sub>C)) = Simpl(\<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P\<rceil>\<^sub>C \<turnstile> \<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> Q\<rceil>\<^sub>C)"
  by rel_auto

lemma assign_c_left_comp_subst[symbolic_exec_cp]: 
  "(x \<Midarrow> u ;; Simpl(\<lceil>P\<rceil>\<^sub>C \<turnstile> \<lceil>Q\<rceil>\<^sub>C)) = Simpl(\<lceil>[$x \<mapsto>\<^sub>s \<lceil>u\<rceil>\<^sub><] \<dagger> P\<rceil>\<^sub>C \<turnstile> \<lceil>[$x \<mapsto>\<^sub>s \<lceil>u\<rceil>\<^sub><] \<dagger> Q\<rceil>\<^sub>C)" 
  by rel_auto 

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
  by rel_auto (metis option.distinct(1))

lemma assign_c_uop1[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (uop F (&v))) = (v \<Midarrow> (uop F e1))"
  using 1
  by rel_auto (fastforce)

lemma assign_c_bop1[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow>(bop bp (&v) e2)) = (v \<Midarrow> (bop bp e1 e2))"
  using 1 2  
  by rel_auto (metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_bop2[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (bop bp e2 (&v))) = (v \<Midarrow> (bop bp e2 e1))"
  using 1 2  
  by rel_auto (metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_trop1[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (trop tp (&v) e2 e3)) = 
         (v \<Midarrow> (trop tp e1 e2 e3))"
  using 1 2 3
  by rel_auto (metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_trop2[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (trop tp e2 (&v) e3)) = 
         (v \<Midarrow> (trop tp e2 e1 e3))"
  using 1 2 3
  by rel_auto (metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_trop3[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (trop tp e2 e3 (&v))) = 
         (v \<Midarrow> (trop tp e2 e3 e1))"
  using 1 2 3
  by rel_auto (metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_qtop1[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp (&v) e2 e3 e4)) = 
         (v \<Midarrow> (qtop tp e1 e2 e3 e4))"
  using 1 2 3 4
  by rel_auto (metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_qtop2[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp e2 (&v) e3 e4)) = 
         (v \<Midarrow> (qtop tp e2 e1 e3 e4))"
  using 1 2 3 4
  by rel_auto (metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_qtop3[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp e2 e3 (&v) e4)) = 
         (v \<Midarrow> (qtop tp e2 e3 e1 e4))"
  using 1 2 3 4
  by rel_auto (metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

lemma assign_c_qtop4[symbolic_exec_cp]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v \<Midarrow> e1 ;; v \<Midarrow> (qtop tp e2 e3 e4 (&v))) = 
         (v \<Midarrow> (qtop tp e2 e3 e4 e1))"
  using 1 2 3 4
  by rel_auto (metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)

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
  using 1 by rel_auto

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

lemma assign_c_cond_If_uop[symbolic_exec_cp]:
  assumes 1: "mwb_lens v"
  shows "(v \<Midarrow> E;; 
         bif uop F (&v) then (v \<Midarrow> uop F (&v)) else (v\<Midarrow> uop G (&v)) eif) =
         (v \<Midarrow> trop If (uop F E) (uop F E) (uop G E))" 
  using 1 assign_c_alt_def assign_c_cond_If assign_c_cond_c_uop assign_c_uop1 mwb_lens_weak
  by (metis (no_types, lifting))

lemma assign_cond_If_bop[symbolic_exec_cp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp"
  shows "((v \<Midarrow> E);; 
          bif bop F exp (&v) then (v \<Midarrow> (bop F exp (&v))) else (v \<Midarrow> (bop G exp (&v))) eif) =
         (v \<Midarrow> (trop If (bop F exp E) (bop F exp E) (bop G exp E)))"
proof -
  have f1: 
    "\<forall>l u p ua ub uc. 
      \<not> weak_lens (l::bool \<Longrightarrow> 'a) \<or> \<not> (l \<sharp> (u::('b, 'a) uexpr)) \<or> 
      bif bop p u (ua :\<^sub>u bool) 
      then (l \<Midarrow> ua::('c, _, _) rel_cp) ;; C3 ((true::('c, _, _) rel_cp) \<turnstile> ub)::('c, _, _) rel_cp 
      else (l \<Midarrow> ua::('c, _, _) rel_cp) ;; C3 (true \<turnstile> uc) 
      eif = 
      (l \<Midarrow> ua::('c, _, _) rel_cp) ;; 
      bif bop p u (&l) then C3 (true \<turnstile> ub) else C3 (true \<turnstile> uc) eif"
    using assign_c_cond_bop2 by blast
  have "\<forall>l. \<not> mwb_lens (l::bool \<Longrightarrow> 'a) \<or> weak_lens l"
    using mwb_lens_weak by blast
  then have "weak_lens v"
    by (metis "1") 
  then have f2: 
         "bif bop F exp E 
          then (v \<Midarrow> E::('c, 'a, 'a) rel_cp) ;; C3 ((true::('c, 'a, _) rel_cp) \<turnstile> (\<not> $abrupt\<acute> \<and> $fault\<acute> =\<^sub>u (\<guillemotleft>None::'c option\<guillemotright>::('c option, ('c, 'a) cp \<times> ('c, 'a) cp) uexpr) \<and> \<lceil>(\<lceil>[v \<mapsto>\<^sub>s bop F exp (&v)]\<rceil>\<^sub>s::'a \<times> 'a \<Rightarrow> 'a \<times> _) \<dagger> (II::('a, 'a) rel)\<rceil>\<^sub>C))::('c, 'a, 'a) rel_cp 
          else (v \<Midarrow> E::('c, 'a, 'a) rel_cp) ;; C3 ((true::('c, 'a, _) rel_cp) \<turnstile> (\<not> $abrupt\<acute> \<and> $fault\<acute> =\<^sub>u (\<guillemotleft>None::'c option\<guillemotright>::('c option, ('c, 'a) cp \<times> ('c, 'a) cp) uexpr) \<and> \<lceil>(\<lceil>[v \<mapsto>\<^sub>s bop G exp (&v)]\<rceil>\<^sub>s::'a \<times> 'a \<Rightarrow> 'a \<times> _) \<dagger> (II::('a, 'a) rel)\<rceil>\<^sub>C)) 
          eif = 
          (v \<Midarrow> E::('c, 'a, 'a) rel_cp) ;; 
          bif bop F exp (&v) 
          then C3 ((true::('c, 'a, 'a) rel_cp) \<turnstile> (\<not> $abrupt\<acute> \<and> $fault\<acute> =\<^sub>u (\<guillemotleft>None::'c option\<guillemotright>::('c option, ('c, 'a) cp \<times> ('c, 'a) cp) uexpr) \<and> \<lceil>(\<lceil>[v \<mapsto>\<^sub>s bop F exp (&v)]\<rceil>\<^sub>s::'a \<times> 'a \<Rightarrow> 'a \<times> _) \<dagger> (II::('a, 'a) rel)\<rceil>\<^sub>C))
          else C3 (true \<turnstile> (\<not> $abrupt\<acute> \<and> $fault\<acute> =\<^sub>u (\<guillemotleft>None::'c option\<guillemotright>::('c option, ('c, 'a) cp \<times> ('c, 'a) cp) uexpr) \<and> \<lceil>(\<lceil>[v \<mapsto>\<^sub>s bop G exp (&v)]\<rceil>\<^sub>s::'a \<times> 'a \<Rightarrow> 'a \<times> _) \<dagger> (II::('a, 'a) rel)\<rceil>\<^sub>C)) 
          eif"
    using f1 by (metis "2") 
  have f3: 
    "\<forall>l u ua p. 
      \<not> mwb_lens (l::bool \<Longrightarrow> 'a) \<or> \<not> (l \<sharp> (u::('b, 'a) uexpr)) \<or> 
      (l \<Midarrow> (ua :\<^sub>u bool)::('c, _, _) rel_cp) ;; (l \<Midarrow> bop p u (&l)::('c, _, _) rel_cp) = 
      (l \<Midarrow> (bop p u ua :\<^sub>u bool)::('c, _, _) rel_cp)"
    by (meson assign_c_bop2)
  then have f4: 
         "(v \<Midarrow> E::('c, 'a, 'a) rel_cp) ;; 
          (v \<Midarrow> bop F exp (&v)::('c, 'a, 'a) rel_cp) = 
          (v \<Midarrow> bop F exp E::('c, 'a, 'a) rel_cp)"
    by (metis "1" "2")
  have 
    "(v \<Midarrow> E::('c, 'a, 'a) rel_cp) ;; 
     (v \<Midarrow> bop G exp (&v)::('c, 'a, 'a) rel_cp) = 
     (v \<Midarrow> bop G exp E::('c, 'a, 'a) rel_cp)"
    using f3 by (metis "1" "2") 
  then have 
         "(v \<Midarrow> E::('c, 'a, 'a) rel_cp) ;; 
          bif bop F exp (&v) 
          then v \<Midarrow> bop F exp (&v)::('c, 'a, 'a) rel_cp 
          else v \<Midarrow> bop G exp (&v) 
          eif = 
          bif bop F exp E 
          then v \<Midarrow> bop F exp E::('c, 'a, 'a) rel_cp  
          else v \<Midarrow> bop G exp E 
          eif"
    using f4 f2 by (simp add: assign_c_alt_def)
  then have 
         "(v \<Midarrow> E::('c, 'a, 'a) rel_cp) ;; 
           bif bop F exp (&v) then v \<Midarrow> bop F exp (&v)::('c, 'a, 'a) rel_cp else v \<Midarrow> bop G exp (&v) eif = 
          (v \<Midarrow> (bop F exp E \<triangleleft> bop F exp E \<triangleright> bop G exp E)::('c, 'a, 'a) rel_cp)"
    by (metis assign_c_cond_If)
  then show ?thesis
    by meson
qed 

lemma assign_c_cond_If_bop1[symbolic_exec_cp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp"
  shows "((v \<Midarrow> E);; 
          bif bop F (&v) exp then (v \<Midarrow> (bop F (&v) exp)) else (v \<Midarrow>(bop G (&v) exp)) eif) =
         (v \<Midarrow> (trop If (bop F E exp) (bop F E exp) (bop G E exp)))" 
  using 1 2
proof -
  have f1: 
    "\<forall> l u p ua ub uc. 
       \<not> weak_lens (l::bool \<Longrightarrow> 'a) \<or> \<not> (l \<sharp> (u::('b, 'a) uexpr)) \<or> 
       bif bop p (ua :\<^sub>u bool) u 
       then (l \<Midarrow> ua::('c, _, _) rel_cp) ;; C3 ((true::('c, _, _) rel_cp) \<turnstile> ub)::('c, _, _) rel_cp 
       else (l \<Midarrow> ua::('c, _, _) rel_cp) ;; C3 (true \<turnstile> uc) 
       eif = 
       (l \<Midarrow> ua::('c, _, _) rel_cp) ;; 
       bif bop p (&l) u 
       then C3 (true \<turnstile> ub) 
       else C3 (true \<turnstile> uc) eif"
    using assign_c_cond_bop1 by blast
  have "\<forall>l. \<not> mwb_lens (l::bool \<Longrightarrow> 'a) \<or> weak_lens l"
    using mwb_lens_weak by blast
  then have "weak_lens v"
    by (metis "1") 
  then have f2: 
         "bif bop F E exp 
          then (v \<Midarrow> E::('c, 'a, 'a) rel_cp) ;; 
               C3 ((true::('c, 'a, _) rel_cp) \<turnstile> (\<not> $abrupt\<acute> \<and> $fault\<acute> =\<^sub>u (\<guillemotleft>None::'c option\<guillemotright>::('c option, ('c, 'a) cp \<times> ('c, 'a) cp) uexpr) \<and> \<lceil>(\<lceil>[v \<mapsto>\<^sub>s bop F (&v) exp]\<rceil>\<^sub>s::'a \<times> 'a \<Rightarrow> 'a \<times> _) \<dagger> (II::('a, 'a) rel)\<rceil>\<^sub>C))::('c, 'a, 'a) rel_cp 
          else (v \<Midarrow> E::('c, 'a, 'a) rel_cp) ;; C3 ((true::('c, 'a, _) rel_cp) \<turnstile> (\<not> $abrupt\<acute> \<and> $fault\<acute> =\<^sub>u (\<guillemotleft>None::'c option\<guillemotright>::('c option, ('c, 'a) cp \<times> ('c, 'a) cp) uexpr) \<and> \<lceil>(\<lceil>[v \<mapsto>\<^sub>s bop G (&v) exp]\<rceil>\<^sub>s::'a \<times> 'a \<Rightarrow> 'a \<times> _) \<dagger> (II::('a, 'a) rel)\<rceil>\<^sub>C)) 
          eif = 
          (v \<Midarrow> E::('c, 'a, 'a) rel_cp) ;; 
          bif bop F (&v) exp 
          then C3 ((true::('c, 'a, 'a) rel_cp) \<turnstile> (\<not> $abrupt\<acute> \<and> $fault\<acute> =\<^sub>u (\<guillemotleft>None::'c option\<guillemotright>::('c option, ('c, 'a) cp \<times> ('c, 'a) cp) uexpr) \<and> \<lceil>(\<lceil>[v \<mapsto>\<^sub>s bop F (&v) exp]\<rceil>\<^sub>s::'a \<times> 'a \<Rightarrow> 'a \<times> _) \<dagger> (II::('a, 'a) rel)\<rceil>\<^sub>C)) 
          else C3 (true \<turnstile> (\<not> $abrupt\<acute> \<and> $fault\<acute> =\<^sub>u (\<guillemotleft>None::'c option\<guillemotright>::('c option, ('c, 'a) cp \<times> ('c, 'a) cp) uexpr) \<and> \<lceil>(\<lceil>[v \<mapsto>\<^sub>s bop G (&v) exp]\<rceil>\<^sub>s::'a \<times> 'a \<Rightarrow> 'a \<times> _) \<dagger> (II::('a, 'a) rel)\<rceil>\<^sub>C)) 
          eif"
    using f1 by (metis "2") 
  have f3: 
    "\<forall>l u ua p. \<not> mwb_lens (l::bool \<Longrightarrow> 'a) \<or> \<not> (l \<sharp> (u::('b, 'a) uexpr)) \<or> 
                (l \<Midarrow> (ua :\<^sub>u bool)::('c, _, _) rel_cp) ;; 
                (l \<Midarrow> bop p (&l) u::('c, _, _) rel_cp) = 
                (l \<Midarrow> (bop p ua u :\<^sub>u bool)::('c, _, _) rel_cp)"
    by (meson assign_c_bop1)
  then have f4: 
         "(v \<Midarrow> E::('c, 'a, 'a) rel_cp) ;; 
          (v \<Midarrow> bop F (&v) exp::('c, 'a, 'a) rel_cp) = 
          (v \<Midarrow> bop F E exp::('c, 'a, 'a) rel_cp)"
    by (metis "1" "2")
  have "(v \<Midarrow> E::('c, 'a, 'a) rel_cp) ;; (v \<Midarrow> bop G (&v) exp::('c, 'a, 'a) rel_cp) = 
        (v \<Midarrow> bop G E exp::('c, 'a, 'a) rel_cp)"
    using f3 by (metis "1" "2")
  then have "(v \<Midarrow> E::('c, 'a, 'a) rel_cp) ;; 
              bif bop F (&v) exp 
              then v \<Midarrow> bop F (&v) exp::('c, 'a, 'a) rel_cp 
              else v \<Midarrow> bop G (&v) exp 
              eif = 
              bif bop F E exp then v \<Midarrow> bop F E exp::('c, 'a, 'a) rel_cp else v \<Midarrow> bop G E exp eif"
    using f4 f2 by (simp add: assign_c_alt_def)
  then have "(v \<Midarrow> E::('c, 'a, 'a) rel_cp) ;; 
              bif bop F (&v) exp 
              then v \<Midarrow> bop F (&v) exp::('c, 'a, 'a) rel_cp 
              else v \<Midarrow> bop G (&v) exp eif = 
             (v \<Midarrow> (bop F E exp \<triangleleft> bop F E exp \<triangleright> bop G E exp)::('c, 'a, 'a) rel_cp)"
    by (metis assign_c_cond_If) 
  then show ?thesis
    by meson
qed

lemma assign_c_cond_If_bop2[symbolic_exec_cp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v \<Midarrow> E);; 
          bif bop F (&v) exp1 then (v \<Midarrow> (bop F (&v) exp1)) else (v \<Midarrow> (bop G (&v) exp2)) eif) =
         (v \<Midarrow> (trop If (bop F E exp1) (bop F E exp1) (bop G E exp2)))" 
  using 1 2 3
  by (smt assign_c_alt_def assign_c_bop1 assign_c_cond_If assign_c_cond_bop1 mwb_lens_weak)

lemma assign_cond_If_bop4[symbolic_exec_cp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v \<Midarrow> E);; 
          bif bop F (&v) exp1 then (v \<Midarrow> (bop F (&v) exp1)) else (v \<Midarrow> (bop G exp2 (&v))) eif ) =
         (v \<Midarrow> (trop If (bop F E exp1) (bop F E exp1) (bop G exp2 E)))" 
  using assms


oops


lemma assign_cond_If_bop5[symbolic_exec_cp]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v:== E);; 
          (v:== (bop F exp1 (&v))) \<triangleleft>bop F exp1 (&v)\<triangleright>\<^sub>r (v:== (bop G (&v) exp2))) =
         (v:== (trop If (bop F exp1 E) (bop F exp1 E) (bop G E exp2)))" 
  using 1 2 3
proof (rel_simp, transfer)
  fix a :: 'a and b :: 'a and va :: "bool \<Longrightarrow> 'a" and Fa :: "bool \<Rightarrow> bool" and Ea :: "'a \<Rightarrow> bool" and Ga :: "bool \<Rightarrow> bool"
  have "Fa (Ea a) \<longrightarrow> (Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<and> (\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a)))"
    by presburger
  then have "\<not> ((\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a))) \<and> (Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Ga (Ea a)))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by fastforce
  then show "(Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by meson
qed 

lemma assign_cond_If_bop6[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v:== E);; 
          (v:== (bop F exp1 (&v))) \<triangleleft>bop F exp1 (&v)\<triangleright>\<^sub>r (v:== (bop G exp2 (&v)))) =
         (v:== (trop If (bop F exp1 E) (bop F exp1 E) (bop G exp2 E)))" 
  using 1 2 3
proof (rel_simp, transfer)
  fix a :: 'a and b :: 'a and va :: "bool \<Longrightarrow> 'a" and Fa :: "bool \<Rightarrow> bool" and Ea :: "'a \<Rightarrow> bool" and Ga :: "bool \<Rightarrow> bool"
  have "Fa (Ea a) \<longrightarrow> (Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<and> (\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a)))"
    by presburger
  then have "\<not> ((\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a))) \<and> (Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Ga (Ea a)))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by fastforce
  then show "(Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by meson
qed 

lemma assign_cond_If_trop[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v:== E);;
         (v:== (trop F exp1 exp2 (&v))) \<triangleleft>trop F exp1 exp2 (&v)\<triangleright>\<^sub>r (v:== (trop G exp1 exp2 (&v)))) =
         (v:== (trop If (trop F exp1 exp2 E) (trop F exp1 exp2 E) (trop G exp1 exp2 E)))" 
  using 1 2 3
proof (rel_simp, transfer)
  fix a :: 'a and b :: 'a and va :: "bool \<Longrightarrow> 'a" and Fa :: "bool \<Rightarrow> bool" and Ea :: "'a \<Rightarrow> bool" and Ga :: "bool \<Rightarrow> bool"
  have "Fa (Ea a) \<longrightarrow> (Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<and> (\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a)))"
    by presburger
  then have "\<not> ((\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a))) \<and> (Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Ga (Ea a)))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by fastforce
  then show "(Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by meson
qed 

lemma assign_cond_If_trop1[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v:== E);; 
          (v:== (trop F exp1 (&v) exp2)) \<triangleleft>trop F exp1 (&v) exp2\<triangleright>\<^sub>r (v:== (trop G exp1 (&v) exp2))) =
         (v:== (trop If (trop F exp1 E exp2) (trop F exp1 E exp2) (trop G exp1 E exp2)))" 
  using 1 2 3
proof (rel_simp, transfer)
  fix a :: 'a and b :: 'a and va :: "bool \<Longrightarrow> 'a" and Fa :: "bool \<Rightarrow> bool" and Ea :: "'a \<Rightarrow> bool" and Ga :: "bool \<Rightarrow> bool"
  have "Fa (Ea a) \<longrightarrow> (Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<and> (\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a)))"
    by presburger
  then have "\<not> ((\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a))) \<and> (Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Ga (Ea a)))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by fastforce
  then show "(Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by meson
qed 

lemma assign_cond_If_trop2[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v:== E);; 
          (v:== (trop F (&v) exp1 exp2)) \<triangleleft>trop F (&v) exp1 exp2\<triangleright>\<^sub>r (v:== (trop G (&v) exp1 exp2))) =
         (v:== (trop If (trop F E exp1 exp2) (trop F E exp1 exp2) (trop G E exp1 exp2)))" 
  using 1 2 3
proof (rel_simp, transfer)
  fix a :: 'a and b :: 'a and va :: "bool \<Longrightarrow> 'a" and Fa :: "bool \<Rightarrow> bool" and Ea :: "'a \<Rightarrow> bool" and Ga :: "bool \<Rightarrow> bool"
  have "Fa (Ea a) \<longrightarrow> (Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<and> (\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a)))"
    by presburger
  then have "\<not> ((\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a))) \<and> (Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Ga (Ea a)))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by fastforce
  then show "(Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by meson
qed 

lemma assign_cond_If_trop3[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2" and 4:"v \<sharp> exp3" and 5:"v \<sharp> exp4"
  shows "((v:== E);;
          (v:== (trop F exp1 exp2 (&v))) \<triangleleft>trop F exp1 exp2 (&v)\<triangleright>\<^sub>r (v:== (trop G exp3 exp4 (&v)))) =
         (v:== (trop If (trop F exp1 exp2 E) (trop F exp1 exp2 E) (trop G exp3 exp4 E)))" 
  using 1 2 3 4 5
proof (rel_simp, transfer)
  fix a :: 'a and b :: 'a and va :: "bool \<Longrightarrow> 'a" and Fa :: "bool \<Rightarrow> bool" and Ea :: "'a \<Rightarrow> bool" and Ga :: "bool \<Rightarrow> bool"
  have "Fa (Ea a) \<longrightarrow> (Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<and> (\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a)))"
    by presburger
  then have "\<not> ((\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a))) \<and> (Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Ga (Ea a)))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by fastforce
  then show "(Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by meson
qed 

lemma assign_cond_If_trop4[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2" and 4:"v \<sharp> exp3" and 5:"v \<sharp> exp4"
  shows "((v:== E);; 
         (v:== (trop F exp1 (&v) exp2)) \<triangleleft>trop F exp1 (&v) exp2\<triangleright>\<^sub>r (v:== (trop G exp3 (&v) exp4))) =
         (v:== (trop If (trop F exp1 E exp2) (trop F exp1 E exp2) (trop G exp3 E exp4)))" 
  using 1 2 3 4 5
proof (rel_simp, transfer)
  fix a :: 'a and b :: 'a and va :: "bool \<Longrightarrow> 'a" and Fa :: "bool \<Rightarrow> bool" and Ea :: "'a \<Rightarrow> bool" and Ga :: "bool \<Rightarrow> bool"
  have "Fa (Ea a) \<longrightarrow> (Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<and> (\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a)))"
    by presburger
  then have "\<not> ((\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a))) \<and> (Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Ga (Ea a)))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by fastforce
  then show "(Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by meson
qed 

lemma assign_cond_If_trop5[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2" and 4:"v \<sharp> exp3" and 5:"v \<sharp> exp4"
  shows "((v:== E);; 
          (v:== (trop F (&v) exp1 exp2)) \<triangleleft>trop F (&v) exp1 exp2\<triangleright>\<^sub>r (v:== (trop G (&v) exp3 exp4))) =
         (v:== (trop If (trop F E exp1 exp2) (trop F E exp1 exp2) (trop G E exp3 exp4)))" 
  using 1 2 3 4 5
proof (rel_simp, transfer)
  fix a :: 'a and b :: 'a and va :: "bool \<Longrightarrow> 'a" and Fa :: "bool \<Rightarrow> bool" and Ea :: "'a \<Rightarrow> bool" and Ga :: "bool \<Rightarrow> bool"
  have "Fa (Ea a) \<longrightarrow> (Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<and> (\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a)))"
    by presburger
  then have "\<not> ((\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a))) \<and> (Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Ga (Ea a)))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by fastforce
  then show "(Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by meson
qed 

end