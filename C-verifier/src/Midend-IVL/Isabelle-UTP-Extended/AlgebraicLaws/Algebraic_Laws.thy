(******************************************************************************
 * Orca: A Functional Correctness Verifier for Imperative Programs
 *       Based on Isabelle/UTP
 *
 * Copyright (c) 2016-2018 Virginia Tech, USA
 *               2016-2018 Technische Universität München, Germany
 *               2016-2018 University of York, UK
 *               2016-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * This software may be distributed and modified according to the terms of
 * the GNU Lesser General Public License version 3.0 or any later version.
 * Note that NO WARRANTY is provided.
 *
 * See CONTRIBUTORS, LICENSE and CITATION files for details.
 ******************************************************************************)

section \<open>Algebraic laws of programming\<close>

text \<open>In this section we introduce the semantic rules related to the different
      statements of IMP. In the literature this also known as the algebraic laws of programming.
      In our framework we will use these rules in order to optimize a given program written in our
      language, and this before any deductive proof verification activity or formal testing.\<close>

theory Algebraic_Laws
  imports "../../Isabelle-UTP/utp/utp_urel_laws"
begin

named_theorems symbolic_exec and symbolic_exec_assign_uop and symbolic_exec_assign_bop and
               symbolic_exec_assign_trop and symbolic_exec_assign_qtop and symbolic_exec_ex
(* Usage of symbolic_exec_ex for the simp lemmas avoids annoying warnings about duplicate theorems
when using `simp add: symbolic_exec` *)

subsection \<open>SKIP Laws\<close>
text \<open>In this section we introduce the algebraic laws of programming related to the SKIP
      statement.\<close>

lemma pre_skip_post: "(\<lceil>b\<rceil>\<^sub>< \<and> II) = (II \<and> \<lceil>b\<rceil>\<^sub>>)"
  by rel_auto

lemma skip_var:
  fixes x :: "(bool \<Longrightarrow> '\<alpha>)"
  shows "($x \<and> II) = (II \<and> $x\<acute>)"
  by rel_auto

lemma assign_r_alt_def [symbolic_exec]:
  fixes x :: "('a \<Longrightarrow>'\<alpha>)"
  shows "x :== v = II\<lbrakk>\<lceil>v\<rceil>\<^sub></$x\<rbrakk>"
  by rel_auto

lemma skip_r_alpha_eq:
  "II = ($\<Sigma>\<acute> =\<^sub>u $\<Sigma>)"
  by rel_auto

lemma skip_r_refine_orig:
  "(p \<Rightarrow> p) \<sqsubseteq> II"
  by pred_blast

lemma skip_r_eq[simp]: "\<lbrakk>II\<rbrakk>\<^sub>e (a, b) \<longleftrightarrow> a = b"
  by rel_auto

lemma skip_refine_join:
  "(p \<Rightarrow> q) \<sqsubseteq> II \<longleftrightarrow> `((p \<squnion> II) \<Rightarrow> q)`"
  by pred_auto
 
lemma skip_refine_rel:
  "`(II \<Rightarrow> (p \<Rightarrow> q))` \<Longrightarrow> (p \<Rightarrow> q) \<sqsubseteq> II"
  by pred_auto
  
lemma skip_r_refine_pred:
  "`(p \<Rightarrow> q)` \<Longrightarrow> (\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> II"
  by rel_auto
    
subsection \<open>Assignment Laws\<close>
text \<open>In this section we introduce the algebraic laws of programming related to the assignment
      statement.\<close>

lemma "&v\<lbrakk>expr/v\<rbrakk> = [v \<mapsto>\<^sub>s expr] \<dagger> &v" ..

lemma usubst_cancel[usubst,symbolic_exec]:
  assumes 1:"weak_lens v"
  shows "(&v)\<lbrakk>expr/v\<rbrakk> = expr"
  using 1
  by transfer' rel_auto

lemma usubst_cancel_r[usubst,symbolic_exec]:
  assumes 1:"weak_lens v"
  shows "($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub></$v\<rbrakk>= \<lceil>expr\<rceil>\<^sub><"
  using 1
  by  rel_auto

lemma assign_test[symbolic_exec]:
  assumes 1:"mwb_lens x"
  shows     "(x :== \<guillemotleft>u\<guillemotright> ;; x :== \<guillemotleft>v\<guillemotright>) = (x :== \<guillemotleft>v\<guillemotright>)"
  using 1
  by (simp add: assigns_comp subst_upd_comp subst_lit usubst_upd_idem)

lemma assign_r_comp[symbolic_exec]:
  "(x :== u ;; P) = P\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>"
  by (simp add: assigns_r_comp usubst)

lemma assign_twice[symbolic_exec]:
  assumes "mwb_lens x" and  "x \<sharp> f"
  shows "(x :== e ;; x :== f) = (x :== f)"
  using assms
  by (simp add: assigns_comp usubst)

lemma assign_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x :== e ;; y :== f) = (y :== f ;; x :== e)"
  using assms
  by (rel_auto, simp_all add: lens_indep_comm)

lemma assign_cond:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "out\<alpha> \<sharp> b"
  shows "(x :== e ;; (P \<triangleleft> b \<triangleright> Q)) =
         ((x :== e ;; P) \<triangleleft>b\<lbrakk>\<lceil>e\<rceil>\<^sub></$x\<rbrakk>\<triangleright> (x :== e ;; Q))"
  by rel_auto

lemma assign_rcond[symbolic_exec]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "(x :== e ;; (P \<triangleleft> b \<triangleright>\<^sub>r Q)) = ((x :== e ;; P) \<triangleleft> (b\<lbrakk>e/x\<rbrakk>) \<triangleright>\<^sub>r (x :== e ;; Q))"
  by rel_auto

lemma assign_uop1[symbolic_exec_assign_uop]:
  assumes 1: "mwb_lens v"
  shows "(v :== e1 ;; v :== (uop F (&v))) = (v :== (uop F e1))"
  using 1
  by rel_auto

lemma assign_bop1[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v :== e1 ;; v :== (bop bp (&v) e2)) = (v :== (bop bp e1 e2))"
  using 1 2
  by rel_auto

lemma assign_bop2[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v :== e1 ;; v :== (bop bp e2 (&v))) = (v :== (bop bp e2 e1))"
  using 1 2
  by rel_auto

lemma assign_trop1[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :== e1 ;; v :== (trop tp (&v) e2 e3)) =
         (v :== (trop tp e1 e2 e3))"
  using 1 2 3
  by rel_auto

lemma assign_trop2[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :== e1 ;; v :== (trop tp e2 (&v) e3)) =
         (v :== (trop tp e2 e1 e3))"
  using 1 2 3
  by rel_auto

lemma assign_trop3[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :== e1 ;; v :== (trop tp e2 e3 (&v))) =
         (v :== (trop tp e2 e3 e1))"
  using 1 2 3
  by rel_auto

lemma assign_qtop1[symbolic_exec_assign_qtop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :== e1 ;; v :== (qtop tp (&v) e2 e3 e4)) =
         (v :== (qtop tp e1 e2 e3 e4))"
  using 1 2 3 4
  by rel_auto

lemma assign_qtop2[symbolic_exec_assign_qtop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :== e1 ;; v :== (qtop tp e2 (&v) e3 e4)) =
         (v :== (qtop tp e2 e1 e3 e4))"
  using 1 2 3 4
  by rel_auto

lemma assign_qtop3[symbolic_exec_assign_qtop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :== e1 ;; v :== (qtop tp e2 e3 (&v) e4)) =
         (v :== (qtop tp e2 e3 e1 e4))"
  using 1 2 3 4
  by rel_auto

lemma assign_qtop4[symbolic_exec_assign_qtop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v :== e1 ;; v :== (qtop tp e2 e3 e4 (&v))) =
         (v :== (qtop tp e2 e3 e4 e1))"
  using 1 2 3 4
  by rel_auto

lemma assign_cond_seqr_dist:
  "(v :== e ;; (P \<triangleleft> b \<triangleright> Q)) = ((v :== e ;; P) \<triangleleft> b\<lbrakk>\<lceil>e\<rceil>\<^sub></$v\<rbrakk> \<triangleright> (v :== e ;; Q))"
  by rel_auto 

text \<open>In the sequel we find assignment laws proposed by Hoare\<close>

lemma assign_vwb_skip:
  assumes 1: "vwb_lens v"
  shows "(v :== &v) = II"
  by (simp add: assms skip_r_def usubst_upd_var_id)
  
lemma assign_simultaneous:
  assumes  1: "vwb_lens v2"
  and      2: "v1 \<bowtie> v2"
  shows "(v1,v2 :== e, (&v2)) =  (v1 :== e)"
  by (simp add: 1 2 usubst_upd_comm usubst_upd_var_id)

lemma assign_seq:
  assumes  1: "vwb_lens var2"
  shows"(var1:== expr);; (var2 :== &var2) = (var1:== expr)"
  using 1 by rel_auto

lemma assign_cond_uop[symbolic_exec_assign_uop]:
  assumes 1: "weak_lens v"
  shows "v :== expr ;; (C1 \<triangleleft>uop F (&v)\<triangleright>\<^sub>r  C2)  =
         (v :== expr ;; C1) \<triangleleft>uop F expr\<triangleright>\<^sub>r (v :== expr ;; C2)"
  using 1
  by rel_auto

lemma assign_cond_bop1[symbolic_exec_assign_bop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "(v :== expr ;; (C1 \<triangleleft>(bop bp (&v) exp2)\<triangleright>\<^sub>r C2)) =
         ((v :== expr ;; C1) \<triangleleft>(bop bp expr exp2)\<triangleright>\<^sub>r  (v :== expr ;; C2))"
  using 1 2
  by rel_auto

lemma assign_cond_bop2[symbolic_exec_assign_bop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "(v :== exp1 ;; (C1 \<triangleleft>(bop bp exp2 (&v))\<triangleright>\<^sub>r C2)) =
         ((v :== exp1 ;; C1) \<triangleleft>(bop bp exp2 exp1)\<triangleright>\<^sub>r (v :== exp1 ;; C2))"
  using 1 2
  by rel_auto

lemma assign_cond_trop1[symbolic_exec_assign_trop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "(v :== expr ;; (C1 \<triangleleft>(trop tp (&v) exp2 exp3)\<triangleright>\<^sub>r C2)) =
         ((v :== expr ;; C1) \<triangleleft>(trop tp expr exp2 exp3)\<triangleright>\<^sub>r (v :== expr ;; C2))"
  using 1 2 3
  by rel_auto

lemma assign_cond_trop2[symbolic_exec_assign_trop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "(v :== exp1 ;; (C1 \<triangleleft>(trop tp exp2 (&v) exp3)\<triangleright>\<^sub>r C2)) =
         ((v :== exp1 ;; C1) \<triangleleft>(trop tp exp2 exp1 exp3)\<triangleright>\<^sub>r (v :== exp1 ;; C2))"
  using 1 2 3
  by rel_auto

lemma assign_cond_trop3[symbolic_exec_assign_trop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "(v :== exp1 ;; (C1 \<triangleleft>(trop bp exp2 exp3 (&v))\<triangleright>\<^sub>r C2)) =
         ((v :== exp1 ;; C1) \<triangleleft>(trop bp exp2 exp3 exp1)\<triangleright>\<^sub>r (v :== exp1 ;; C2))"
  using 1 2 3
  by rel_auto

lemma assign_cond_qtop1[symbolic_exec_assign_qtop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "(v :== exp1 ;; (C1 \<triangleleft>(qtop tp (&v) exp2 exp3 exp4)\<triangleright>\<^sub>r C2)) =
         ((v :== exp1 ;; C1) \<triangleleft>(qtop tp exp1 exp2 exp3  exp4)\<triangleright>\<^sub>r (v :== exp1 ;; C2))"
  using 1 2 3 4
  by rel_auto

lemma assign_cond_qtop2[symbolic_exec_assign_qtop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4:"v \<sharp> exp4"
  shows "(v :== exp1 ;; (C1 \<triangleleft>(qtop tp exp2 (&v) exp3 exp4)\<triangleright>\<^sub>r C2)) =
         ((v :== exp1 ;; C1) \<triangleleft>(qtop tp exp2 exp1 exp3 exp4)\<triangleright>\<^sub>r  (v :== exp1 ;; C2))"
  using 1 2 3 4
  by rel_auto

lemma assign_cond_qtop3[symbolic_exec_assign_qtop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "(v :== exp1 ;; (C1 \<triangleleft>(qtop bp exp2 exp3 (&v) exp4)\<triangleright>\<^sub>r C2)) =
         ((v :== exp1 ;; C1) \<triangleleft>(qtop bp exp2 exp3 exp1  exp4)\<triangleright>\<^sub>r (v :== exp1 ;; C2))"
  using 1 2 3 4
  by rel_auto

lemma assign_cond_qtop4[symbolic_exec_assign_qtop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "(v :== exp1 ;; (C1 \<triangleleft>(qtop bp exp2 exp3 exp4 (&v))\<triangleright>\<^sub>r C2)) =
         ((v :== exp1 ;; C1) \<triangleleft>(qtop bp exp2 exp3  exp4 exp1)\<triangleright>\<^sub>r (v :== exp1 ;; C2))"
  using 1 2 3 4
  by rel_auto

lemma assign_cond_If [symbolic_exec]:
  "((v :== exp1) \<triangleleft> bexp\<triangleright>\<^sub>r (v :== exp2)) =
   (v :== (trop If bexp exp1 exp2))"
  by rel_auto

lemma assign_cond_If_uop[symbolic_exec_assign_uop]:
  assumes 1: "mwb_lens v"
  shows "(v :== E;;
         ((v :== uop F (&v)) \<triangleleft>uop F (&v)\<triangleright>\<^sub>r (v :== uop G (&v)))) =
         (v :== trop If (uop F E) (uop F E) (uop G E))"
  using 1
proof (rel_simp, transfer)
  fix a :: 'a and b :: 'a and va :: "bool \<Longrightarrow> 'a" and Fa :: "bool \<Rightarrow> bool" and Ea :: "'a \<Rightarrow> bool" and Ga :: "bool \<Rightarrow> bool"
  have "Fa (Ea a) \<longrightarrow> (Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<and> (\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a)))"
    by presburger
  then have "\<not> ((\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a))) \<and> (Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Ga (Ea a)))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by fastforce
  then show "(Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by meson
qed

lemma assign_cond_If_bop[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> expr"
  shows "((v :== E);;
          ((v :== (bop F expr (&v))) \<triangleleft>bop F expr (&v)\<triangleright>\<^sub>r (v :== (bop G expr (&v))))) =
         (v :== (trop If (bop F expr E) (bop F expr E) (bop G expr E)))"
  using 1 2
proof (rel_simp, transfer)
  fix a :: 'a and b :: 'a and va :: "bool \<Longrightarrow> 'a" and Fa :: "bool \<Rightarrow> bool" and Ea :: "'a \<Rightarrow> bool" and Ga :: "bool \<Rightarrow> bool"
  have "Fa (Ea a) \<longrightarrow> (Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<and> (\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a)))"
    by presburger
  then have "\<not> ((\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a))) \<and> (Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Ga (Ea a)))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by fastforce
  then show "(Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by meson
qed

lemma assign_cond_If_bop1[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> expr"
  shows "((v :== E);;
          ((v :== (bop F (&v) expr)) \<triangleleft>bop F (&v) expr\<triangleright>\<^sub>r (v :== (bop G (&v) expr)))) =
         (v :== (trop If (bop F E expr) (bop F E expr) (bop G E expr)))"
  using 1 2
proof (rel_simp, transfer)
  fix a :: 'a and b :: 'a and va :: "bool \<Longrightarrow> 'a" and Fa :: "bool \<Rightarrow> bool" and Ea :: "'a \<Rightarrow> bool" and Ga :: "bool \<Rightarrow> bool"
  have "Fa (Ea a) \<longrightarrow> (Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)) \<and> (\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a)))"
    by presburger
  then have "\<not> ((\<not> Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Fa (Ea a))) \<and> (Fa (Ea a) \<or> \<not> b = put\<^bsub>va\<^esub> a (Ga (Ea a)))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by fastforce
  then show "(Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Fa (Ea a)) \<or> \<not> Fa (Ea a) \<and> b = put\<^bsub>va\<^esub> a (Ga (Ea a))) = (b = put\<^bsub>va\<^esub> a (Fa (Ea a) \<or> \<not> Fa (Ea a) \<and> Ga (Ea a)))"
    by meson
qed

lemma assign_cond_If_bop2[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v :== E);;
          ((v :== (bop F (&v) exp1)) \<triangleleft>bop F (&v) exp1\<triangleright>\<^sub>r (v :== (bop G (&v) exp2)))) =
         (v :== (trop If (bop F E exp1) (bop F E exp1) (bop G E exp2)))"
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

lemma assign_cond_If_bop4[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v :== E);;
          ((v :== (bop F (&v) exp1)) \<triangleleft>bop F (&v) exp1\<triangleright>\<^sub>r (v :== (bop G exp2 (&v))))) =
         (v :== (trop If (bop F E exp1) (bop F E exp1) (bop G exp2 E)))"
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

lemma assign_cond_If_bop5[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v :== E);;
          ((v :== (bop F exp1 (&v))) \<triangleleft>bop F exp1 (&v)\<triangleright>\<^sub>r (v :== (bop G (&v) exp2)))) =
         (v :== (trop If (bop F exp1 E) (bop F exp1 E) (bop G E exp2)))"
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
  shows "((v :== E);;
          ((v :== (bop F exp1 (&v))) \<triangleleft>bop F exp1 (&v)\<triangleright>\<^sub>r (v :== (bop G exp2 (&v))))) =
         (v :== (trop If (bop F exp1 E) (bop F exp1 E) (bop G exp2 E)))"
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
  shows "((v :== E);;
         ((v :== (trop F exp1 exp2 (&v))) \<triangleleft>trop F exp1 exp2 (&v)\<triangleright>\<^sub>r (v :== (trop G exp1 exp2 (&v))))) =
         (v :== (trop If (trop F exp1 exp2 E) (trop F exp1 exp2 E) (trop G exp1 exp2 E)))"
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
  shows "((v :== E);;
          ((v :== (trop F exp1 (&v) exp2)) \<triangleleft>trop F exp1 (&v) exp2\<triangleright>\<^sub>r (v :== (trop G exp1 (&v) exp2)))) =
         (v :== (trop If (trop F exp1 E exp2) (trop F exp1 E exp2) (trop G exp1 E exp2)))"
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
  shows "((v :== E);;
          ((v :== (trop F (&v) exp1 exp2)) \<triangleleft>trop F (&v) exp1 exp2\<triangleright>\<^sub>r (v :== (trop G (&v) exp1 exp2)))) =
         (v :== (trop If (trop F E exp1 exp2) (trop F E exp1 exp2) (trop G E exp1 exp2)))"
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
  shows "((v :== E);;
          ((v :== (trop F exp1 exp2 (&v))) \<triangleleft>trop F exp1 exp2 (&v)\<triangleright>\<^sub>r (v :== (trop G exp3 exp4 (&v))))) =
         (v :== (trop If (trop F exp1 exp2 E) (trop F exp1 exp2 E) (trop G exp3 exp4 E)))"
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
  shows "((v :== E);;
         ((v :== (trop F exp1 (&v) exp2)) \<triangleleft>trop F exp1 (&v) exp2\<triangleright>\<^sub>r (v :== (trop G exp3 (&v) exp4)))) =
         (v :== (trop If (trop F exp1 E exp2) (trop F exp1 E exp2) (trop G exp3 E exp4)))"
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
  shows "((v :== E);;
          ((v :== (trop F (&v) exp1 exp2)) \<triangleleft>trop F (&v) exp1 exp2\<triangleright>\<^sub>r (v :== (trop G (&v) exp3 exp4)))) =
         (v :== (trop If (trop F E exp1 exp2) (trop F E exp1 exp2) (trop G E exp3 exp4)))"
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

subsection \<open>Conditional Laws\<close>
text \<open>In this section we introduce the algebraic laws of programming related to the conditional
      statement.\<close>
named_theorems urel_cond
lemma cond_idem[urel_cond]:
  "(P \<triangleleft> b \<triangleright> P) = P"
  by rel_auto

lemma cond_symm:
  "(P \<triangleleft> b \<triangleright> Q) = (Q \<triangleleft>\<not> b\<triangleright> P)"
  by rel_auto

lemma cond_assoc:
  "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> b \<triangleright> R)) = ((P \<triangleleft> b \<triangleright> Q) \<triangleleft> b \<triangleright>  R)"
  by rel_auto

lemma cond_distr[urel_cond]:
  "((P \<triangleleft> b'\<triangleright> R) \<triangleleft> b \<triangleright> (Q \<triangleleft> b'\<triangleright> R))= ((P \<triangleleft> b \<triangleright> Q) \<triangleleft> b'\<triangleright> R)"
  by rel_auto

lemma cond_unit_T:
  "(P \<triangleleft>true\<triangleright> Q) = P"
  by auto

lemma cond_unit_F:
  "(P \<triangleleft>false\<triangleright> Q) = Q"
  by auto

lemma cond_and_T_integrate[urel_cond]:
  "((P \<and> b) \<or> (Q \<triangleleft> b \<triangleright> R)) = ((P \<or> Q) \<triangleleft> b \<triangleright> R)"
  by rel_auto

lemma cond_L6[urel_cond]:
  "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> b \<triangleright> R)) = (P \<triangleleft> b \<triangleright> R)"
  by rel_auto


lemma cond_L7[urel_cond]:
  "(P \<triangleleft> b \<triangleright> (P \<triangleleft> c \<triangleright> Q)) = (P \<triangleleft> b \<or> c \<triangleright> Q)"
  by rel_auto

lemma cond_and_distr[urel_cond]:
  "((P \<and> Q) \<triangleleft> b \<triangleright> (R \<and> S)) = ((P \<triangleleft> b \<triangleright> R) \<and> (Q \<triangleleft> b \<triangleright> S))"
  by rel_auto

lemma cond_or_distr[urel_cond]:
  "((P \<or> Q) \<triangleleft> b \<triangleright> (R \<or> S)) = ((P \<triangleleft> b \<triangleright> R) \<or> (Q \<triangleleft> b \<triangleright> S))"
  by rel_auto

lemma cond_imp_distr[urel_cond]:
  "((P \<Rightarrow> Q) \<triangleleft> b \<triangleright> (R \<Rightarrow> S)) =
   ((P \<triangleleft> b \<triangleright> R) \<Rightarrow> (Q \<triangleleft> b \<triangleright> S))"
  by rel_auto

lemma cond_eq_distr[urel_cond]:
  "((P \<Leftrightarrow> Q) \<triangleleft> b \<triangleright> (R \<Leftrightarrow> S)) =
   ((P \<triangleleft> b \<triangleright> R) \<Leftrightarrow> (Q \<triangleleft> b \<triangleright> S))"
  by rel_auto

lemma cond_ueq_distr[urel_cond]:
  "((P =\<^sub>u Q) \<triangleleft> b \<triangleright> (R =\<^sub>u S)) =
   ((P \<triangleleft> b \<triangleright> R) =\<^sub>u (Q \<triangleleft> b \<triangleright> S))"
  by rel_auto

lemma cond_conj_distr[urel_cond]:
  "((P \<and> Q) \<triangleleft> b \<triangleright> (P \<and> S)) = (P \<and> (Q \<triangleleft> b \<triangleright> S))"
  by rel_auto

lemma cond_disj_distr [urel_cond]:
  "((P \<or> Q) \<triangleleft> b \<triangleright> (P \<or> S)) = (P \<or> (Q \<triangleleft> b \<triangleright> S))"
  by rel_auto

lemma cond_neg[urel_cond]:
  "\<not> (P \<triangleleft> b \<triangleright> Q) = ((\<not> P) \<triangleleft> b \<triangleright> (\<not> Q))"
  by rel_auto

lemma cond_conj[urel_cond]:
  "(P \<triangleleft>b \<and> c\<triangleright> Q) = (P \<triangleleft> c \<triangleright> Q) \<triangleleft> b \<triangleright> Q"
  by rel_auto

(*IF Theorem by Hoare: It optimize nested IF*)
theorem COND12[urel_cond]:
  "((C1 \<triangleleft>bexp2\<triangleright> C3) \<triangleleft>bexp1\<triangleright> (C2 \<triangleleft>bexp3\<triangleright> C3)) =
   ((C1 \<triangleleft>bexp1\<triangleright> C2) \<triangleleft>(bexp2 \<triangleleft>bexp1\<triangleright>bexp3)\<triangleright> C3)"
  by rel_auto

lemma comp_cond_left_distr:
  "((P \<triangleleft> b \<triangleright>\<^sub>r Q) ;; R) = ((P ;; R) \<triangleleft> b \<triangleright>\<^sub>r (Q ;; R))"
  by rel_auto

lemma cond_var_subst_left[urel_cond]:
  assumes "vwb_lens x"
  shows "(P\<lbrakk>true/x\<rbrakk> \<triangleleft>&x \<triangleright> Q) = (P \<triangleleft>&x \<triangleright> Q)"
  using assms
  apply rel_auto apply transfer
  using vwb_lens.put_eq by fastforce

lemma cond_var_subst_right[urel_cond]:
  assumes "vwb_lens x"
  shows "(P \<triangleleft>&x \<triangleright> Q\<lbrakk>false/x\<rbrakk>) = (P \<triangleleft>&x \<triangleright> Q)"
  using assms
  apply pred_auto apply transfer
  by (metis (full_types) vwb_lens.put_eq)

lemma cond_var_split[urel_cond]:
  "vwb_lens x \<Longrightarrow> (P\<lbrakk>true/x\<rbrakk> \<triangleleft>&x \<triangleright> P\<lbrakk>false/x\<rbrakk>) = P"
  by (rel_auto, (metis (full_types) vwb_lens.put_eq)+)

lemma cond_seq_left_distr[urel_comp]:
  "out\<alpha> \<sharp> b \<Longrightarrow> ((P \<triangleleft> b \<triangleright> Q) ;; R) = ((P ;; R) \<triangleleft> b \<triangleright> (Q ;; R))"
  by rel_auto

lemma cond_seq_right_distr[urel_comp]:
  "in\<alpha> \<sharp> b \<Longrightarrow> (P ;; (Q \<triangleleft> b \<triangleright> R)) = ((P ;; Q) \<triangleleft> b \<triangleright> (P ;; R))"
  by rel_auto

subsection \<open>Sequential Laws\<close>
text \<open>In this section we introduce the algebraic laws of programming related to the sequential
      composition of statements.\<close>


lemma seqr_exists_left[symbolic_exec]:
  "((\<exists> $x \<bullet> P) ;; Q) = (\<exists> $x \<bullet> (P ;; Q))"
  by rel_auto

lemma seqr_exists_right[symbolic_exec]:
  "(P ;; (\<exists> $x\<acute> \<bullet> Q)) = (\<exists> $x\<acute> \<bullet> (P ;; Q))"
  by rel_auto

lemma seqr_left_zero [simp, symbolic_exec_ex]:
  "false ;; P = false"
  by pred_auto

lemma seqr_right_zero [simp, symbolic_exec_ex]:
  "P ;; false = false"
  by pred_auto

lemma seqr_or_distr[urel_comp]:
  "(P ;; (Q \<or> R)) = ((P ;; Q) \<or> (P ;; R))"
  by rel_auto

lemma seqr_unfold:
  "(P ;; Q) = (\<^bold>\<exists> v \<bullet> P\<lbrakk>\<guillemotleft>v\<guillemotright>/$\<Sigma>\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$\<Sigma>\<rbrakk>)"
  by rel_auto

lemma seqr_middle:
  assumes "vwb_lens x"
  shows "(P ;; Q) = (\<^bold>\<exists> v \<bullet> P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  using assms
  apply (rel_auto robust)
  apply (rename_tac xa P Q a b y)
  apply (rule_tac x="get\<^bsub>xa\<^esub> y" in exI)
  apply (rule_tac x="y" in exI)
  apply (simp)
done

lemma seqr_left_one_point[urel_comp]:
  assumes "vwb_lens x"
  shows "((P \<and> $x\<acute> =\<^sub>u \<guillemotleft>v\<guillemotright>) ;; Q) = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  using assms
  by (rel_auto, metis vwb_lens_wb wb_lens.get_put)

lemma seqr_right_one_point[urel_comp]:
  assumes "vwb_lens x"
  shows "(P ;; ($x =\<^sub>u \<guillemotleft>v\<guillemotright> \<and> Q)) = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  using assms
  by (rel_auto, metis vwb_lens_wb wb_lens.get_put)

lemma seqr_insert_ident_left[urel_comp]:
  assumes "vwb_lens x" "$x\<acute> \<sharp> P" "$x \<sharp> Q"
  shows "(($x\<acute> =\<^sub>u $x \<and> P) ;; Q) = (P ;; Q)"
  using assms
  by (rel_auto, meson vwb_lens_wb wb_lens_weak weak_lens.put_get)

lemma seqr_insert_ident_right[urel_comp]:
  assumes "vwb_lens x" "$x\<acute> \<sharp> P" "$x \<sharp> Q"
  shows "(P ;; ($x\<acute> =\<^sub>u $x \<and> Q)) = (P ;; Q)"
  using assms
  by (rel_auto, metis (no_types, hide_lams) vwb_lens_def wb_lens_def weak_lens.put_get)

lemma seq_var_ident_lift[urel_comp]:
  assumes "vwb_lens x" "$x\<acute> \<sharp> P" "$x \<sharp> Q"
  shows "(($x\<acute> =\<^sub>u $x \<and> P) ;; ($x\<acute> =\<^sub>u $x \<and> Q)) = ($x\<acute> =\<^sub>u $x \<and> (P ;; Q))"
  using assms
  by (rel_auto, metis (no_types, lifting) vwb_lens_wb wb_lens_weak weak_lens.put_get)

lemma seqr_skip: "II ;; C = C ;; II"
  by (metis seqr_left_unit seqr_right_unit)

(*The rules SEQ6 SEQ7 related to SEQ and non-deterministic choice are missing for now*)

subsection \<open>While laws for normal designs\<close>

text \<open>In this section we introduce the algebraic laws of programming related to the while
      statement.\<close>
  
lemma while_gfp_rel_def_alt:
  "(while\<^sup>\<top> b do body od) = (\<nu> X \<bullet> bif b then (body ;; X) else SKIP eif)"
  unfolding from_until_gfp_rel_def while_gfp_rel_def 
  by simp 
    
lemma while_lfp_rel_def_alt:
  "(while\<^sub>\<bottom> b do body od) = (\<mu> X \<bullet> bif b then (body ;; X) else SKIP eif)"
  unfolding from_until_lfp_rel_def while_lfp_rel_def 
  by simp
    
theorem while_gfp_rel_unfold:
  "while\<^sup>\<top> b do body od = (bif b then (body ;; while\<^sup>\<top> b do body od) else SKIP eif)"
proof -
  have m:"mono (\<lambda>X. bif b then (body ;; X) else SKIP eif)"
    by (auto intro: monoI seqr_mono cond_mono)
  have "(while\<^sup>\<top> b do body od) = (\<nu> X \<bullet> bif b then (body;; X) else SKIP eif)"
    by (simp add: while_gfp_rel_def_alt)
  also have "... = (bif b then (body ;; (\<nu> X \<bullet> bif b then (body ;; X) else SKIP eif)) else SKIP eif)"
    by (rule lfp_fixpoint[THEN sym, OF m])
  also have "... = (bif b then (body ;; while\<^sup>\<top> b do body od) else SKIP eif)"
    by (simp add: while_gfp_rel_def_alt)
  finally show ?thesis .
qed
  
theorem while_lfp_rel_unfold:
  "while\<^sub>\<bottom> b do body od = (bif b then (body;; while\<^sub>\<bottom> b do body od) else SKIP eif)"
proof -
  have m:"mono (\<lambda>X. bif b then (body ;; X) else SKIP eif)"
    by (auto intro: monoI seqr_mono cond_mono)       
  have "(while\<^sub>\<bottom> b do body od) = (\<mu> X \<bullet> bif b then (body ;; X) else SKIP eif)"
    by (simp add: while_lfp_rel_def_alt)
  also have "... = (bif b then (body ;; (\<mu> X \<bullet> bif b then (body ;; X) else SKIP eif)) else SKIP eif)"
     by (rule gfp_fixpoint[THEN sym, OF m]) 
  also have "... = (bif b then (body ;; while\<^sub>\<bottom> b do body od) else SKIP eif)"
    by (simp add: while_lfp_rel_def_alt)
  finally show ?thesis .
qed
    
theorem while_lfp_rel_true: 
  "while\<^sub>\<bottom> true do body od = (\<mu> X \<bullet> (body;; X))"
  by (simp add: while_lfp_rel_def_alt alpha)
 
lemma while_lfp_rel_false:
  "(while\<^sub>\<bottom> false do body od) = SKIP"
  by (simp add: while_lfp_rel_def_alt alpha gfp_const)

theorem while_gfp_rel_false: 
 "while\<^sup>\<top> false do body od = SKIP"
 by (simp add: while_gfp_rel_def_alt alpha lfp_const)

theorem while_gfp_rel_non_termination: (*because of this lemma and the lemma utp_designs.design_top we do not use gfp for capturing termination *)
  "while\<^sup>\<top> true do SKIP od = false"
  unfolding while_gfp_rel_def_alt  
proof (rule lfp_eqI[of "(\<lambda>X. bif true then SKIP ;; X else SKIP eif)"] , goal_cases)
  case 1
  then show ?case by (auto intro: monoI seqr_mono cond_mono) 
next
  case 2
  then show ?case by rel_simp  
next
  case 3
  then show ?case by simp                      
qed

theorem while_lfp_rel_non_termination: 
  "while\<^sub>\<bottom> true do SKIP od = true"
  unfolding while_lfp_rel_def_alt
proof (rule gfp_eqI[of "(\<lambda>X. bif true then SKIP ;; X else SKIP eif)"] , goal_cases)
  case 1
  then show ?case by (auto intro: monoI seqr_mono cond_mono) 
next
  case 2
  then show ?case  by rel_simp  
next
  case 3
  then show ?case by simp                       
qed    

text \<open>An infinite loop with a feasible body corresponds to a program error (non-termination).\<close>

theorem while_infinite: 
  assumes is_in_abort_situation: "P ;; true\<^sub>h = true" 
  shows "while\<^sub>\<bottom> true do P od = true"    
  apply (simp add: while_lfp_rel_true)
  apply (rule antisym)
  apply (simp)
  apply (rule gfp_upperbound)
  apply (simp add: assms)
  done
    
subsection \<open>Other Iteration laws for relations\<close>
  
theorem from_until_gfp_rel_alt_def:
  "from\<^sup>\<top> init until exit do body od = init ;; while\<^sup>\<top> \<not> exit do body od"
  unfolding while_gfp_rel_def_alt from_until_gfp_rel_def 
  by simp  

lemma from_until_while_gfp_rel:
  "from\<^sup>\<top> SKIP until exit do body od = while\<^sup>\<top> \<not> exit do body od"
  unfolding from_until_gfp_rel_alt_def
  by simp
    
theorem from_until_gfp_rel_unfold:
  "from\<^sup>\<top> init until exit do body od = 
   init ;; (bif \<not> exit then (body;; while\<^sup>\<top> \<not> exit do body od) else SKIP eif)"
  unfolding from_until_gfp_rel_alt_def using while_gfp_rel_unfold[of "\<not>exit"]
  by simp
    
theorem from_until_lfp_rel_alt_def:
  "from\<^sub>\<bottom> init until exit do body od = init ;; while\<^sub>\<bottom> \<not> exit do body od"
  unfolding while_lfp_rel_def_alt from_until_lfp_rel_def 
  by simp  

lemma from_until_while_lfp_rel:
  "from\<^sub>\<bottom> SKIP until exit do body od = while\<^sub>\<bottom> \<not> exit do body od"
  unfolding from_until_lfp_rel_alt_def
  by simp
    
theorem from_until_lfp_rel_unfold:
  "from\<^sub>\<bottom> init until exit do body od = 
   init ;; (bif \<not> exit then (body;; while\<^sub>\<bottom> \<not> exit do body od) else SKIP eif)"
  unfolding from_until_lfp_rel_alt_def using while_lfp_rel_unfold[of "\<not>exit"]
  by simp

theorem do_while_gfp_rel_alt_def:
  "do body while\<^sup>\<top> exit od = body ;; while\<^sup>\<top> exit do body od"
  unfolding  do_while_gfp_rel_def from_until_gfp_rel_alt_def
  by simp  
    
theorem do_while_gfp_rel_unfold:
  "do body while\<^sup>\<top> exit od = 
   body ;; (bif exit then (body;; while\<^sup>\<top> exit do body od) else SKIP eif)"
  unfolding do_while_gfp_rel_alt_def using while_gfp_rel_unfold[of exit]
  by simp

theorem do_while_lfp_rel_alt_def:
  "do body while\<^sub>\<bottom> exit od = body ;; while\<^sub>\<bottom> exit do body od"
  unfolding  do_while_lfp_rel_def from_until_lfp_rel_alt_def
  by simp  
    
theorem do_while_lfp_rel_unfold:
  "do body while\<^sub>\<bottom> exit od = 
   body ;; (bif exit then (body;; while\<^sub>\<bottom> exit do body od) else SKIP eif)"
  unfolding do_while_lfp_rel_alt_def using while_lfp_rel_unfold[of exit]
  by simp    

theorem for_gfp_rel_alt_def:
  "for\<^sup>\<top> (init, exit, incr) do body od = init ;; while\<^sup>\<top> exit do body;;incr od"
  unfolding  for_gfp_rel_def from_until_gfp_rel_alt_def
  by simp  
    
theorem for_gfp_rel_unfold: 
  shows "for\<^sup>\<top> (init, exit, incr) do body od = 
         init ;; (bif exit then (body;;incr;;while\<^sup>\<top> exit do body ;; incr od) else SKIP eif)"
  unfolding for_gfp_rel_alt_def using while_gfp_rel_unfold 
  by (metis seqr_assoc)

theorem for_lfp_rel_alt_def:
 "for\<^sub>\<bottom> (init, exit, incr) do body od = init ;; while\<^sub>\<bottom> exit do body;;incr od"
  unfolding  for_lfp_rel_def from_until_lfp_rel_alt_def
  by simp  
    
theorem for_lfp_rel_unfold:
  "for\<^sub>\<bottom> (init, exit, incr) do body od = 
   init ;; (bif exit then (body;;incr;;while\<^sub>\<bottom> exit do body ;; incr od) else SKIP eif)"
  unfolding for_lfp_rel_alt_def using while_lfp_rel_unfold 
  by (metis seqr_assoc)  

subsection \<open>assume and assert laws\<close>

lemma assume_twice[urel_comp]: "(b\<^sup>\<top> ;; c\<^sup>\<top>) = (b \<and> c)\<^sup>\<top>"
  by rel_auto

lemma assert_twice[urel_comp]: "(b\<^sub>\<bottom> ;; c\<^sub>\<bottom>) = (b \<and> c)\<^sub>\<bottom>"
  by rel_auto

subsection \<open>Relation algebra laws\<close>

theorem RA1: "(P ;; (Q ;; R)) = ((P ;; Q) ;; R)"
  using seqr_assoc by auto

theorem RA2: "(P ;; II) = P" "(II ;; P) = P"
  by simp_all

theorem RA3: "P\<^sup>-\<^sup>- = P"
  by simp

theorem RA4: "(P ;; Q)\<^sup>- = (Q\<^sup>- ;; P\<^sup>-)"
  by simp

theorem RA5: "(P \<or> Q)\<^sup>- = (P\<^sup>- \<or> Q\<^sup>-)"
  by (rel_auto)

theorem RA6[urel_comp]: "((P \<or> Q) ;; R) = ((P;;R) \<or> (Q;;R))"
  using seqr_or_distl by blast

theorem RA7: "((P\<^sup>- ;; (\<not>(P ;; Q))) \<or> (\<not>Q)) = (\<not>Q)"
  by (rel_auto)

subsection \<open>Refinement rules\<close>

lemma reverse_impl_refine:
  "`Q2 \<Rightarrow> Q1`  = (Q1 \<sqsubseteq> Q2)"
  by pred_auto    
  
lemma pre_weak_rel:
  assumes "`Pre \<Rightarrow> I`"
  and     "(I \<Rightarrow> Post) \<sqsubseteq> P"
  shows "(Pre \<Rightarrow> Post) \<sqsubseteq> P"
 using assms
  by(rel_auto)
    
lemma post_str_rel: 
  "(p\<Rightarrow>q) \<sqsubseteq> P \<Longrightarrow> `q\<Rightarrow>r` \<Longrightarrow> (p\<Rightarrow>r) \<sqsubseteq> P"
  by pred_blast
        
lemma cond_refine_rel: 
  assumes "(b \<and> p \<Rightarrow> q) \<sqsubseteq> C\<^sub>1" and "(\<not>b \<and> p \<Rightarrow> q)\<sqsubseteq> C\<^sub>2" 
  shows "(p \<Rightarrow> q) \<sqsubseteq> (C\<^sub>1 \<triangleleft> b \<triangleright> C\<^sub>2)"
  using assms by rel_auto
    
lemma cond_refine_pred: 
  assumes "(\<lceil>b \<and> p\<rceil>\<^sub><\<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> C\<^sub>1" and "(\<lceil>\<not>b \<and> p\<rceil>\<^sub><\<Rightarrow> \<lceil>q\<rceil>\<^sub>>)\<sqsubseteq> C\<^sub>2" 
  shows "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> (C\<^sub>1 \<triangleleft> \<lceil>b\<rceil>\<^sub>< \<triangleright> C\<^sub>2)"
  using assms by rel_auto

lemma seq_refine_pred:
  assumes "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>s\<rceil>\<^sub>>) \<sqsubseteq> f" and "(\<lceil>s\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> fa"
  shows "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> (f ;; fa)"
  using assms by rel_auto
   
lemma seq_refine_unrest:
  assumes "out\<alpha> \<sharp> p" "in\<alpha> \<sharp> q"
  assumes "(p \<Rightarrow> \<lceil>s\<rceil>\<^sub>>) \<sqsubseteq> f" and "(\<lceil>s\<rceil>\<^sub>< \<Rightarrow> q) \<sqsubseteq> fa"
  shows "(p \<Rightarrow> q) \<sqsubseteq> (f ;; fa)"
  using assms by rel_blast    
    
lemmas skip_refine' = post_str_rel[OF skip_r_refine_orig]

end


