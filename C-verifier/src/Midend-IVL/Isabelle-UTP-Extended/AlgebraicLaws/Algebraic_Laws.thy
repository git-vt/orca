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
  imports 
    UTP.utp_rel_laws
    "../theories/Rel/utp_rel_more"
begin

syntax
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrel"  (infixr ":==" 72)

named_theorems symbolic_exec and symbolic_exec_assign_uop and symbolic_exec_assign_bop and
               symbolic_exec_assign_trop and symbolic_exec_assign_qtop and symbolic_exec_ex
(* Usage of symbolic_exec_ex for the simp lemmas avoids annoying warnings about duplicate theorems
when using `simp add: symbolic_exec` *)

subsection \<open>SKIP Laws\<close>
text \<open>In this section we introduce the algebraic laws of programming related to the SKIP
      statement.\<close>

declare assign_r_alt_def [symbolic_exec]

lemma skip_r_eq[simp]: "\<lbrakk>II\<rbrakk>\<^sub>e (a, b) \<longleftrightarrow> a = b"
  by rel_auto
    
subsection \<open>Assignment Laws\<close>

text \<open>In this section we introduce the algebraic laws of programming related to the assignment
      statement.\<close>

declare usubst_lookup_upd_pr_var [symbolic_exec]
declare usubst_lookup_upd [symbolic_exec]
declare subst_var [symbolic_exec]
declare assign_test [symbolic_exec]
declare assign_r_comp [symbolic_exec]
declare assign_twice [symbolic_exec]
declare assign_rcond[symbolic_exec]

lemma assign_uop1 [symbolic_exec_assign_uop]:
  assumes 1: "mwb_lens v"
  shows "(v :== e1 ;; v :== (uop F (&v))) = (v :== (uop F e1))"
  using 1
  by rel_auto

lemma assign_bop1 [symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v :== e1 ;; v :== (bop bp (&v) e2)) = (v :== (bop bp e1 e2))"
  using 1 2
  by rel_auto

lemma assign_bop2 [symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v :== e1 ;; v :== (bop bp e2 (&v))) = (v :== (bop bp e2 e1))"
  using 1 2
  by rel_auto

lemma assign_trop1 [symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :== e1 ;; v :== (trop tp (&v) e2 e3)) =
         (v :== (trop tp e1 e2 e3))"
  using 1 2 3
  by rel_auto

lemma assign_trop2 [symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :== e1 ;; v :== (trop tp e2 (&v) e3)) =
         (v :== (trop tp e2 e1 e3))"
  using 1 2 3
  by rel_auto

lemma assign_trop3 [symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v :== e1 ;; v :== (trop tp e2 e3 (&v))) =
         (v :== (trop tp e2 e3 e1))"
  using 1 2 3
  by rel_auto

lemma assign_qtop1 [symbolic_exec_assign_qtop]:
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
  by (simp add: assign_r_comp usubst_condr)
 

text \<open>In the sequel we find assignment laws proposed by Hoare\<close>

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
  using 1 by (rel_simp)

lemma assign_cond_If_bop[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> expr"
  shows "((v :== E);;
          ((v :== (bop F expr (&v))) \<triangleleft>bop F expr (&v)\<triangleright>\<^sub>r (v :== (bop G expr (&v))))) =
         (v :== (trop If (bop F expr E) (bop F expr E) (bop G expr E)))"
  using 1 2 by rel_simp

lemma assign_cond_If_bop1[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> expr"
  shows "((v :== E);;
          ((v :== (bop F (&v) expr)) \<triangleleft>bop F (&v) expr\<triangleright>\<^sub>r (v :== (bop G (&v) expr)))) =
         (v :== (trop If (bop F E expr) (bop F E expr) (bop G E expr)))"
  using 1 2 by rel_simp

lemma assign_cond_If_bop2[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v :== E);;
          ((v :== (bop F (&v) exp1)) \<triangleleft>bop F (&v) exp1\<triangleright>\<^sub>r (v :== (bop G (&v) exp2)))) =
         (v :== (trop If (bop F E exp1) (bop F E exp1) (bop G E exp2)))"
  using 1 2 3 by rel_simp

lemma assign_cond_If_bop4[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v :== E);;
          ((v :== (bop F (&v) exp1)) \<triangleleft>bop F (&v) exp1\<triangleright>\<^sub>r (v :== (bop G exp2 (&v))))) =
         (v :== (trop If (bop F E exp1) (bop F E exp1) (bop G exp2 E)))"
  using 1 2 3 by rel_simp

lemma assign_cond_If_bop5[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v :== E);;
          ((v :== (bop F exp1 (&v))) \<triangleleft>bop F exp1 (&v)\<triangleright>\<^sub>r (v :== (bop G (&v) exp2)))) =
         (v :== (trop If (bop F exp1 E) (bop F exp1 E) (bop G E exp2)))"
  using 1 2 3 by rel_simp

lemma assign_cond_If_bop6[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v :== E);;
          ((v :== (bop F exp1 (&v))) \<triangleleft>bop F exp1 (&v)\<triangleright>\<^sub>r (v :== (bop G exp2 (&v))))) =
         (v :== (trop If (bop F exp1 E) (bop F exp1 E) (bop G exp2 E)))"
  using 1 2 3 by rel_simp

lemma assign_cond_If_trop[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v :== E);;
         ((v :== (trop F exp1 exp2 (&v))) \<triangleleft>trop F exp1 exp2 (&v)\<triangleright>\<^sub>r (v :== (trop G exp1 exp2 (&v))))) =
         (v :== (trop If (trop F exp1 exp2 E) (trop F exp1 exp2 E) (trop G exp1 exp2 E)))"
  using 1 2 3 by rel_simp

lemma assign_cond_If_trop1[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v :== E);;
          ((v :== (trop F exp1 (&v) exp2)) \<triangleleft>trop F exp1 (&v) exp2\<triangleright>\<^sub>r (v :== (trop G exp1 (&v) exp2)))) =
         (v :== (trop If (trop F exp1 E exp2) (trop F exp1 E exp2) (trop G exp1 E exp2)))"
  using 1 2 3 by rel_simp

lemma assign_cond_If_trop2[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v :== E);;
          ((v :== (trop F (&v) exp1 exp2)) \<triangleleft>trop F (&v) exp1 exp2\<triangleright>\<^sub>r (v :== (trop G (&v) exp1 exp2)))) =
         (v :== (trop If (trop F E exp1 exp2) (trop F E exp1 exp2) (trop G E exp1 exp2)))"
  using 1 2 3 by rel_simp

lemma assign_cond_If_trop3[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2" and 4:"v \<sharp> exp3" and 5:"v \<sharp> exp4"
  shows "((v :== E);;
          ((v :== (trop F exp1 exp2 (&v))) \<triangleleft>trop F exp1 exp2 (&v)\<triangleright>\<^sub>r (v :== (trop G exp3 exp4 (&v))))) =
         (v :== (trop If (trop F exp1 exp2 E) (trop F exp1 exp2 E) (trop G exp3 exp4 E)))"
  using 1 2 3 4 5 by rel_simp

lemma assign_cond_If_trop4[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2" and 4:"v \<sharp> exp3" and 5:"v \<sharp> exp4"
  shows "((v :== E);;
         ((v :== (trop F exp1 (&v) exp2)) \<triangleleft>trop F exp1 (&v) exp2\<triangleright>\<^sub>r (v :== (trop G exp3 (&v) exp4)))) =
         (v :== (trop If (trop F exp1 E exp2) (trop F exp1 E exp2) (trop G exp3 E exp4)))"
  using 1 2 3 4 5 by rel_simp

lemma assign_cond_If_trop5[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2" and 4:"v \<sharp> exp3" and 5:"v \<sharp> exp4"
  shows "((v :== E);;
          ((v :== (trop F (&v) exp1 exp2)) \<triangleleft>trop F (&v) exp1 exp2\<triangleright>\<^sub>r (v :== (trop G (&v) exp3 exp4)))) =
         (v :== (trop If (trop F E exp1 exp2) (trop F E exp1 exp2) (trop G E exp3 exp4)))"
  using 1 2 3 4 5 by rel_simp

subsection \<open>Conditional Laws\<close>

text \<open>In this section we introduce the algebraic laws of programming related to the conditional
      statement.\<close>

named_theorems urel_cond

declare cond_idem[urel_cond]
declare cond_distr[urel_cond]
declare cond_and_T_integrate [urel_cond]
declare cond_L6 [urel_cond]
declare cond_L7 [urel_cond]
declare cond_and_distr [urel_cond]
declare cond_or_distr[urel_cond]
declare cond_imp_distr[urel_cond]
declare cond_eq_distr[urel_cond]

lemma cond_ueq_distr[urel_cond]:
  "((P =\<^sub>u Q) \<triangleleft> b \<triangleright> (R =\<^sub>u S)) =
   ((P \<triangleleft> b \<triangleright> R) =\<^sub>u (Q \<triangleleft> b \<triangleright> S))"
  by rel_auto

declare cond_conj_distr [urel_cond]
declare cond_disj_distr [urel_cond]
declare cond_neg [urel_cond]
declare cond_conj [urel_cond]

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

named_theorems urel_comp

declare cond_seq_left_distr [urel_comp]
declare cond_seq_right_distr [urel_comp]

subsection \<open>Sequential Laws\<close>

text \<open>In this section we introduce the algebraic laws of programming related to the sequential
      composition of statements.\<close>

declare seqr_exists_left [symbolic_exec]
declare seqr_exists_right [symbolic_exec]
declare seqr_left_zero [symbolic_exec_ex]
declare seqr_right_zero [symbolic_exec_ex]

declare seqr_or_distr [urel_comp]

declare seqr_left_one_point [urel_comp]
declare seqr_right_one_point[urel_comp]
declare seqr_insert_ident_left[urel_comp]
declare seqr_insert_ident_right[urel_comp]
declare seq_var_ident_lift[urel_comp] 

lemma seqr_skip: "II ;; C = C ;; II"
  by (metis seqr_left_unit seqr_right_unit)

lemma post_str_rel: 
  "(p\<Rightarrow>q) \<sqsubseteq> P \<Longrightarrow> `q\<Rightarrow>r` \<Longrightarrow> (p\<Rightarrow>r) \<sqsubseteq> P"
  by pred_blast

(*The rules SEQ6 SEQ7 related to SEQ and non-deterministic choice are missing for now*)

subsection \<open>While laws for normal designs\<close>

text \<open>In this section we introduce the algebraic laws of programming related to the while
      statement.\<close>
    
    
subsection \<open>Other Iteration laws for relations\<close>
  
theorem from_until_gfp_rel_alt_def:
  "from\<^sup>\<top> init until exit do body od = init ;; while\<^sup>\<top> \<not> exit do body od"
  unfolding while_def from_until_gfp_rel_def 
  by simp  

lemma from_until_while_gfp_rel:
  "from\<^sup>\<top> SKIP\<^sub>r until exit do body od = while\<^sup>\<top> \<not> exit do body od"
  unfolding from_until_gfp_rel_alt_def
  by simp
    
theorem from_until_gfp_rel_unfold:
  "from\<^sup>\<top> init until exit do body od = 
   init ;; (bif \<not> exit then (body;; while\<^sup>\<top> \<not> exit do body od) else SKIP\<^sub>r eif)"
  unfolding from_until_gfp_rel_alt_def
  by (metis while_unfold) 
    
theorem from_until_lfp_rel_alt_def:
  "from\<^sub>\<bottom> init until exit do body od = init ;; while\<^sub>\<bottom> \<not> exit do body od"
  unfolding while_bot_def from_until_lfp_rel_def 
  by simp  

lemma from_until_while_lfp_rel:
  "from\<^sub>\<bottom> SKIP\<^sub>r until exit do body od = while\<^sub>\<bottom> \<not> exit do body od"
  unfolding from_until_lfp_rel_alt_def
  by simp
    
theorem from_until_lfp_rel_unfold:
  "from\<^sub>\<bottom> init until exit do body od = 
   init ;; (bif \<not> exit then (body;; while\<^sub>\<bottom> \<not> exit do body od) else SKIP\<^sub>r eif)"
  unfolding from_until_lfp_rel_alt_def
  by (metis while_bot_unfold) 

theorem do_while_gfp_rel_alt_def:
  "do body while\<^sup>\<top> exit od = body ;; while\<^sup>\<top> exit do body od"
  unfolding  do_while_gfp_rel_def from_until_gfp_rel_alt_def
  by simp  
    
theorem do_while_gfp_rel_unfold:
  "do body while\<^sup>\<top> exit od = 
   body ;; (bif exit then (body;; while\<^sup>\<top> exit do body od) else SKIP\<^sub>r eif)"
  unfolding do_while_gfp_rel_alt_def using while_unfold[of exit]
  by simp

theorem do_while_lfp_rel_alt_def:
  "do body while\<^sub>\<bottom> exit od = body ;; while\<^sub>\<bottom> exit do body od"
  unfolding  do_while_lfp_rel_def from_until_lfp_rel_alt_def
  by simp  
    
theorem do_while_lfp_rel_unfold:
  "do body while\<^sub>\<bottom> exit od = 
   body ;; (bif exit then (body;; while\<^sub>\<bottom> exit do body od) else SKIP\<^sub>r eif)"
  unfolding do_while_lfp_rel_alt_def using while_bot_unfold[of exit]
  by simp    

theorem for_gfp_rel_alt_def:
  "for\<^sup>\<top> (init, exit, incr) do body od = init ;; while\<^sup>\<top> exit do body;;incr od"
  unfolding  for_gfp_rel_def from_until_gfp_rel_alt_def
  by simp  
    
theorem for_gfp_rel_unfold: 
  shows "for\<^sup>\<top> (init, exit, incr) do body od = 
         init ;; (bif exit then (body;;incr;;while\<^sup>\<top> exit do body ;; incr od) else SKIP\<^sub>r eif)"
  unfolding for_gfp_rel_alt_def using while_unfold 
  by (metis seqr_assoc)

theorem for_lfp_rel_alt_def:
 "for\<^sub>\<bottom> (init, exit, incr) do body od = init ;; while\<^sub>\<bottom> exit do body;;incr od"
  unfolding  for_lfp_rel_def from_until_lfp_rel_alt_def
  by simp  
    
theorem for_lfp_rel_unfold:
  "for\<^sub>\<bottom> (init, exit, incr) do body od = 
   init ;; (bif exit then (body;;incr;;while\<^sub>\<bottom> exit do body ;; incr od) else SKIP\<^sub>r eif)"
  unfolding for_lfp_rel_alt_def using while_bot_unfold 
  by (metis seqr_assoc)  

subsection \<open>assume and assert laws\<close>

declare assume_seq [urel_comp]
declare assert_seq [urel_comp]
declare RA6 [urel_comp]

lemmas skip_refine' = post_str_rel[OF skip_r_refine]

end


