 
section {*Algebraic laws of programming*}

text{*In this section we introduce the semantic rules related to the different
      statements of IMP. In the literature this also known as the algebraic laws of programming.
      In our framework we will use these rules in order to optimize a given program written in our 
      language, and this before any deductive proof verification activity or formal testing.*}

theory Algebraic_Laws
imports Commands "utp/utp_urel_laws"
begin
subsection {*testing features*}

text {*block_test1 is a scenario. The scenario represent a program where i is name of the variable
       in the scope of the initial state s. In the scenario, and using the command block,
       we create a new variable with the same name inside the block. 
       Now i is a local var for the cope t.
       In that case we can use the restore function and the state s to set the variable to its
       previous value ie.,its value in the scope s, and this before we exit the block.*}

lemma blocks_test1:
  "mwb_lens i \<Longrightarrow>
      `i :== \<guillemotleft>2::int\<guillemotright>;; 
       block (i :== \<guillemotleft>5\<guillemotright>) (SKIP) (\<lambda> (s, s') (t, t').  i:== \<guillemotleft>\<lbrakk>\<langle>id\<rangle>\<^sub>s i\<rbrakk>\<^sub>e s\<guillemotright>) (\<lambda> (s, s') (t, t').  SKIP)` = 
       (`$i =\<^sub>u \<guillemotleft>2::int\<guillemotright>`)"
  apply rel_auto
  apply (meson mwb_lens_weak weak_lens.view_determination)
  apply (metis mwb_lens_weak odd_nonzero weak_lens.put_get)
done

text {*block_test2 is similar to  block_test1 but the var i is a global var.
       In that case we can use restore function and the state t to set the variable to its
       latest value, ie.,its value in in the scope t,probably modified inside the scope of the block.*}

lemma blocks_test2:
  "mwb_lens i \<Longrightarrow> mwb_lens res \<Longrightarrow>
      `i :== \<guillemotleft>2::int\<guillemotright>;; 
       block (i :== \<guillemotleft>5\<guillemotright>) (SKIP) (\<lambda> (s, s') (t, t').  i:== \<guillemotleft>\<lbrakk>\<langle>id\<rangle>\<^sub>s i\<rbrakk>\<^sub>e t\<guillemotright>) (\<lambda> (s, s') (t, t').  SKIP)` = 
       (`$i =\<^sub>u \<guillemotleft>5::int\<guillemotright>`)"
  apply rel_auto
  apply (meson mwb_lens_weak weak_lens.view_determination)
  apply (metis mwb_lens_weak odd_nonzero weak_lens.put_get)
done

named_theorems symbolic_exec and symbolic_exec_assign_uop and symbolic_exec_assign_bop and 
               symbolic_exec_assign_trop and symbolic_exec_assign_qtop and symbolic_exec_ex
(* Usage of symbolic_exec_ex for the simp lemmas avoids annoying warnings about duplicate theorems
when using `simp add: symbolic_exec` *)

subsection {*SKIP Laws*}
text{*In this section we introduce the algebraic laws of programming related to the SKIP
      statement.*}

lemma seqr_left_unit [simp, symbolic_exec_ex]:
  "SKIP ;; P = P"
  by rel_auto

lemma seqr_right_unit [simp, symbolic_exec_ex]:
  "P ;; SKIP = P"
  by rel_auto

lemma pre_skip_post: "(\<lceil>b\<rceil>\<^sub>< \<and> SKIP) = (SKIP \<and> \<lceil>b\<rceil>\<^sub>>)"
  by rel_auto

lemma skip_var:
  fixes x :: "(bool, '\<alpha>) uvar"
  shows "($x \<and> SKIP) = (SKIP \<and> $x\<acute>)"
  by rel_auto

lemma assign_r_alt_def [symbolic_exec]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "x :== v = SKIP\<lbrakk>\<lceil>v\<rceil>\<^sub></$x\<rbrakk>"
  by rel_auto

lemma skip_r_alpha_eq:
  "SKIP = ($\<Sigma>\<acute> =\<^sub>u $\<Sigma>)"
  by rel_auto

subsection {*Assignment Laws*}
text{*In this section we introduce the algebraic laws of programming related to the assignment
      statement.*}

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


lemma "mwb_lens x \<Longrightarrow> `x :== \<guillemotleft>1::int\<guillemotright> ;; x :== \<guillemotleft>3::int\<guillemotright>` = (`&x =\<^sub>u \<guillemotleft>3\<guillemotright>`)" 
  apply rel_auto
apply (meson mwb_lens_weak weak_lens.view_determination)
by (metis mwb_lens_weak odd_nonzero weak_lens.put_get)

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
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "out\<alpha> \<sharp> b"
  shows "(x :== e ;; (IF b THEN P ELSE Q)) = 
         (IF (b\<lbrakk>\<lceil>e\<rceil>\<^sub></$x\<rbrakk>) THEN (x :== e ;; P) ELSE (x :== e ;; Q))"
  by rel_auto

lemma assign_rcond[symbolic_exec]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "(x :== e ;; (P \<triangleleft> b \<triangleright>\<^sub>r Q)) = ((x :== e ;; P) \<triangleleft> (b\<lbrakk>e/x\<rbrakk>) \<triangleright>\<^sub>r (x :== e ;; Q))"
  by rel_auto

lemma assign_uop1[symbolic_exec_assign_uop]: 
  assumes 1: "mwb_lens v"
  shows "(v:== e1 ;; v:== (uop F (&v))) = (v:== (uop F e1))"
  using 1 
  by rel_auto

lemma assign_bop1[symbolic_exec_assign_bop]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v:== e1 ;; v:== (bop bp (&v) e2)) = (v:== (bop bp e1 e2))"
  using 1 2  
  by rel_auto

lemma assign_bop2[symbolic_exec_assign_bop]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2"
  shows "(v:== e1 ;; v:== (bop bp e2 (&v))) = (v:== (bop bp e2 e1))"
  using 1 2  
  by rel_auto

lemma assign_trop1[symbolic_exec_assign_trop]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v:== e1 ;; v:== (trop tp (&v) e2 e3)) = 
         (v:== (trop tp e1 e2 e3))"
  using 1 2 3
  by rel_auto

lemma assign_trop2[symbolic_exec_assign_trop]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v:== e1 ;; v:== (trop tp e2 (&v) e3)) = 
         (v:== (trop tp e2 e1 e3))"
  using 1 2 3
  by rel_auto

lemma assign_trop3[symbolic_exec_assign_trop]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3"
  shows "(v:== e1 ;; v:== (trop tp e2 e3 (&v))) = 
         (v:== (trop tp e2 e3 e1))"
  using 1 2 3
  by rel_auto

lemma assign_qtop1[symbolic_exec_assign_qtop]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v:== e1 ;; v:== (qtop tp (&v) e2 e3 e4)) = 
         (v:== (qtop tp e1 e2 e3 e4))"
  using 1 2 3 4
  by rel_auto

lemma assign_qtop2[symbolic_exec_assign_qtop]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v:== e1 ;; v:== (qtop tp e2 (&v) e3 e4)) = 
         (v:== (qtop tp e2 e1 e3 e4))"
  using 1 2 3 4
  by rel_auto

lemma assign_qtop3[symbolic_exec_assign_qtop]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v:== e1 ;; v:== (qtop tp e2 e3 (&v) e4)) = 
         (v:== (qtop tp e2 e3 e1 e4))"
  using 1 2 3 4
  by rel_auto

lemma assign_qtop4[symbolic_exec_assign_qtop]: 
  assumes 1: "mwb_lens v" and 2:"v \<sharp> e2" and 3:"v \<sharp> e3" and 4:"v \<sharp> e4"
  shows "(v:== e1 ;; v:== (qtop tp e2 e3 e4 (&v))) = 
         (v:== (qtop tp e2 e3 e4 e1))"
  using 1 2 3 4
  by rel_auto

lemma assign_cond_seqr_dist[symbolic_exec]:
  "(IF (b\<lbrakk>\<lceil>e\<rceil>\<^sub></$v\<rbrakk>) THEN (v:== e ;; P) ELSE (v:== e ;; Q)) = 
   (v:== e ;; IF b THEN P ELSE Q)" 
  by rel_auto

text {*In the sequel we find assignment laws proposed by Hoare*}

lemma assign_vwb_skip:
  assumes 1: "vwb_lens v"
  shows "(v:== &v) = SKIP"
  by (simp add: assms skip_r_def usubst_upd_var_id)

lemma assign_simultaneous:
  assumes  1: "vwb_lens var2"
  and      2: "var1 \<bowtie> var2"
  shows "(var1, var2 :== exp, &var2) = (var1 :== exp)"
  by (simp add: "1" "2" usubst_upd_comm usubst_upd_var_id)

lemma assign_seq:
  assumes  1: "vwb_lens var2"
  shows"(var1:== exp);; (var2 :== &var2) = (var1:== exp)"
  using 1 by rel_auto

lemma assign_cond_uop[symbolic_exec_assign_uop]:
  assumes 1: "weak_lens v"
  shows "(v:== exp ;; C1) \<triangleleft>uop F exp\<triangleright>\<^sub>r (v:== exp ;; C2) = 
          v:== exp ;; C1 \<triangleleft>uop F (&v)\<triangleright>\<^sub>r  C2"
  using 1 
  by rel_auto

lemma assign_cond_bop1[symbolic_exec_assign_bop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "(v:== exp ;; C1 \<triangleleft>(bop bp (&v) exp2)\<triangleright>\<^sub>r C2) = 
         ((v:== exp ;; C1) \<triangleleft>(bop bp exp exp2)\<triangleright>\<^sub>r  (v:== exp ;; C2))"
  using 1 2 
  by rel_auto

lemma assign_cond_bop2[symbolic_exec_assign_bop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2"
  shows "(v:== exp1 ;; C1 \<triangleleft>(bop bp exp2 (&v))\<triangleright>\<^sub>r C2) = 
         ((v:== exp1 ;; C1) \<triangleleft>(bop bp exp2 exp1)\<triangleright>\<^sub>r (v:== exp1 ;; C2))"
  using 1 2 
  by rel_auto

lemma assign_cond_trop1[symbolic_exec_assign_trop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "(v:== exp ;; C1 \<triangleleft>(trop tp (&v) exp2 exp3)\<triangleright>\<^sub>r C2) = 
         ((v:== exp ;; C1) \<triangleleft>(trop tp exp exp2 exp3)\<triangleright>\<^sub>r (v:== exp ;; C2))"
  using 1 2 3
  by rel_auto

lemma assign_cond_trop2[symbolic_exec_assign_trop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "(v:== exp1 ;; C1 \<triangleleft>(trop tp exp2 (&v) exp3)\<triangleright>\<^sub>r C2) = 
         ((v:== exp1 ;; C1) \<triangleleft>(trop tp exp2 exp1 exp3)\<triangleright>\<^sub>r (v:== exp1 ;; C2))"
  using 1 2 3 
  by rel_auto

lemma assign_cond_trop3[symbolic_exec_assign_trop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3"
  shows "(v:== exp1 ;; C1 \<triangleleft>(trop bp exp2 exp3 (&v))\<triangleright>\<^sub>r C2) = 
         ((v:== exp1 ;; C1) \<triangleleft>(trop bp exp2 exp3 exp1)\<triangleright>\<^sub>r (v:== exp1 ;; C2))"
  using 1 2 3 
  by rel_auto

lemma assign_cond_qtop1[symbolic_exec_assign_qtop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "(v:== exp1 ;;  C1 \<triangleleft>(qtop tp (&v) exp2 exp3 exp4)\<triangleright>\<^sub>r C2) = 
         ((v:== exp1 ;; C1) \<triangleleft>(qtop tp exp1 exp2 exp3  exp4)\<triangleright>\<^sub>r (v:== exp1 ;; C2))"
  using 1 2 3 4
  by rel_auto

lemma assign_cond_qtop2[symbolic_exec_assign_qtop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4:"v \<sharp> exp4"
  shows "(v:== exp1 ;; C1 \<triangleleft>(qtop tp exp2 (&v) exp3 exp4)\<triangleright>\<^sub>r C2) = 
         ((v:== exp1 ;; C1) \<triangleleft>(qtop tp exp2 exp1 exp3 exp4)\<triangleright>\<^sub>r  (v:== exp1 ;; C2))"
  using 1 2 3 4
  by rel_auto

lemma assign_cond_qtop3[symbolic_exec_assign_qtop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "(v:== exp1 ;; C1 \<triangleleft>(qtop bp exp2 exp3 (&v) exp4)\<triangleright>\<^sub>r C2) = 
         ((v:== exp1 ;; C1) \<triangleleft>(qtop bp exp2 exp3 exp1  exp4)\<triangleright>\<^sub>r (v:== exp1 ;; C2))"
  using 1 2 3 4
  by rel_auto

lemma assign_cond_qtop4[symbolic_exec_assign_qtop]:
  assumes 1: "weak_lens v" and 2: "v \<sharp> exp2" and 3: "v \<sharp> exp3" and 4: "v \<sharp> exp4"
  shows "(v:== exp1 ;; C1 \<triangleleft>(qtop bp exp2 exp3 exp4 (&v))\<triangleright>\<^sub>r C2) = 
         ((v:== exp1 ;; C1) \<triangleleft>(qtop bp exp2 exp3  exp4 exp1)\<triangleright>\<^sub>r (v:== exp1 ;; C2))"
  using 1 2 3 4
  by rel_auto

lemma assign_cond_If [symbolic_exec]:
  "((v:== exp1) \<triangleleft> bexp\<triangleright>\<^sub>r (v:== exp2)) = 
   (v :== (trop If bexp exp1 exp2))" 
  by rel_auto

lemma assign_cond_If_uop[symbolic_exec_assign_uop]:
  assumes 1: "mwb_lens v"
  shows "(v:== E;; 
         (v:== uop F (&v)) \<triangleleft>uop F (&v)\<triangleright>\<^sub>r (v:== uop G (&v))) =
         (v:== trop If (uop F E) (uop F E) (uop G E))" 
  using 1
  by rel_auto

lemma assign_cond_If_bop[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp"
  shows "((v:== E);; 
          (v:== (bop F exp (&v))) \<triangleleft>bop F exp (&v)\<triangleright>\<^sub>r (v:== (bop G exp (&v)))) =
         (v:== (trop If (bop F exp E) (bop F exp E) (bop G exp E)))" 
  using 1 2
  by rel_auto

lemma assign_cond_If_bop1[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp"
  shows "((v:== E);; 
          (v:== (bop F (&v) exp)) \<triangleleft>bop F (&v) exp\<triangleright>\<^sub>r (v:== (bop G (&v) exp))) =
         (v:== (trop If (bop F E exp) (bop F E exp) (bop G E exp)))" 
  using 1 2
  by rel_auto

lemma assign_cond_If_bop2[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v:== E);; 
          (v:== (bop F (&v) exp1)) \<triangleleft>bop F (&v) exp1\<triangleright>\<^sub>r (v:== (bop G (&v) exp2))) =
         (v:== (trop If (bop F E exp1) (bop F E exp1) (bop G E exp2)))" 
  using 1 2 3
  by rel_auto

lemma assign_cond_If_bop4[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v:== E);; 
          (v:== (bop F (&v) exp1)) \<triangleleft>bop F (&v) exp1\<triangleright>\<^sub>r (v:== (bop G exp2 (&v)))) =
         (v:== (trop If (bop F E exp1) (bop F E exp1) (bop G exp2 E)))" 
  using 1 2 3
  by rel_auto

lemma assign_cond_If_bop5[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v:== E);; 
          (v:== (bop F exp1 (&v))) \<triangleleft>bop F exp1 (&v)\<triangleright>\<^sub>r (v:== (bop G (&v) exp2))) =
         (v:== (trop If (bop F exp1 E) (bop F exp1 E) (bop G E exp2)))" 
  using 1 2 3
  by rel_auto

lemma assign_cond_If_bop6[symbolic_exec_assign_bop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v:== E);; 
          (v:== (bop F exp1 (&v))) \<triangleleft>bop F exp1 (&v)\<triangleright>\<^sub>r (v:== (bop G exp2 (&v)))) =
         (v:== (trop If (bop F exp1 E) (bop F exp1 E) (bop G exp2 E)))" 
  using 1 2 3
  by rel_auto

lemma assign_cond_If_trop[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v:== E);;
         (v:== (trop F exp1 exp2 (&v))) \<triangleleft>trop F exp1 exp2 (&v)\<triangleright>\<^sub>r (v:== (trop G exp1 exp2 (&v)))) =
         (v:== (trop If (trop F exp1 exp2 E) (trop F exp1 exp2 E) (trop G exp1 exp2 E)))" 
  using 1 2 3
  by rel_auto

lemma assign_cond_If_trop1[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v:== E);; 
          (v:== (trop F exp1 (&v) exp2)) \<triangleleft>trop F exp1 (&v) exp2\<triangleright>\<^sub>r (v:== (trop G exp1 (&v) exp2))) =
         (v:== (trop If (trop F exp1 E exp2) (trop F exp1 E exp2) (trop G exp1 E exp2)))" 
  using 1 2 3
  by rel_auto

lemma assign_cond_If_trop2[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2"
  shows "((v:== E);; 
          (v:== (trop F (&v) exp1 exp2)) \<triangleleft>trop F (&v) exp1 exp2\<triangleright>\<^sub>r (v:== (trop G (&v) exp1 exp2))) =
         (v:== (trop If (trop F E exp1 exp2) (trop F E exp1 exp2) (trop G E exp1 exp2)))" 
  using 1 2 3
  by rel_auto

lemma assign_cond_If_trop3[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2" and 4:"v \<sharp> exp3" and 5:"v \<sharp> exp4"
  shows "((v:== E);;
          (v:== (trop F exp1 exp2 (&v))) \<triangleleft>trop F exp1 exp2 (&v)\<triangleright>\<^sub>r (v:== (trop G exp3 exp4 (&v)))) =
         (v:== (trop If (trop F exp1 exp2 E) (trop F exp1 exp2 E) (trop G exp3 exp4 E)))" 
  using 1 2 3 4 5
  by rel_auto

lemma assign_cond_If_trop4[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2" and 4:"v \<sharp> exp3" and 5:"v \<sharp> exp4"
  shows "((v:== E);; 
         (v:== (trop F exp1 (&v) exp2)) \<triangleleft>trop F exp1 (&v) exp2\<triangleright>\<^sub>r (v:== (trop G exp3 (&v) exp4))) =
         (v:== (trop If (trop F exp1 E exp2) (trop F exp1 E exp2) (trop G exp3 E exp4)))" 
  using 1 2 3 4 5
  by rel_auto

lemma assign_cond_If_trop5[symbolic_exec_assign_trop]:
  assumes 1: "mwb_lens v" and 2:"v \<sharp> exp1" and 3:"v \<sharp> exp2" and 4:"v \<sharp> exp3" and 5:"v \<sharp> exp4"
  shows "((v:== E);; 
          (v:== (trop F (&v) exp1 exp2)) \<triangleleft>trop F (&v) exp1 exp2\<triangleright>\<^sub>r (v:== (trop G (&v) exp3 exp4))) =
         (v:== (trop If (trop F E exp1 exp2) (trop F E exp1 exp2) (trop G E exp3 exp4)))" 
  using 1 2 3 4 5
  by rel_auto

subsection {*Conditional Laws*}
text{*In this section we introduce the algebraic laws of programming related to the conditional
      statement.*}

lemma cond_idem[symbolic_exec]:
  "(IF b THEN P ELSE P) = P" 
  by rel_auto

lemma cond_symm:
  "(IF b THEN P ELSE Q) = (IF \<not> b THEN Q ELSE P)" 
  by rel_auto

lemma cond_assoc: 
  "(IF b THEN P ELSE (IF b THEN Q ELSE R)) =  
   (IF b THEN (IF b THEN P ELSE Q) ELSE R)"  
   by rel_auto

lemma cond_distr[symbolic_exec]: 
  "(IF b THEN (IF b' THEN P ELSE R) ELSE (IF b' THEN Q ELSE R))=  
   (IF b' THEN (IF b THEN P ELSE Q) ELSE R)" 
  by rel_auto

lemma cond_unit_T [simp, symbolic_exec_ex]:"(IF true THEN P ELSE Q) = P" 
  by rel_auto

lemma cond_unit_F [simp, symbolic_exec_ex]:"(IF false THEN P ELSE Q) = Q" 
  by rel_auto

lemma cond_and_T_integrate[symbolic_exec]:
  "((P \<and> b) \<or> (IF b THEN Q ELSE R)) = (IF b THEN (P \<or> Q) ELSE R)"
  by rel_auto

lemma cond_L6[symbolic_exec]: 
  "(IF b THEN P ELSE (IF b THEN Q ELSE R)) = 
   (IF b THEN P ELSE R)" 
  by rel_auto

lemma cond_L7[symbolic_exec]: 
  "(IF b THEN P ELSE (IF c THEN P ELSE Q)) = 
   (IF b \<or> c THEN P ELSE Q)"
  by rel_auto

lemma cond_and_distr[symbolic_exec]: 
  "(IF b THEN (P \<and> Q) ELSE (R \<and> S)) = 
   ((IF b THEN P ELSE R) \<and> (IF b THEN Q ELSE S))"  
  by rel_auto

lemma cond_or_distr[symbolic_exec]: 
  "(IF b THEN (P \<or> Q) ELSE (R \<or> S)) = 
   ((IF b THEN P ELSE R) \<or> (IF b THEN Q ELSE S))" 
  by rel_auto

lemma cond_imp_distr[symbolic_exec]:
  "(IF b THEN (P \<Rightarrow> Q) ELSE (R \<Rightarrow> S)) = 
   ((IF b THEN P ELSE R) \<Rightarrow> (IF b THEN Q ELSE S))" 
  by rel_auto

lemma cond_eq_distr[symbolic_exec]:
  "(IF b THEN (P \<Leftrightarrow> Q) ELSE (R \<Leftrightarrow> S)) = 
   ((IF b THEN P ELSE R) \<Leftrightarrow> (IF b THEN Q ELSE S))"
  by rel_auto

lemma cond_conj_distr[symbolic_exec]:
  "(P \<and> (IF b THEN Q ELSE S)) = (IF b THEN (P \<and> Q) ELSE (P \<and> S))"  
  by rel_auto

lemma cond_disj_distr [symbolic_exec]:
  "(P \<or> (IF b THEN Q ELSE S)) = (IF b THEN (P \<or> Q) ELSE (P \<or> S))" 
  by rel_auto 

lemma cond_neg[symbolic_exec]: 
  "\<not> (IF b THEN P ELSE Q) = (IF b THEN (\<not> P) ELSE (\<not> Q))"
  by rel_auto 

(*lemma cond_USUP_dist: 
  "IF b THEN (\<Squnion> P\<in>S \<bullet> F(P)) ELSE (\<Squnion> P\<in>S \<bullet> G(P)) = (IF b THEN \<Squnion> P\<in>S \<bullet> F(P) ELSE G(P))"
  by (subst uexpr_eq_iff, auto simp add: disj_upred_def conj_upred_def not_upred_def cond_def UINF.rep_eq uminus_uexpr_def inf_uexpr.rep_eq sup_uexpr.rep_eq uop.rep_eq bop.rep_eq lit.rep_eq)

lemma cond_UINF_dist: "(\<Sqinter> P\<in>S \<bullet> F(P)) \<triangleleft> b \<triangleright> (\<Sqinter> P\<in>S \<bullet> G(P)) = (\<Sqinter> P\<in>S \<bullet> F(P) \<triangleleft> b \<triangleright> G(P))"
  by (subst uexpr_eq_iff, auto simp add: disj_upred_def conj_upred_def not_upred_def cond_def USUP.rep_eq uminus_uexpr_def inf_uexpr.rep_eq sup_uexpr.rep_eq uop.rep_eq bop.rep_eq lit.rep_eq)
*)

lemma cond_conj[symbolic_exec]: 
  "(IF b \<and> c THEN P ELSE Q) = IF b THEN (IF c THEN P ELSE Q) ELSE Q"
  by rel_auto 
    

(*IF Theorem by Hoare: It optimize nested IF*)
theorem COND12[symbolic_exec]: 
  "(IF bexp1 THEN (IF bexp2 THEN C1 ELSE C3) ELSE (IF bexp3 THEN C2 ELSE C3)) =
   (IF (trop If bexp1 bexp2 bexp3) THEN (IF bexp1 THEN C1 ELSE C2) ELSE C3)"
  by rel_auto 
 
lemma comp_cond_left_distr:
  "((P \<triangleleft> b \<triangleright>\<^sub>r Q) ;; R) = ((P ;; R) \<triangleleft> b \<triangleright>\<^sub>r (Q ;; R))"
  by rel_auto
 
lemma cond_var_subst_left:
  assumes "vwb_lens x"
  shows "(IF &x THEN P\<lbrakk>true/x\<rbrakk> ELSE Q) = (IF  &x THEN P ELSE Q)"
  using assms
  by (metis cond_def conj_var_subst pr_var_def upred_eq_true utp_pred.inf.commute)

lemma cond_var_subst_right:
  assumes "vwb_lens x"
  shows "(IF &x THEN P ELSE Q\<lbrakk>false/x\<rbrakk>) = (IF &x THEN P ELSE Q)"
  using assms
  by (metis cond_def  conj_var_subst pr_var_def upred_eq_false utp_pred.inf.commute)


lemma cond_var_split:
  "vwb_lens x \<Longrightarrow> (IF &x THEN P\<lbrakk>true/x\<rbrakk> ELSE P\<lbrakk>false/x\<rbrakk>) = P"
  by (rel_auto, (metis (full_types) vwb_lens.put_eq)+)

lemma cond_seq_left_distr:
  "out\<alpha> \<sharp> b \<Longrightarrow> ((IF b THEN P ELSE Q) ;; R) = (IF b THEN (P ;; R) ELSE (Q ;; R))"
  by rel_auto

lemma cond_seq_right_distr:
  "in\<alpha> \<sharp> b \<Longrightarrow> (P ;; (IF b THEN Q ELSE R)) = (IF b THEN (P ;; Q) ELSE (P ;; R))"
  by rel_auto

subsection {*Sequential Laws*}
text{*In this section we introduce the algebraic laws of programming related to the sequential
      composition of statements.*}


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

lemma seqr_assoc: "P ;; (Q ;; R) = (P ;; Q) ;; R"
  by rel_auto

lemma seqr_or_distl:
  "((P \<or> Q) ;; R) = ((P ;; R) \<or> (Q ;; R))"
  by rel_auto

lemma seqr_or_distr:
  "(P ;; (Q \<or> R)) = ((P ;; Q) \<or> (P ;; R))"
  by rel_auto

lemma seqr_unfold:
  "(P ;; Q) = (\<^bold>\<exists> v \<bullet> P\<lbrakk>\<guillemotleft>v\<guillemotright>/$\<Sigma>\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$\<Sigma>\<rbrakk>)"
  by rel_auto

lemma seqr_middle:
  assumes "vwb_lens x"
  shows "(P ;; Q) = (\<^bold>\<exists> v \<bullet> P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  using assms
  apply (rel_auto)
  apply (rename_tac xa P Q a b y)
  apply (rule_tac x="get\<^bsub>xa\<^esub> y" in exI)
  apply (rule_tac x="y" in exI)
  apply (simp)
done

lemma seqr_left_one_point:
  assumes "vwb_lens x"
  shows "((P \<and> $x\<acute> =\<^sub>u \<guillemotleft>v\<guillemotright>) ;; Q) = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  using assms
  by (rel_auto, metis vwb_lens_wb wb_lens.get_put)

lemma seqr_right_one_point:
  assumes "vwb_lens x"
  shows "(P ;; ($x =\<^sub>u \<guillemotleft>v\<guillemotright> \<and> Q)) = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  using assms
  by (rel_auto, metis vwb_lens_wb wb_lens.get_put)

lemma seqr_insert_ident_left:
  assumes "vwb_lens x" "$x\<acute> \<sharp> P" "$x \<sharp> Q"
  shows "(($x\<acute> =\<^sub>u $x \<and> P) ;; Q) = (P ;; Q)"
  using assms
  by (rel_auto, meson vwb_lens_wb wb_lens_weak weak_lens.put_get)

lemma seqr_insert_ident_right:
  assumes "vwb_lens x" "$x\<acute> \<sharp> P" "$x \<sharp> Q"
  shows "(P ;; ($x\<acute> =\<^sub>u $x \<and> Q)) = (P ;; Q)"
  using assms
  by (rel_auto, metis (no_types, hide_lams) vwb_lens_def wb_lens_def weak_lens.put_get)

lemma seq_var_ident_lift:
  assumes "vwb_lens x" "$x\<acute> \<sharp> P" "$x \<sharp> Q"
  shows "(($x\<acute> =\<^sub>u $x \<and> P) ;; ($x\<acute> =\<^sub>u $x \<and> Q)) = ($x\<acute> =\<^sub>u $x \<and> (P ;; Q))"
  using assms
  by (rel_auto, metis (no_types, lifting) vwb_lens_wb wb_lens_weak weak_lens.put_get)

lemma seqr_skip: "SKIP ;; C = C ;; SKIP"
  by (metis seqr_left_unit seqr_right_unit)

(*The rules SEQ6 SEQ7 related to SEQ and non-deterministic choice are missing for now*)
  
subsection {*While laws*}
text{*In this section we introduce the algebraic laws of programming related to the while
      statement.*}

theorem while_unfold:
  "WHILE b DO P OD = ((P ;; WHILE b DO P OD) \<triangleleft> b \<triangleright>\<^sub>r SKIP)"
proof -
  have m:"mono (\<lambda>X. (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r SKIP)"
    by (auto intro: monoI seqr_mono cond_mono)
  have "(WHILE b DO P OD) = (\<nu> X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r SKIP)"
    by (simp add: While_def)
  also have "... = ((P ;; (\<nu> X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r SKIP)) \<triangleleft> b \<triangleright>\<^sub>r SKIP)"
    by (subst lfp_unfold, simp_all add: m)
  also have "... = ((P ;; WHILE b DO P OD) \<triangleleft> b \<triangleright>\<^sub>r SKIP)"
    by (simp add: While_def)
  finally show ?thesis .
qed

lemma while_true:
  assumes 1:"b = true"
  shows "(WHILE b DO P OD) = (P ;; WHILE b DO P OD)"
proof -
  have "(WHILE b DO P OD) = (P ;; WHILE b DO P OD) \<triangleleft> b \<triangleright>\<^sub>r SKIP" 
    using while_unfold[of b P] by simp
  also have "... = (P ;; WHILE b DO P OD)" 
    using 1 by (simp add: aext_true)
  finally show ?thesis .
qed

lemma while_false:
  assumes 1:"b = false"
  shows "(WHILE b DO P OD) = SKIP"
proof -
  have "(WHILE b DO P OD) = (P ;; WHILE b DO P OD) \<triangleleft> b \<triangleright>\<^sub>r SKIP" 
    using while_unfold[of b P] by simp
  also have "... = SKIP" 
    using 1 by (simp add: aext_false)
  finally show ?thesis . 
qed

subsection {*assume and assert laws*}
lemma assume_twice: "(b\<^sup>\<top> ;; c\<^sup>\<top>) = (b \<and> c)\<^sup>\<top>"
  by rel_auto

lemma assert_twice: "(b\<^sub>\<bottom> ;; c\<^sub>\<bottom>) = (b \<and> c)\<^sub>\<bottom>" 
  by rel_auto

subsection {*Tactic setup*}
text {*In this section we will design a tactic that can be used to automate
       the process of program optimization.*}

method rel_simp' =
  (unfold upred_defs urel_defs)?,
  transfer',
  (simp add: fun_eq_iff relcomp_unfold OO_def
    lens_defs upred_defs Product_Type.split_beta)?,
  (simp add: lens_interp_laws)?,
  clarsimp?
method rel_auto' = rel_simp', auto?

method symbolic_exec_commands =
  (simp add: symbolic_exec)?,
  ((subst symbolic_exec symbolic_exec_ex)+)?,
  (simp add: symbolic_exec_assign_uop)?,
  ((subst symbolic_exec_assign_uop)+)?,
  (simp add: symbolic_exec_assign_bop)?,
  ((subst symbolic_exec_assign_bop)+)?,
  (simp add: symbolic_exec_assign_trop)?,
  ((subst symbolic_exec_assign_trop)+)?,
  (simp add: symbolic_exec_assign_qtop)?,
  ((subst symbolic_exec_assign_qtop)+)?,
  transfer'?,
  rel_auto'?

lemmas symbolic_exec_all =
  symbolic_exec
  symbolic_exec_assign_uop
  symbolic_exec_assign_bop
  symbolic_exec_assign_trop
  symbolic_exec_assign_qtop

method symbolic_exec_commands_min =
  (simp add: symbolic_exec_all)?,
  ((subst symbolic_exec_all symbolic_exec_ex)+)?,
  transfer'?,
  rel_auto?

end