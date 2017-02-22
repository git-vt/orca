section {*Algebraic laws of programming*}

text{*In this section we introduce the semantic rules related to the different
      statements of IMP. In the literature this also known as the algebraic laws of programming.
      In our framework we will use these rules in order to optimize a given program written in our 
      language, and this before any deductive proof verification activity or formal testing.*}

theory Algebraic_Laws
imports Commands
begin

named_theorems small_step(*legacy*) and  symbolic_exec_subst
 

subsection {*SKIP Laws*}
text{*In this section we introduce the algebraic laws of programming related to the SKIP
      statement.*}

lemma SKI0 [symbolic_exec_subst]:
  "SKIP ; C = C"
  by auto

lemma SKI1[symbolic_exec_subst]:
  "C ; SKIP = C"
  by auto

subsection {*Assignment Laws*}
text{*In this section we introduce the algebraic laws of programming related to the assignment
      statement.*}

lemma ASN_test:
  assumes 1:"mwb_lens x" 
  shows     "(x :== \<guillemotleft>u\<guillemotright> ; x :== \<guillemotleft>v\<guillemotright>) = (x :== \<guillemotleft>v\<guillemotright>)"
  using 1 unfolding subst_upd_var_def 
  by transfer auto

lemma ASN_cancel:
  assumes 1:"weak_lens var" 
  shows "(var :== expr)\<dagger> (VAR var) = expr"
  using 1 unfolding subst_upd_var_def
  by transfer auto

lemma ASN0[small_step]:
  "(var:== exp ; C) = C o [var \<mapsto>\<^sub>s exp]" ..

lemma ASN1[small_step]: 
  "(var:== exp ; C) \<dagger> P = [var \<mapsto>\<^sub>s exp] \<dagger> (C \<dagger> P)"
  by transfer simp
 
lemma ASN2[small_step]: 
  "(var:== exp ; C) = [var \<mapsto>\<^sub>s exp] \<dagger> C"
  unfolding SKI1 subst_subst
  by transfer auto 

lemma ASN3[small_step]: 
  assumes 1:"var \<sharp>\<sharp> C"
  shows"(var:== exp ; C) = C (var \<mapsto>\<^sub>s exp)"
  using 1 unfolding unrest_usubst_def ASN2 SKI1 subst_upd_var_def 
  by transfer auto 

text {*In the sequel we find assign laws which are in Simon Foster paper*}
text {*The rules in the sequel are too generic. 
       We can not use these rules naively in an automatic tactic for optimizing the program. 
       To be applied to a given program this rule needs some knowledge, eg., annotations
       saying that @{text "var \<sharp> exp2"} is true.*}

lemma ASN4: 
  assumes 1: "mwb_lens var" 
  and  2: "var \<sharp> exp2" (*Thats why he needs the concept of unrest in his theory*)
  shows "(var:== exp1 ; var:== exp2) = var:== exp2" 
proof (rule ext)
  fix \<sigma> :: 'b
  have "\<forall>u \<sigma> v. put\<^bsub>var\<^esub> \<sigma> v = put\<^bsub>var\<^esub> (put\<^bsub>var\<^esub> \<sigma> u) v"
    using 1 by auto
  then have "subst_upd SKIP var exp2 \<sigma> = 
             subst_upd SKIP var exp2 (subst_upd SKIP var exp1 \<sigma>)"
    using 2
    by (auto simp add: subst_upd_var_def  unrest.abs_eq)
  then show "(subst_upd SKIP var exp1; subst_upd SKIP var exp2) \<sigma> = 
              subst_upd SKIP var exp2 \<sigma>"
    by (simp add: subst.abs_eq) 
qed

lemma ASN4_uop1[symbolic_exec_subst]: 
  assumes 1: "mwb_lens var"
  shows "(var:== exp1 ; var:== (uop F (VAR var))) = (var:== (uop F exp1))"
  using 1  unfolding subst_upd_var_def unrest_def
  by transfer auto 

lemma ASN4_bop1: 
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp2"
  shows "(var:== exp1 ; var:== (bop bp (VAR var) exp2)) = (var:== (bop bp exp1 exp2))"
  using 1 2  unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN4_bop2: 
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp2"
  shows "(var:== exp1 ; var:== (bop bp exp2 (VAR var))) = (var:== (bop bp exp2 exp1))"
  using 1 2 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN4_trop1: 
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp2" and 3:"var \<sharp> exp3"
  shows "(var:== exp1 ; var:== (trop tp (VAR var) exp2 exp3)) = 
         (var:== (trop tp exp1 exp2 exp3))"
  using 1 2 3 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN4_trop2: 
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp2" and 3:"var \<sharp> exp3"
  shows "(var:== exp1 ; var:== (trop tp exp2 (VAR var) exp3)) = 
         (var:== (trop tp exp2 exp1 exp3))"
  using 1 2 3 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN4_trop3: 
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp2" and 3:"var \<sharp> exp3"
  shows "(var:== exp1 ; var:== (trop tp exp2 exp3 (VAR var))) = 
         (var:== (trop tp exp2 exp3 exp1))"
  using 1 2 3 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN4_qtop1: 
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp2" and 3:"var \<sharp> exp3" and 4:"var \<sharp> exp4"
  shows "(var:== exp1 ; var:== (qtop tp (VAR var) exp2 exp3 exp4)) = 
         (var:== (qtop tp exp1 exp2 exp3 exp4))"
  using 1 2 3 4 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN4_qtop2: 
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp2" and 3:"var \<sharp> exp3" and 4:"var \<sharp> exp4"
  shows "(var:== exp1 ; var:== (qtop tp exp2 (VAR var) exp3 exp4)) = 
         (var:== (qtop tp exp2 exp1 exp3 exp4))"
  using 1 2 3 4 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN4_qtop3: 
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp2" and 3:"var \<sharp> exp3" and 4:"var \<sharp> exp4"
  shows "(var:== exp1 ; var:== (qtop tp exp2 exp3 (VAR var) exp4)) = 
         (var:== (qtop tp exp2 exp3 exp1 exp4))"
  using 1 2 3 4 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN4_qtop4: 
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp2" and 3:"var \<sharp> exp3" and 4:"var \<sharp> exp4"
  shows "(var:== exp1 ; var:== (qtop tp exp2 exp3 exp4 (VAR var))) = 
         (var:== (qtop tp exp2 exp3 exp4 exp1))"
  using 1 2 3 4 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN5:
  assumes  1: "var1 \<sharp> exp2"
  and  2: "var2 \<sharp> exp1"
  and  3: "var1 \<bowtie> var2"
  shows "(var1:== exp1 ; var2:== exp2) = (var2:== exp2 ; var1:== exp1)" 
proof (rule ext)
  fix \<sigma> :: 'b
  have h1: "\<And>subst var \<sigma> v. subst_upd subst (var::'a \<Longrightarrow> 'b) exp1 (put\<^bsub>var2\<^esub> \<sigma> v) = 
           put\<^bsub>var\<^esub> (subst (put\<^bsub>var2\<^esub> \<sigma> v)) (exp1 \<sigma>)"
    using 2 by (simp add: unrest.abs_eq subst_upd_var_def) 
  have "var1 \<bowtie> var2" 
    using 3 by simp
  then have "put\<^bsub>var1\<^esub> (put\<^bsub>var2\<^esub> \<sigma> (exp2 \<sigma>)) (exp1 \<sigma>) = 
             put\<^bsub>var2\<^esub> (put\<^bsub>var1\<^esub> \<sigma> (exp1 \<sigma>)) (exp2 \<sigma>)"
    by (simp add: lens_indep_comm)
  then have "subst_upd SKIP var2 exp2 (put\<^bsub>var1\<^esub> \<sigma> (exp1 \<sigma>)) = 
             put\<^bsub>var1\<^esub> (put\<^bsub>var2\<^esub> \<sigma> (exp2 \<sigma>)) (exp1 \<sigma>)"
    using 1 unfolding subst_upd_var_def by transfer simp
  then have "(subst_upd SKIP var1 exp1; subst_upd SKIP var2 exp2) \<sigma> = 
             put\<^bsub>var1\<^esub> (put\<^bsub>var2\<^esub> \<sigma> (exp2 \<sigma>)) (exp1 \<sigma>)"
    unfolding subst_upd_var_def by transfer simp
  then have "(subst_upd SKIP var1 exp1; subst_upd SKIP var2 exp2) \<sigma> = 
              subst_upd SKIP var1 exp1 (put\<^bsub>var2\<^esub> \<sigma> (exp2 \<sigma>))"
    using h1 by simp
  then show "(subst_upd SKIP var1 exp1; subst_upd SKIP var2 exp2) \<sigma> = 
             (subst_upd SKIP var2 exp2; subst_upd SKIP var1 exp1) \<sigma>"
    unfolding subst_upd_var_def by transfer simp
qed

lemma ASN6[symbolic_exec_subst]:
  "(IF ([var \<mapsto>\<^sub>s exp] \<dagger> bexp) THEN (var:== exp ; C1) ELSE (var:== exp ; C2)) = 
   (var:== exp ; IF bexp THEN C1 ELSE C2)" 
  by transfer auto

text {*In the sequel we find assignment laws proposed by Hoare*}

lemma ASN8:
  assumes 1: "vwb_lens var"
  shows "(var:== VAR var) = SKIP"
  using 1 usubst_upd_var_id [of var]
  by simp

lemma ASN9:
  assumes 1: "mwb_lens var1"
  and     2: "vwb_lens var2"
  and     3: "var1 \<bowtie> var2"
  shows"[var1 \<mapsto>\<^sub>s exp, var2 \<mapsto>\<^sub>s (VAR var2)] = (var1:== exp)"
  using 1 2 3 unfolding subst_upd_var_def subst.abs_eq imp_var.abs_eq id_def
proof -
  { fix \<sigma> :: 'b
    have "put\<^bsub>var1\<^esub> \<sigma> (exp \<sigma>) = put\<^bsub>var2\<^esub> (put\<^bsub>var1\<^esub> \<sigma> (exp \<sigma>)) (get\<^bsub>var2\<^esub> \<sigma>)"
      using 3 2 lens_indep_comm
      by (metis vwb_lens_wb wb_lens.get_put)
 }
  then show "(\<lambda>\<sigma>. put\<^bsub>var2\<^esub> (put\<^bsub>var1\<^esub> \<sigma> (exp \<sigma>)) (get\<^bsub>var2\<^esub> \<sigma>)) = 
             (\<lambda>\<sigma>. put\<^bsub>var1\<^esub> \<sigma> (exp \<sigma>))" 
    by auto
qed

lemma ASN10[small_step]:
  assumes  1: "vwb_lens var2"
  shows"(var1:== exp); (var2 :== (VAR var2)) = (var1:== exp)"
  using 1 ASN8[of var2]
  by simp 

lemma ASN11_uop[symbolic_exec_subst]:
  assumes 1: "weak_lens var"
  shows "(IF (uop F exp) THEN (var:== exp ; C1) ELSE (var:== exp ; C2)) = 
         (var:== exp ; IF (uop F (VAR var)) THEN C1 ELSE C2)"
  using 1 unfolding subst_upd_var_def 
  by transfer auto 

lemma ASN11_bop1:
  assumes 1: "weak_lens var" and 2: "var \<sharp> exp2"
  shows "(var:== exp ; IF (bop bp (VAR var) exp2) THEN C1 ELSE C2) = 
         (IF (bop bp exp exp2) THEN (var:== exp ; C1) ELSE (var:== exp ; C2))"
  using 1 2 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN11_bop2:
  assumes 1: "weak_lens var" and 2: "var \<sharp> exp2"
  shows "(var:== exp1 ; IF (bop bp exp2 (VAR var)) THEN C1 ELSE C2) = 
         (IF (bop bp exp2 exp1) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2))"
  using 1 2 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN11_trop1:
  assumes 1: "weak_lens var" and 2: "var \<sharp> exp2" and 3: "var \<sharp> exp3"
  shows "(var:== exp ; IF (trop tp (VAR var) exp2 exp3) THEN C1 ELSE C2) = 
         (IF (trop tp exp exp2 exp3) THEN (var:== exp ; C1) ELSE (var:== exp ; C2))"
  using 1 2 3 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN11_trop2:
  assumes 1: "weak_lens var" and 2: "var \<sharp> exp2" and 3: "var \<sharp> exp3"
  shows "(var:== exp1 ; IF (trop tp exp2 (VAR var) exp3) THEN C1 ELSE C2) = 
         (IF (trop tp exp2 exp1 exp3) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2))"
  using 1 2 3 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN11_trop3:
  assumes 1: "weak_lens var" and 2: "var \<sharp> exp2" and 3: "var \<sharp> exp3"
  shows "(var:== exp1 ; IF (trop bp exp2 exp3 (VAR var)) THEN C1 ELSE C2) = 
         (IF (trop bp exp2 exp3 exp1) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2))"
  using 1 2 3 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN11_qtop1:
  assumes 1: "weak_lens var" and 2: "var \<sharp> exp2" and 3: "var \<sharp> exp3" and 4: "var \<sharp> exp4"
  shows "(var:== exp1 ; IF (qtop tp (VAR var) exp2 exp3 exp4) THEN C1 ELSE C2) = 
         (IF (qtop tp exp1 exp2 exp3  exp4) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2))"
  using 1 2 3 4 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN11_qtop2:
  assumes 1: "weak_lens var" and 2: "var \<sharp> exp2" and 3: "var \<sharp> exp3" and 4:"var \<sharp> exp4"
  shows "(var:== exp1 ; IF (qtop tp exp2 (VAR var) exp3 exp4) THEN C1 ELSE C2) = 
         (IF (qtop tp exp2 exp1 exp3 exp4) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2))"
  using 1 2 3 4 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN11_qtop3:
  assumes 1: "weak_lens var" and 2: "var \<sharp> exp2" and 3: "var \<sharp> exp3" and 4: "var \<sharp> exp4"
  shows "(var:== exp1 ; IF (qtop bp exp2 exp3 (VAR var) exp4) THEN C1 ELSE C2) = 
         (IF (qtop bp exp2 exp3 exp1  exp4) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2))"
  using 1 2 3 4 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN11_qtop4:
  assumes 1: "weak_lens var" and 2: "var \<sharp> exp2" and 3: "var \<sharp> exp3" and 4: "var \<sharp> exp4"
  shows "(var:== exp1 ; IF (qtop bp exp2 exp3 exp4 (VAR var)) THEN C1 ELSE C2) = 
         (IF (qtop bp exp2 exp3  exp4 exp1) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2))"
  using 1 2 3 4 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN12[symbolic_exec_subst]:
  "(IF bexp THEN (var:== exp1) ELSE (var:== exp2)) = 
   (var :== (trop If bexp exp1 exp2))" 
   unfolding subst_upd_var_def 
   by transfer auto 

lemma ASN13_uop[symbolic_exec_subst]:
  assumes 1: "mwb_lens var"
  shows "((var:== E); 
          IF uop F (VAR var) THEN (var:== (uop F (VAR var))) ELSE (var:== (uop G (VAR var)))) =
         (var:== (trop If (uop F E) (uop F E) (uop G E)))" 
  using 1 unfolding subst_upd_var_def 
  by transfer auto

lemma ASN13_bop:
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp"
  shows "((var:== E); 
          IF bop F exp (VAR var)  THEN (var:== (bop F exp (VAR var))) ELSE (var:== (bop G exp (VAR var)))) =
         (var:== (trop If (bop F exp E) (bop F exp E) (bop G exp E)))" 
  using 1 2 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN13_bop1:
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp"
  shows "((var:== E); 
          IF bop F (VAR var) exp THEN (var:== (bop F (VAR var) exp)) ELSE (var:== (bop G (VAR var) exp))) =
         (var:== (trop If (bop F E exp) (bop F E exp) (bop G E exp)))" 
  using 1 2 unfolding subst_upd_var_def unrest_def
  by transfer auto 

lemma ASN13_bop2:
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp1" and 3:"var \<sharp> exp2"
  shows "((var:== E); 
          IF bop F (VAR var) exp1 THEN (var:== (bop F (VAR var) exp1)) ELSE (var:== (bop G (VAR var) exp2))) =
         (var:== (trop If (bop F E exp1) (bop F E exp1) (bop G E exp2)))" 
  using 1 2 3 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN13_bop3:
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp"
  shows "((var:== E); 
          IF bop F exp (VAR var)  THEN (var:== (bop F exp (VAR var))) ELSE (var:== (bop G exp (VAR var)))) =
         (var:== (trop If (bop F exp E) (bop F exp E) (bop G exp E)))" 
  using 1 2 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN13_bop4:
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp1" and 3:"var \<sharp> exp2"
  shows "((var:== E); 
          IF bop F (VAR var) exp1 THEN (var:== (bop F (VAR var) exp1)) ELSE (var:== (bop G exp2 (VAR var)))) =
         (var:== (trop If (bop F E exp1) (bop F E exp1) (bop G exp2 E)))" 
  using 1 2 3 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN13_bop5:
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp1" and 3:"var \<sharp> exp2"
  shows "((var:== E); 
          IF bop F exp1 (VAR var) THEN (var:== (bop F exp1 (VAR var))) ELSE (var:== (bop G (VAR var) exp2))) =
         (var:== (trop If (bop F exp1 E) (bop F exp1 E) (bop G E exp2)))" 
  using 1 2 3 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN13_bop6:
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp1" and 3:"var \<sharp> exp2"
  shows "((var:== E); 
          IF bop F exp1 (VAR var) THEN (var:== (bop F exp1 (VAR var))) ELSE (var:== (bop G exp2 (VAR var)))) =
         (var:== (trop If (bop F exp1 E) (bop F exp1 E) (bop G exp2 E)))" 
  using 1 2 3 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN13_trop:
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp1" and 3:"var \<sharp> exp2"
  shows "((var:== E); 
          IF trop F exp1 exp2 (VAR var)  THEN (var:== (trop F exp1 exp2 (VAR var))) ELSE (var:== (trop G exp1 exp2 (VAR var)))) =
         (var:== (trop If (trop F exp1 exp2 E) (trop F exp1 exp2 E) (trop G exp1 exp2 E)))" 
  using 1 2 3 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN13_trop1:
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp1" and 3:"var \<sharp> exp2"
  shows "((var:== E); 
          IF trop F exp1 (VAR var) exp2 THEN (var:== (trop F exp1 (VAR var) exp2)) ELSE (var:== (trop G exp1 (VAR var) exp2))) =
         (var:== (trop If (trop F exp1 E exp2) (trop F exp1 E exp2) (trop G exp1 E exp2)))" 
  using 1 2 3 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN13_trop2:
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp1" and 3:"var \<sharp> exp2"
  shows "((var:== E); 
          IF trop F (VAR var)  exp1 exp2 THEN (var:== (trop F (VAR var) exp1 exp2)) ELSE (var:== (trop G (VAR var)  exp1 exp2))) =
         (var:== (trop If (trop F E exp1 exp2) (trop F E exp1 exp2) (trop G E exp1 exp2)))" 
  using 1 2 3 unfolding subst_upd_var_def unrest_def
  by transfer auto 

lemma ASN13_trop3:
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp1" and 3:"var \<sharp> exp2" and 4:"var \<sharp> exp3" and 5:"var \<sharp> exp4"
  shows "((var:== E); 
          IF trop F exp1 exp2 (VAR var) THEN (var:== (trop F exp1 exp2 (VAR var))) ELSE (var:== (trop G exp3 exp4 (VAR var)))) =
         (var:== (trop If (trop F exp1 exp2 E) (trop F exp1 exp2 E) (trop G exp3 exp4 E)))" 
  using 1 2 3 4 5 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN13_trop4:
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp1" and 3:"var \<sharp> exp2" and 4:"var \<sharp> exp3" and 5:"var \<sharp> exp4"
  shows "((var:== E); 
          IF trop F exp1 (VAR var) exp2 THEN (var:== (trop F exp1 (VAR var) exp2)) ELSE (var:== (trop G exp3 (VAR var) exp4))) =
         (var:== (trop If (trop F exp1 E exp2) (trop F exp1 E exp2) (trop G exp3 E exp4)))" 
  using 1 2 3 4 5 unfolding subst_upd_var_def unrest_def
  by transfer auto

lemma ASN13_trop5:
  assumes 1: "mwb_lens var" and 2:"var \<sharp> exp1" and 3:"var \<sharp> exp2" and 4:"var \<sharp> exp3" and 5:"var \<sharp> exp4"
  shows "((var:== E); 
          IF trop F (VAR var) exp1 exp2 THEN (var:== (trop F (VAR var) exp1 exp2)) ELSE (var:== (trop G (VAR var) exp3 exp4))) =
         (var:== (trop If (trop F E exp1 exp2) (trop F E exp1 exp2) (trop G E exp3 exp4)))" 
  using 1 2 3 4 5 unfolding subst_upd_var_def unrest_def
  by transfer auto

theorem ASN14:
  assumes "mwb_lens x" and "x \<sharp>\<sharp> \<guillemotleft>SOME \<sigma>. True\<guillemotright>"
  shows
  "((IF b THEN x :== E ELSE \<guillemotleft>SOME \<sigma>. True\<guillemotright>); 
    (IF (uop c (VAR x)) THEN (x :== (uop F (VAR x))) ELSE \<guillemotleft>SOME \<sigma>. True\<guillemotright> )) = 
    (IF (trop If b (uop c  E) \<guillemotleft>False\<guillemotright>) THEN x :== (uop F E) ELSE \<guillemotleft>SOME \<sigma>. True\<guillemotright>)"
  using assms unfolding unrest_usubst_def subst_upd_var_def   
  by transfer auto 

theorem ASN15:
  assumes "mwb_lens x" and "x \<sharp>\<sharp> \<guillemotleft>bot\<guillemotright>"
  shows
  "((IF b THEN x :== E ELSE \<guillemotleft>bot\<guillemotright>); 
    (IF (uop c (VAR x)) THEN (x :== (uop F (VAR x))) ELSE \<guillemotleft>bot\<guillemotright> )) = 
    (IF (trop If b (uop c  E) \<guillemotleft>False\<guillemotright>) THEN x :== (uop F E) ELSE \<guillemotleft>bot\<guillemotright>)"
  using assms unfolding unrest_usubst_def subst_upd_var_def   
  by transfer auto

subsection {*Conditional Laws*}
text{*In this section we introduce the algebraic laws of programming related to the conditional
      statement.*}
 
(*IF True*)
lemma COND1[symbolic_exec_subst]:
  "(IF TRUE THEN C1 ELSE C2) = C1" 
  by transfer simp

(*IF False*)
lemma COND2[symbolic_exec_subst]:
  "(IF FALSE THEN C1 ELSE C2) = C2" 
  by transfer simp

(*IF Idemp*)
lemma COND3[symbolic_exec_subst]:
  "(IF bexp THEN C1 ELSE C1) = C1" 
  by simp

(*IF assoc*)
lemma COND4:
  "(IF bexp THEN C1 ELSE (IF bexp THEN C2 ELSE C3)) =  
   (IF bexp THEN (IF bexp THEN C1 ELSE C2) ELSE C3)" 
  by auto

(*IF inverse*)
lemma COND5:
  "(IF P THEN C1 ELSE C2) = (IF \<not>\<^sub>e P THEN C2 ELSE C1)" 
  by transfer auto

(*IF unfold nested cond*)
lemma COND6[symbolic_exec_subst]:
  "(IF bexp THEN (IF bexp1 THEN C1 ELSE C2) ELSE (IF bexp2 THEN C1 ELSE C2)) = 
   (IF trop If bexp bexp1 bexp2 THEN C1 ELSE C2)" 
  by transfer auto

(*IF ignore*)
lemma COND7[symbolic_exec_subst]:
  "(IF bexp THEN C1 ELSE (IF bexp THEN C2 ELSE C3)) = 
   (IF bexp THEN C1 ELSE C3)" 
  by auto

(*the rules COND8, COND9 and COND10 are related to non-deterministic choice between C1 and C2..
  which is not yet supported by our language*)

(*IF distribute*)
lemma COND11[symbolic_exec_subst]:
  "(IF bexp1 THEN (IF bexp2 THEN C1 ELSE C3) ELSE (IF bexp2 THEN C2 ELSE C3))=  
   (IF bexp2 THEN (IF bexp1 THEN C1 ELSE C2) ELSE C3)" 
  by auto

(*IF Theorem by Hoare: It optimize nested IF*)
theorem COND12[symbolic_exec_subst]: 
  "(IF bexp1 THEN (IF bexp2 THEN C1 ELSE C3) ELSE (IF bexp3 THEN C2 ELSE C3)) =
   (IF (trop If bexp1 bexp2 bexp3) THEN (IF bexp1 THEN C1 ELSE C2) ELSE C3)"
  by transfer auto

lemma COND13:
  assumes 1: "\<lceil>bexp\<rceil>"
  shows 
  "(IF bexp THEN C1 ELSE C2)=  C1"
  using 1 
  by transfer auto

lemma COND14:
  assumes 1: "\<lceil>\<not>\<^sub>e bexp\<rceil>"
  shows 
  "(IF bexp THEN C1 ELSE C2)=  C2"
  using 1 
  by transfer auto

subsection {*Sequential Laws*}
text{*In this section we introduce the algebraic laws of programming related to the sequential
      composition of statements.*}

(*Seq assoc*)
lemma SEQ1: 
  "(C1 ; C2) ; C3 = C1 ; (C2 ; C3)"
  by auto

(*Seq SKIP*)
lemma SEQ2: 
  "(SKIP ; C) = (C ; SKIP)"
  by transfer simp

(*Seq unit 1*)
lemma SEQ3: 
  "((0\<^sub>L :== VAR 0\<^sub>L) ; C) = (C ; (0\<^sub>L :== VAR 0\<^sub>L))"
  unfolding subst_upd_var_def unit_lens_def
  by transfer auto

lemma SEQ4: 
  "(bot ; C) = (C ; bot)"
  unfolding subst_upd_var_def unit_lens_def
 oops

(*Seq unit 2*)

lemma SEQ5: 
  "(bot ; C) = bot" 
oops

(*Seq unit 3*)
lemma SEQ6: 
  "(C ; bot) = bot"
  by auto

(*The rules SEQ6 SEQ7 related to SEQ and non-deterministic choice are missing for now*)
  
(*Seq distribution*)
lemma SEQ7[symbolic_exec_subst]: 
  "(IF bexp THEN (C1 ; C3) ELSE (C2 ; C3))= 
   ((IF bexp THEN C1 ELSE C2); C3)"
   by transfer auto 

subsection {*While laws*}
text{*In this section we introduce the algebraic laws of programming related to the while
      statement.*}

lemma W_mono: "mono (W b r)"
  unfolding W_def mono_def
  by auto


(* A little complete partial order theory due to Tobias Nipkow, see also IMP as well as 
   Monads-theory. *)
definition chain :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool" 
where     "chain S = (\<forall>i. S i \<subseteq> S(Suc i))"

lemma chain_total: "chain S \<Longrightarrow> S i \<le> S j \<or> S j \<le> S i"
by (metis chain_def le_cases lift_Suc_mono_le)

definition cont :: "('a set \<Rightarrow> 'b set) \<Rightarrow> bool" 
where     "cont f = (\<forall>S. chain S \<longrightarrow> f(UN n. S n) = (UN n. f(S n)))"

lemma mono_if_cont: fixes f :: "'a set => 'b set"
  assumes "cont f" shows "mono f"
proof
  fix a b :: "'a set" assume "a \<subseteq> b"
  let ?S = "\<lambda>n::nat. if n=0 then a else b"
  have "chain ?S" using `a \<subseteq> b` by(auto simp: chain_def)
  hence "f(UN n. ?S n) = (UN n. f(?S n))"
    using assms by(simp add: cont_def)
  moreover have "(UN n. ?S n) = b" using `a \<subseteq> b` by (auto split: if_splits)
  moreover have "(UN n. f(?S n)) = f a \<union> f b" by (auto split: if_splits)
  ultimately show "f a \<subseteq> f b" by (metis Un_upper1)
qed

lemma chain_iterates: fixes f :: "'a set \<Rightarrow> 'a set"
  assumes "mono f" shows "chain(\<lambda>n. (f^^n) {})"
proof-
  { fix n have "(f ^^ n) {} \<subseteq> (f ^^ Suc n) {}" using assms
    by(induction n) (auto simp: mono_def) }
  thus ?thesis by(auto simp: chain_def)
qed

theorem lfp_if_cont:
  assumes "cont f" shows "lfp f = (UN n. (f^^n) {})" (is "_ = ?U")
proof
  show "lfp f \<subseteq> ?U"
  proof (rule lfp_lowerbound)
    have "f ?U = (UN n. (f^^Suc n){})"
      using chain_iterates[OF mono_if_cont[OF assms]] assms
      by(simp add: cont_def)
    also have "\<dots> = (f^^0){} \<union> \<dots>" by simp
    also have "\<dots> = ?U"
      by(auto simp del: funpow.simps) (metis not0_implies_Suc)
    finally show "f ?U \<subseteq> ?U" by simp
  qed
next
  { fix n p assume "f p \<subseteq> p"
    have "(f^^n){} \<subseteq> p"
    proof(induction n)
      case 0 show ?case by simp
    next
      case Suc
      from monoD[OF mono_if_cont[OF assms] Suc] `f p \<subseteq> p`
      show ?case by simp
    qed
  }
  thus "?U \<subseteq> lfp f" by(auto simp: lfp_def)
qed


lemma single_valued_UN_chain:
  assumes "chain S" "(!!n. single_valued (S n))"
  shows "single_valued(UN n. S n)"
proof(auto simp: single_valued_def)
  fix m n x y z assume "(x, y) \<in> S m" "(x, z) \<in> S n"
  with chain_total[OF assms(1), of m n] assms(2)
  show "y = z" by (auto simp: single_valued_def)
qed

lemma single_valued_lfp: 
fixes f :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
assumes "cont f" "\<And>r. single_valued r \<Longrightarrow> single_valued (f r)"
shows "single_valued(lfp f)"
unfolding lfp_if_cont[OF assms(1)]
proof(rule single_valued_UN_chain[OF chain_iterates[OF mono_if_cont[OF assms(1)]]])
  fix n show "single_valued ((f ^^ n) {})"
  by(induction n)(auto simp: assms(2))
qed

lemma cont_W: "cont (W c b)"
  by (auto simp: cont_def W_def)

theorem single_valued_lfp_Fun2Rel: "single_valued (lfp(W c (Rel B)))"
  apply(rule single_valued_lfp, simp_all add: cont_W)
  apply(auto simp: W_def single_valued_def)
  apply (simp add: Commands.Rel_def)
done

lemma Rel2Fun_if:
  "RelInv {(s, t). if b s then (s, t) \<in> Rel c O lfp (\<Gamma> b (Rel c)) else s = t} \<sigma> =
  (if b \<sigma> then RelInv (Rel c O lfp (\<Gamma> b (Rel c))) \<sigma> else  \<sigma>)"
  by (simp add: RelInv_def)


lemma Rel2Fun_Id: "(RelInv \<circ> Rel) x = x"
  by (rule ext, auto simp: comp_def Rel_def RelInv_def)

lemma Rel2Fun_homomorphism:
  assumes determ_X: "single_valued X" and determ_Y: "single_valued Y"
          and "is_total X" and "is_total Y"
  shows   "RelInv (X O Y) = (RelInv Y) o (RelInv X)"
proof - 
    have relational_partial_next_in_O: 
         "\<And>x E F. (\<exists>y. (x, y) \<in> (E O F)) \<Longrightarrow> (\<exists>y. (x, y) \<in> E)" by auto
    have some_eq_intro:
         "\<And> Z x y . single_valued Z \<Longrightarrow> (x, y) \<in> Z \<Longrightarrow> (SOME y. (x, y) \<in> Z) = y"
          by (auto simp: single_valued_def)
    show ?thesis
    proof (rule ext, rename_tac "\<sigma>", simp add: RelInv_def)?
     fix \<sigma> :: 'a
     { fix aa :: 'a
       obtain aaa :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
         ff1: "\<forall>p pa a aa. (\<not> (p OO pa) a aa \<or> p a (aaa p pa a aa) \<and> pa (aaa p pa a aa) aa) \<and> ((\<forall>ab. \<not> p a ab \<or> \<not> pa ab aa) \<or> (p OO pa) a aa)"
         by moura
       { assume "(SOME a. (\<sigma>, a) \<in> X, aa) \<notin> Y"
         moreover
         { assume "(aaa (\<lambda>a aa. (a, aa) \<in> X) (\<lambda>a aa. (a, aa) \<in> Y) \<sigma> aa, aa) \<notin> Y \<and> (SOME a. (\<sigma>, a) \<in> X, aa) \<notin> Y"
           then have "\<not> ((\<lambda>a aa. (a, aa) \<in> X) OO (\<lambda>a aa. (a, aa) \<in> Y)) \<sigma> aa \<and> (SOME a. (\<sigma>, a) \<in> X, aa) \<notin> Y"
             using ff1 by meson }
         ultimately have "(\<sigma>, SOME a. (\<sigma>, a) \<in> X) \<in> X \<longrightarrow> ((SOME a. (\<sigma>, a) \<in> X O Y) = (SOME a. (SOME a. (\<sigma>, a) \<in> X, a) \<in> Y) \<or> (\<sigma>, aa) \<notin> X O Y \<and> (SOME a. (\<sigma>, a) \<in> X, aa) \<notin> Y \<or> (\<sigma>, aa) \<in> X O Y \<and> (SOME a. (\<sigma>, a) \<in> X, aa) \<in> Y) \<or> \<not> ((\<lambda>a aa. (a, aa) \<in> X) OO (\<lambda>a aa. (a, aa) \<in> Y)) \<sigma> aa \<and> (SOME a. (\<sigma>, a) \<in> X, aa) \<notin> Y \<or> (\<sigma>, aaa (\<lambda>a aa. (a, aa) \<in> X) (\<lambda>a aa. (a, aa) \<in> Y) \<sigma> aa) \<notin> X \<and> (SOME a. (\<sigma>, a) \<in> X, aa) \<notin> Y \<or> \<not> ((\<lambda>a aa. (a, aa) \<in> X) OO (\<lambda>a aa. (a, aa) \<in> Y)) \<sigma> aa \<and> (\<sigma>, aa) \<notin> X O Y"
           by (metis (lifting) determ_X some_eq_intro) }
       moreover
       { assume "(\<sigma>, SOME a. (\<sigma>, a) \<in> X) \<notin> X"
         moreover
         { assume "\<exists>a. \<not> ((\<lambda>a aa. (a, aa) \<in> X) OO (\<lambda>a aa. (a, aa) \<in> Y)) \<sigma> aa \<and> (\<sigma>, aa) \<notin> X O Y \<and> (\<sigma>, a) \<in> X"
           then have "\<exists>a p. p (a::'a) (SOME a. (\<sigma>, a) \<in> X) \<and> \<not> (p OO (\<lambda>a aa. (a, aa) \<in> Y)) a aa \<and> (\<sigma>, aa) \<notin> X O Y"
             by (meson exE_some) }
         ultimately have "(\<sigma>, aa) \<in> X O Y \<and> (\<sigma>, SOME a. (\<sigma>, a) \<in> X) \<notin> X \<or> (\<exists>a p. p (a::'a) (SOME a. (\<sigma>, a) \<in> X) \<and> \<not> (p OO (\<lambda>a aa. (a, aa) \<in> Y)) a aa \<and> (\<sigma>, aa) \<notin> X O Y)"
           by (metis (no_types) assms(3) is_total_def relcompp_relcomp_eq)
         then have "(\<exists>a p. p (a::'a) (SOME a. (\<sigma>, a) \<in> X) \<and> \<not> (p OO (\<lambda>a aa. (a, aa) \<in> Y)) a aa \<and> (\<sigma>, aa) \<notin> X O Y) \<or> (\<sigma>, aaa (\<lambda>a aa. (a, aa) \<in> X) (\<lambda>a aa. (a, aa) \<in> Y) \<sigma> aa) \<notin> X \<and> (SOME a. (\<sigma>, a) \<in> X, aa) \<notin> Y \<or> (SOME a. (\<sigma>, a) \<in> X O Y) = (SOME a. (SOME a. (\<sigma>, a) \<in> X, a) \<in> Y) \<or> (\<sigma>, aa) \<notin> X O Y \<and> (SOME a. (\<sigma>, a) \<in> X, aa) \<notin> Y \<or> (\<sigma>, aa) \<in> X O Y \<and> (SOME a. (\<sigma>, a) \<in> X, aa) \<in> Y"
           by (meson exE_some) }
       moreover
       { assume "(\<sigma>, aaa (\<lambda>a aa. (a, aa) \<in> X) (\<lambda>a aa. (a, aa) \<in> Y) \<sigma> aa) \<notin> X \<and> (SOME a. (\<sigma>, a) \<in> X, aa) \<notin> Y"
         then have "\<not> ((\<lambda>a aa. (a, aa) \<in> X) OO (\<lambda>a aa. (a, aa) \<in> Y)) \<sigma> aa \<and> (SOME a. (\<sigma>, a) \<in> X, aa) \<notin> Y"
           using ff1 by meson }
       ultimately have "(SOME a. (\<sigma>, a) \<in> X O Y) = (SOME a. (SOME a. (\<sigma>, a) \<in> X, a) \<in> Y) \<or> (\<sigma>, aa) \<notin> X O Y \<and> (SOME a. (\<sigma>, a) \<in> X, aa) \<notin> Y \<or> (\<sigma>, aa) \<in> X O Y \<and> (SOME a. (\<sigma>, a) \<in> X, aa) \<in> Y"
         by blast }
     then show "(SOME a. (\<sigma>, a) \<in> X O Y) = (SOME a. (SOME a. (\<sigma>, a) \<in> X, a) \<in> Y)"
       by meson
   qed
qed

(*apply (case_tac " \<exists> \<sigma>'. (\<sigma>, \<sigma>') \<in> X O Y")
apply (simp )
apply (frule relational_partial_next_in_O)
apply (auto simp: single_valued_relcomp some_eq_intro determ_X determ_Y relcomp.relcompI)
by (meson assms(3) assms(4) is_total_def relcomp.relcompI)*)

lemma single_valued_Rel: "single_valued (Rel B)"
by (auto simp: single_valued_def Rel_def)


text{* Putting everything together, the theory of embedding and the invariant of
       determinism of the while-body, gives us the usual unfold-theorem: *}

theorem while_unfold:
assumes loop_terminates: "is_total (lfp (W b (Rel c)))"
shows  "(WHILE b DO c OD) = (IF b THEN (c ; (WHILE b DO c OD)) ELSE SKIP)"
proof (rule ext)
  fix \<sigma>
  have h1:"(WHILE b DO c OD) = RelInv (W b (Rel c) (lfp (W b (Rel c)))) "
    using lfp_unfold [OF mono_if_cont, OF cont_W, of b "Rel c"]
    by simp
  show "(WHILE b DO c OD) \<sigma> =
         (IF b THEN c; WHILE b DO c OD ELSE SKIP) \<sigma>"
   by (subst h1, subst W_def) 
      (auto simp: h1 Rel2Fun_if Rel2Fun_homomorphism  Rel2Fun_Id [simplified comp_def] 
                  single_valued_Rel  single_valued_lfp_Fun2Rel loop_terminates)
qed

lemma WHILE2:
  assumes 1:"\<lceil>b\<rceil>" and 2:"is_total (lfp (W b (Rel c)))" 
  shows "(WHILE b DO c OD) = (c; WHILE b DO c OD)"
  using 1 2  
  by (subst while_unfold) (simp_all only: COND13) 

lemma WHILE3:
  assumes 1:" \<lceil>\<not>\<^sub>e b\<rceil>" and 2:"is_total (lfp (W b (Rel c)))"  
  shows "(WHILE b DO c OD) = SKIP"
  using 1 2  
  by transfer (auto simp add: while_unfold) 

subsection {*Laws used by tactics*}
text {*In this section we will design a set of rules that can be used to automatise 
       the process of program optimization.*}

subsubsection {*Assignment rules*}
text {*We will create a variant rule for @{thm ASN4}. The variant rule in the sequel
       can be applied naively in an automatic tactic used for optimizing the program.*}


lemma ASN4_SE1[symbolic_exec_subst]: 
  assumes 1: "mwb_lens var" 
  shows "(var:== exp1 ; var:== \<guillemotleft>exp2\<guillemotright>) = (var:== \<guillemotleft>exp2\<guillemotright>)"
  using 1 unrest_const[of var exp2] ASN4[of var]
  by simp

lemma ASN4_SE2[symbolic_exec_subst]: 
  assumes 1: "mwb_lens var" 
  shows "(var:== exp1 ; var:== (bop bp (VAR var) \<guillemotleft>exp2\<guillemotright>)) = (var:== (bop bp exp1 \<guillemotleft>exp2\<guillemotright>))"
  using 1 unrest_const[of var exp2] ASN4_bop1[of var]
  by auto

lemma ASN4_SE3[symbolic_exec_subst]: 
  assumes 1: "mwb_lens var" 
  shows "(var:== exp1 ; var:== (bop bp \<guillemotleft>exp2\<guillemotright> (VAR var))) = (var:== (bop bp \<guillemotleft>exp2\<guillemotright> exp1))"
  using 1 unrest_const[of var exp2] ASN4_bop2[of var]
  by auto

lemma ASN4_SE4[symbolic_exec_subst]: 
  assumes 1: "mwb_lens var"
  shows "(var:== exp1 ; var:== (trop tp (VAR var) \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright>)) = 
         (var:== (trop tp exp1 \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright>))"
  using 1 unrest_const[of var exp2] unrest_const[of var exp3] ASN4_trop1[of var]
  by auto

lemma ASN4_SE5[symbolic_exec_subst]: 
  assumes 1: "mwb_lens var"
  shows "(var:== exp1 ; var:== (trop tp \<guillemotleft>exp2\<guillemotright> (VAR var) \<guillemotleft>exp3\<guillemotright>)) = 
         (var:== (trop tp \<guillemotleft>exp2\<guillemotright> exp1 \<guillemotleft>exp3\<guillemotright>))"
  using 1 unrest_const[of var exp2] unrest_const[of var exp3] ASN4_trop2[of var]
  by auto

lemma ASN4_SE6[symbolic_exec_subst]: 
  assumes 1: "mwb_lens var"
  shows "(var:== exp1 ; var:== (trop tp \<guillemotleft>exp2\<guillemotright>  \<guillemotleft>exp3\<guillemotright> (VAR var))) = 
         (var:== (trop tp \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> exp1))"
  using 1 unrest_const[of var exp2] unrest_const[of var exp3] ASN4_trop3[of var]
  by auto

lemma ASN4_SE7[symbolic_exec_subst]: 
  assumes 1: "mwb_lens var"
  shows "(var:== exp1 ; var:== (qtop tp (VAR var) \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>)) = 
         (var:== (qtop tp exp1 \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>))"
  using 1 unrest_const[of var exp2] unrest_const[of var exp3] 
          unrest_const[of var exp4] ASN4_qtop1[of var]
  by auto

lemma ASN4_SE8[symbolic_exec_subst]: 
  assumes 1: "mwb_lens var"
  shows "(var:== exp1 ; var:== (qtop tp \<guillemotleft>exp2\<guillemotright> (VAR var) \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>)) = 
         (var:== (qtop tp \<guillemotleft>exp2\<guillemotright> exp1 \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>))"
  using 1 unrest_const[of var exp2] unrest_const[of var exp3] 
          unrest_const[of var exp4] ASN4_qtop2[of var]
  by auto

lemma ASN4_SE9[symbolic_exec_subst]: 
  assumes 1: "mwb_lens var"
  shows "(var:== exp1 ; var:== (qtop tp \<guillemotleft>exp2\<guillemotright>  \<guillemotleft>exp3\<guillemotright> (VAR var) \<guillemotleft>exp4\<guillemotright>)) = 
         (var:== (qtop tp \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> exp1 \<guillemotleft>exp4\<guillemotright>))"
  using 1 unrest_const[of var exp2] unrest_const[of var exp3] 
          unrest_const[of var exp4] ASN4_qtop3[of var]
  by auto

lemma ASN4_SE10[symbolic_exec_subst]: 
  assumes 1: "mwb_lens var"
  shows "(var:== exp1 ; var:== (qtop tp \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright> (VAR var))) = 
         (var:== (qtop tp \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright> exp1))"
  using 1 unrest_const[of var exp2] unrest_const[of var exp3] 
          unrest_const[of var exp4] ASN4_qtop4[of var]
  by auto

lemma ASN11_SE1[symbolic_exec_subst]:
  assumes 1: "weak_lens var"
  shows "(IF (bop bp exp \<guillemotleft>exp2\<guillemotright>) THEN (var:== exp ; C1) ELSE (var:== exp ; C2)) =  
         (var:== exp ; IF (bop bp (VAR var) \<guillemotleft>exp2\<guillemotright>) THEN C1 ELSE C2)"
  using 1 unfolding subst_upd_var_def
  by transfer auto

lemma ASN11_SE2[symbolic_exec_subst]:
  assumes 1: "weak_lens var"
  shows "(IF (bop bp \<guillemotleft>exp2\<guillemotright> exp1) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2)) = 
         (var:== exp1 ; IF (bop bp \<guillemotleft>exp2\<guillemotright> (VAR var)) THEN C1 ELSE C2)"
  using 1 unfolding subst_upd_var_def
  by transfer auto

lemma ASN11_SE3[symbolic_exec_subst]:
  assumes 1: "weak_lens var"
  shows "(IF (trop tp exp1 \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright>) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2))= 
         (var:== exp1 ; IF (trop tp (VAR var) \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright>) THEN C1 ELSE C2)"
  using 1 unfolding subst_upd_var_def
  by transfer auto

lemma ASN11_SE4[symbolic_exec_subst]:
  assumes 1: "weak_lens var"
  shows "(IF (trop tp \<guillemotleft>exp2\<guillemotright> exp1 \<guillemotleft>exp3\<guillemotright>) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2))= 
         (var:== exp1 ; IF (trop tp \<guillemotleft>exp2\<guillemotright> (VAR var) \<guillemotleft>exp3\<guillemotright>) THEN C1 ELSE C2) "
  using 1 unfolding subst_upd_var_def
  by transfer auto

lemma ASN11_SE5[symbolic_exec_subst]:
  assumes 1: "weak_lens var"
  shows "(IF (trop bp \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> exp1) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2)) = 
         (var:== exp1 ; IF (trop bp \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> (VAR var)) THEN C1 ELSE C2)"
  using 1 unfolding subst_upd_var_def
  by transfer auto

lemma ASN11_SE6[symbolic_exec_subst]:
  assumes 1: "weak_lens var" 
  shows "(IF (qtop tp exp1 \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2)) =
         (var:== exp1 ; IF (qtop tp (VAR var) \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>) THEN C1 ELSE C2)"
  using 1 unfolding subst_upd_var_def
  by transfer auto

lemma ASN11_SE7[symbolic_exec_subst]:
  assumes 1: "weak_lens var"
  shows "(IF (qtop tp \<guillemotleft>exp2\<guillemotright> exp1 \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2)) = 
         (var:== exp1 ; IF (qtop tp \<guillemotleft>exp2\<guillemotright> (VAR var) \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>) THEN C1 ELSE C2)"
  using 1 unfolding subst_upd_var_def
  by transfer auto

lemma ASN11_SE8[symbolic_exec_subst]:
  assumes 1: "weak_lens var" 
  shows "(IF (qtop bp \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> exp1 \<guillemotleft>exp4\<guillemotright>) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2)) =  
         (var:== exp1 ; IF (qtop bp \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> (VAR var) \<guillemotleft>exp4\<guillemotright>) THEN C1 ELSE C2)"
  using 1 unfolding subst_upd_var_def
  by transfer auto

lemma ASN11_SE9[symbolic_exec_subst]:
  assumes 1: "weak_lens var" and 2: "var \<sharp> exp2" and 3: "var \<sharp> exp3" and 4: "var \<sharp> exp4"
  shows "(IF (qtop bp \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright> exp1) THEN (var:== exp1 ; C1) ELSE (var:== exp1 ; C2)) = 
         (var:== exp1 ; IF (qtop bp \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright> (VAR var)) THEN C1 ELSE C2)"
  using 1 unfolding subst_upd_var_def
  by transfer auto

lemma ASN13_SE1[symbolic_exec_subst]:
  assumes 1: "mwb_lens var"
  shows "((var:== E); 
          IF bop F (VAR var) \<guillemotleft>exp\<guillemotright> THEN (var:== (bop F (VAR var) \<guillemotleft>exp\<guillemotright>)) ELSE (var:== (bop G (VAR var) \<guillemotleft>exp\<guillemotright>))) =
         (var:== (trop If (bop F E \<guillemotleft>exp\<guillemotright>) (bop F E \<guillemotleft>exp\<guillemotright>) (bop G E \<guillemotleft>exp\<guillemotright>)))" 
  using 1 unfolding subst_upd_var_def
  by transfer auto

lemma ASN13_SE2[symbolic_exec_subst]:
  assumes 1: "mwb_lens var"
  shows "((var:== E); 
          IF bop F \<guillemotleft>exp\<guillemotright> (VAR var)  THEN (var:== (bop F \<guillemotleft>exp\<guillemotright> (VAR var))) ELSE (var:== (bop G \<guillemotleft>exp\<guillemotright> (VAR var)))) =
         (var:== (trop If (bop F \<guillemotleft>exp\<guillemotright> E) (bop F \<guillemotleft>exp\<guillemotright> E) (bop G \<guillemotleft>exp\<guillemotright> E)))" 
  using 1 unrest_const[of var exp] ASN13_bop[of var] 
  by auto

lemma ASN13_SE3[symbolic_exec_subst]:
  assumes 1: "mwb_lens var"
  shows "((var:== E); 
          IF bop F (VAR var) \<guillemotleft>exp1\<guillemotright> THEN (var:== (bop F (VAR var) \<guillemotleft>exp1\<guillemotright>)) ELSE (var:== (bop G (VAR var) \<guillemotleft>exp2\<guillemotright>))) =
         (var:== (trop If (bop F E \<guillemotleft>exp1\<guillemotright>) (bop F E \<guillemotleft>exp1\<guillemotright>) (bop G E \<guillemotleft>exp2\<guillemotright>)))" 
  using 1 unrest_const[of var exp1] unrest_const[of var exp2] ASN13_bop2[of var] 
  by auto

lemma ASN13_SE4[symbolic_exec_subst]:
  assumes 1: "mwb_lens var"
  shows "((var:== E); 
          IF bop F (VAR var) \<guillemotleft>exp1\<guillemotright> THEN (var:== (bop F (VAR var) \<guillemotleft>exp1\<guillemotright>)) ELSE (var:== (bop G \<guillemotleft>exp2\<guillemotright> (VAR var)))) =
         (var:== (trop If (bop F E \<guillemotleft>exp1\<guillemotright>) (bop F E \<guillemotleft>exp1\<guillemotright>) (bop G \<guillemotleft>exp2\<guillemotright> E)))" 
  using 1 unrest_const[of var exp1] unrest_const[of var exp2] ASN13_bop4[of var] 
  by auto

lemma ASN13_SE5[symbolic_exec_subst]:
  assumes 1: "mwb_lens var"
  shows "((var:== E); 
          IF bop F \<guillemotleft>exp1\<guillemotright> (VAR var) THEN (var:== (bop F \<guillemotleft>exp1\<guillemotright> (VAR var))) ELSE (var:== (bop G (VAR var) \<guillemotleft>exp2\<guillemotright>))) =
         (var:== (trop If (bop F \<guillemotleft>exp1\<guillemotright> E) (bop F \<guillemotleft>exp1\<guillemotright> E) (bop G E \<guillemotleft>exp2\<guillemotright>)))" 
  using 1 unrest_const[of var exp1] unrest_const[of var exp2] ASN13_bop5[of var] 
  by auto

lemma ASN13_SE6[symbolic_exec_subst]:
  assumes 1: "mwb_lens var"
  shows "((var:== E); 
          IF bop F \<guillemotleft>exp1\<guillemotright> (VAR var) THEN (var:== (bop F \<guillemotleft>exp1\<guillemotright> (VAR var))) ELSE (var:== (bop G \<guillemotleft>exp2\<guillemotright> (VAR var)))) =
         (var:== (trop If (bop F \<guillemotleft>exp1\<guillemotright> E) (bop F \<guillemotleft>exp1\<guillemotright> E) (bop G \<guillemotleft>exp2\<guillemotright> E)))" 
  using 1 unrest_const[of var exp1] unrest_const[of var exp2] ASN13_bop6[of var] 
  by auto                                                           

lemma ASN13_SE7[symbolic_exec_subst]:
  assumes 1: "mwb_lens var"
  shows "((var:== E); 
          IF trop F \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> (VAR var)  THEN (var:== (trop F \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> (VAR var))) ELSE (var:== (trop G \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> (VAR var)))) =
         (var:== (trop If (trop F \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> E) (trop F \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> E) (trop G \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> E)))" 
  using 1 unrest_const[of var exp1] unrest_const[of var exp2] ASN13_trop[of var] 
  by auto                                                           

lemma ASN13_SE8[symbolic_exec_subst]:
  assumes 1: "mwb_lens var"
  shows "((var:== E); 
          IF trop F \<guillemotleft>exp1\<guillemotright> (VAR var) \<guillemotleft>exp2\<guillemotright> THEN (var:== (trop F \<guillemotleft>exp1\<guillemotright> (VAR var) \<guillemotleft>exp2\<guillemotright>)) ELSE (var:== (trop G \<guillemotleft>exp1\<guillemotright> (VAR var) \<guillemotleft>exp2\<guillemotright>))) =
         (var:== (trop If (trop F \<guillemotleft>exp1\<guillemotright> E \<guillemotleft>exp2\<guillemotright>) (trop F \<guillemotleft>exp1\<guillemotright> E \<guillemotleft>exp2\<guillemotright>) (trop G \<guillemotleft>exp1\<guillemotright> E \<guillemotleft>exp2\<guillemotright>)))" 
  using 1 unrest_const[of var exp1] unrest_const[of var exp2] ASN13_trop1[of var] 
  by auto

lemma ASN13_SE9[symbolic_exec_subst]:
  assumes 1: "mwb_lens var"
  shows "((var:== E); 
          IF trop F (VAR var) \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> THEN (var:== (trop F (VAR var) \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright>)) ELSE (var:== (trop G (VAR var) \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright>))) =
         (var:== (trop If (trop F E \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright>) (trop F E \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright>) (trop G E \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright>)))" 
  using 1 unrest_const[of var exp1] unrest_const[of var exp2] ASN13_trop2[of var] 
  by auto 

lemma ASN13_SE10[symbolic_exec_subst]:
  assumes 1: "mwb_lens var" 
  shows "((var:== E); 
          IF trop F \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> (VAR var) THEN (var:== (trop F \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> (VAR var))) ELSE (var:== (trop G \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright> (VAR var)))) =
         (var:== (trop If (trop F \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> E) (trop F \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> E) (trop G \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright> E)))" 
  using 1 unrest_const[of var exp1] unrest_const[of var exp2] ASN13_trop3[of var]
          unrest_const[of var exp3] unrest_const[of var exp4] 
  by auto

lemma ASN13_SE11[symbolic_exec_subst]:
  assumes 1: "mwb_lens var" 
  shows "((var:== E); 
          IF trop F \<guillemotleft>exp1\<guillemotright> (VAR var) \<guillemotleft>exp2\<guillemotright> THEN (var:== (trop F \<guillemotleft>exp1\<guillemotright> (VAR var) \<guillemotleft>exp2\<guillemotright>)) ELSE (var:== (trop G \<guillemotleft>exp3\<guillemotright> (VAR var) \<guillemotleft>exp4\<guillemotright>))) =
         (var:== (trop If (trop F \<guillemotleft>exp1\<guillemotright> E \<guillemotleft>exp2\<guillemotright>) (trop F \<guillemotleft>exp1\<guillemotright> E \<guillemotleft>exp2\<guillemotright>) (trop G \<guillemotleft>exp3\<guillemotright> E \<guillemotleft>exp4\<guillemotright>)))" 
  using 1 unrest_const[of var exp1] unrest_const[of var exp2] ASN13_trop4[of var]
          unrest_const[of var exp3] unrest_const[of var exp4] 
  by auto

lemma ASN13_SE12[symbolic_exec_subst]:
  assumes 1: "mwb_lens var"
  shows "((var:== E); 
          IF trop F (VAR var) \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> THEN (var:== (trop F (VAR var) \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright>)) ELSE (var:== (trop G (VAR var) \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>))) =
         (var:== (trop If (trop F E \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright>) (trop F E \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright>) (trop G E \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>)))" 
  using 1 unrest_const[of var exp1] unrest_const[of var exp2] ASN13_trop5[of var]
          unrest_const[of var exp3] unrest_const[of var exp4] 
  by auto

end