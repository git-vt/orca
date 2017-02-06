theory Algebraic_Laws
imports Commands

begin

section {*Algebraic laws of programming*}
text{*In this section we introduce the semantic rules related to the different
      statements of IMP. In the literature this also known as the algebraic laws of programming.*}

named_theorems small_step

subsection {*SKIP Laws*}
text{*In this section we introduce the algebraic laws of programming related to the SKIP
      statement.*}

lemma SKI0 [small_step]:
  "SKIP ; C = C"
  by auto

lemma SKI1[small_step]:
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

lemma ASN4[small_step]:
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

lemma ASN5[small_step]:
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

lemma ASN6[small_step]:
  "(var:== exp ; IF bexp THEN C1 ELSE C2) = 
   (IF ([var \<mapsto>\<^sub>s exp] \<dagger> bexp) THEN (var:== exp ; C1) ELSE (var:== exp ; C2))" 
  by transfer auto

text {*In the sequel we find assignment laws proposed by Hoare*}

lemma ASN7 [small_step]:
  assumes 1: "mwb_lens var"
  shows"(var:== exp ; var:== (uop F (VAR var))) = (var:== (uop F exp))"
  using 1 unfolding subst_upd_var_def 
  by transfer auto

lemma ASN8 [small_step]:
  assumes 1: "vwb_lens var"
  shows "(var:== VAR var) = SKIP"
  using 1 unfolding subst_upd_var_def
  by transfer auto

lemma ASN9[small_step]:
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

lemma ASN11[small_step]:
  assumes 1: "weak_lens var"
  shows "(var:== exp ; IF (uop F (VAR var)) THEN C1 ELSE C2) = 
         (IF (uop F exp) THEN (var:== exp ; C1) ELSE (var:== exp ; C2))"
  using 1 unfolding subst_upd_var_def 
  by transfer auto 

lemma ASN12[small_step]:
  "(IF bexp THEN (var:== exp1) ELSE (var:== exp2)) = 
   (var :== (trop If bexp exp1 exp2))" 
   unfolding subst_upd_var_def 
   by transfer auto 

lemma ASN13[small_step]:
  assumes 1: "mwb_lens var"
  shows "((var:== E); 
          IF uop F (VAR var) THEN (var:== (uop F (VAR var))) ELSE (var:== (uop G (VAR var)))) =
         (var:== (trop If (uop F E) (uop F E) (uop G E)))" 
  using 1 unfolding subst_upd_var_def 
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
lemma COND1[small_step]:
  "(IF \<guillemotleft>True\<guillemotright> THEN C1 ELSE C2) = C1" 
  by transfer simp

(*IF False*)
lemma COND2[small_step]:
  "(IF \<guillemotleft>False\<guillemotright> THEN C1 ELSE C2) = C2" 
  by transfer simp

(*IF Idemp*)
lemma COND3[small_step]:
  "(IF bexp THEN C1 ELSE C1) = C1" 
  by simp

(*IF assoc*)
lemma COND4[small_step]:
  "(IF bexp THEN C1 ELSE (IF bexp THEN C2 ELSE C3)) =  
   (IF bexp THEN (IF bexp THEN C1 ELSE C2) ELSE C3)" 
  by auto

(*IF inverse*)
lemma COND5[small_step]:
  "(IF P THEN C1 ELSE C2) = (IF uop Not P THEN C2 ELSE C1)" 
  by transfer auto

(*IF unfold nested cond*)
lemma COND6[small_step]:
  "(IF trop If bexp bexp1 bexp2 THEN C1 ELSE C2) = 
   (IF bexp THEN (IF bexp1 THEN C1 ELSE C2) ELSE (IF bexp2 THEN C1 ELSE C2))" 
  by transfer auto

(*IF ignore*)
lemma COND7[small_step]:
  "(IF bexp THEN C1 ELSE (IF bexp THEN C2 ELSE C3)) = 
   (IF bexp THEN C1 ELSE C3)" 
  by auto

(*the rules COND8, COND9 and COND10 are related to non-deterministic choice between C1 and C2..
  which is not yet supported by our anguage*)

(*IF distribute*)
lemma COND11[small_step]:
  "(IF bexp2 THEN (IF bexp1 THEN C1 ELSE C2) ELSE C3) =  
   (IF bexp1 THEN (IF bexp2 THEN C1 ELSE C3) ELSE (IF bexp2 THEN C2 ELSE C3))" 
  by auto

(*IF Theorem by Hoare: It optimize nested IF*)
theorem COND12[small_step]: 
  "(IF bexp1 THEN (IF bexp2 THEN C1 ELSE C3) ELSE (IF bexp3 THEN C2 ELSE C3)) =
   (IF (IF bexp1 THEN bexp2 ELSE bexp3) THEN (IF bexp1 THEN C1 ELSE C2) ELSE C3)"
  by auto

subsection {*Sequential laws Laws*}
text{*In this section we introduce the algebraic laws of programming related to the sequential
      composition of statements.*}

(*Seq assoc*)
lemma SEQ1[small_step]: 
  "(C1 ; C2) ; C3 = C1 ; (C2 ; C3)"
  by auto

(*Seq SKIP*)
lemma SEQ2[small_step]: 
  "(SKIP ; C) = (C ; SKIP)"
  by transfer simp

(*Seq unit 1*)
lemma SEQ3[small_step]: 
  "((0\<^sub>L :== VAR 0\<^sub>L) ; C) = (C ; (0\<^sub>L :== VAR 0\<^sub>L))"
  unfolding subst_upd_var_def unit_lens_def
  by transfer auto

lemma SEQ4[small_step]: 
  "(bot ; C) = (C ; bot)"
  unfolding subst_upd_var_def unit_lens_def
 oops

(*Seq unit 2*)

lemma SEQ5[small_step]: 
  "(bot ; C) = bot" 
oops

(*Seq unit 3*)
lemma SEQ6[small_step]: 
  "(C ; bot) = bot"
  by auto

(*The rules SEQ6 SEQ7 related to SEQ and non-deterministic choice are missing for now*)
  
(*Seq distribution*)
lemma SEQ7[small_step]: 
  "((IF bexp THEN C1 ELSE C2); C3) = 
   (IF bexp THEN (C1 ; C3) ELSE (C2 ; C3))"
   by transfer auto 

subsection {*While laws*}
text{*In this section we introduce the algebraic laws of programming related to the while
      statement.*}

lemma W_mono: "mono (W b r)"
  unfolding W_def mono_def
  by auto

lemma WHILE3:
  assumes 1:" \<not> b s"
  shows "(WHILE b DO C OD) s = SKIP s"
  using 1  apply transfer apply auto
  oops

lemma D_While_If:
  "D(WHILE b DO c) = D(IF b THEN c;;WHILE b DO c ELSE SKIP)"
proof-
  let ?w = "WHILE b DO c" let ?f = "W (bval b) (D c)"
  have "D ?w = lfp ?f" by simp
  also have "\<dots> = ?f (lfp ?f)" by(rule lfp_unfold [OF W_mono])
  also have "\<dots> = D(IF b THEN c;;?w ELSE SKIP)" by (simp add: W_def)
  finally show ?thesis .
qed

lemma IF_D1:
  "(Rel (IF b THEN c1 ELSE c2)) = 
   {(s,t). if b s then (s,t) \<in> (Rel c1) else (s,t) \<in> (Rel c2)}"
  by (auto simp add: Rel_def)

lemma WHILE_D1:
    "RelInv(Rel (WHILE b DO C OD)) = RelInv (lfp (W b (Rel C)))"
  by (simp add: Rel_def RelInv_def)

lemma WHILE1:
  "(WHILE b DO C OD) = (IF b THEN C; WHILE b DO C OD ELSE SKIP)"
proof-
  let ?w = "WHILE b DO C OD" let ?f = "RelInv(Rel(W  b (Rel C)))"
  have "?w = RelInv (lfp ?f)" .. 
  also have "\<dots> = RelInv (?f  (lfp ?f))" by (metis W_mono def_lfp_unfold) 
  also have "\<dots> = (IF b THEN C; ?w ELSE SKIP)" apply (simp add:  W_def )
      
(*proof -
           { fix aa :: 'a
             { assume "\<not> b aa"
               then have "(WHILE b DO C OD) aa = aa \<and> \<not> b aa"
                 using ff1 by metis (* failed *)
               then have "(\<not> b aa \<or> (C; WHILE b DO C OD) aa = RelInv (W b (Rel C) (lfp (W b (Rel C)))) aa) \<and> (b aa \<or> SKIP aa = RelInv (W b (Rel C) (lfp (W b (Rel C)))) aa)"
                 using \<open>WHILE b DO C OD = RelInv (W b (Rel C) (lfp (W b (Rel C))))\<close> by force }
             moreover
             { assume "b aa"
               then have "(WHILE b DO C OD) aa = (WHILE b DO C OD) (C aa) \<and> b aa"
                 using ff1 sorry (* > 1.0 s, timed out *)
               then have "(\<not> b aa \<or> (C; WHILE b DO C OD) aa = RelInv (W b (Rel C) (lfp (W b (Rel C)))) aa) \<and> (b aa \<or> SKIP aa = RelInv (W b (Rel C) (lfp (W b (Rel C)))) aa)"
                 using \<open>WHILE b DO C OD = RelInv (W b (Rel C) (lfp (W b (Rel C))))\<close> by fastforce }
             ultimately have "(\<not> b aa \<or> (C; WHILE b DO C OD) aa = RelInv (W b (Rel C) (lfp (W b (Rel C)))) aa) \<and> (b aa \<or> SKIP aa = RelInv (W b (Rel C) (lfp (W b (Rel C)))) aa)"
               by blast }
           then show ?thesis
             by (metis (no_types))
         qed*)
       
  finally show ?thesis
  by (simp add: \<open>RelInv (W b (Rel C) (lfp (W b (Rel C)))) = IF b THEN C; WHILE b DO C OD ELSE SKIP\<close> \<open>WHILE b DO C OD = RelInv (W b (Rel C) (lfp (W b (Rel C))))\<close>) 
qed

lemma WHILE1:
 "(WHILE b DO C OD) = (IF b THEN C; WHILE b DO C OD ELSE SKIP)"
 proof-
  let ?w = "WHILE b DO C OD" let ?f = "W  b (Rel C)"
  have "?w = RelInv (lfp ?f)" .. 
  also have "\<dots> = RelInv (?f  (lfp ?f))" by (metis W_mono def_lfp_unfold) 
  also have "\<dots> = (IF b THEN C; ?w ELSE SKIP)" apply (simp add:  W_def )
         (*proof -
           { fix aa :: 'a
             { assume "\<not> b aa"
               then have "(WHILE b DO C OD) aa = aa \<and> \<not> b aa"
                 using ff1 by metis (* failed *)
               then have "(\<not> b aa \<or> (C; WHILE b DO C OD) aa = RelInv (W b (Rel C) (lfp (W b (Rel C)))) aa) \<and> (b aa \<or> SKIP aa = RelInv (W b (Rel C) (lfp (W b (Rel C)))) aa)"
                 using \<open>WHILE b DO C OD = RelInv (W b (Rel C) (lfp (W b (Rel C))))\<close> by force }
             moreover
             { assume "b aa"
               then have "(WHILE b DO C OD) aa = (WHILE b DO C OD) (C aa) \<and> b aa"
                 using ff1 sorry (* > 1.0 s, timed out *)
               then have "(\<not> b aa \<or> (C; WHILE b DO C OD) aa = RelInv (W b (Rel C) (lfp (W b (Rel C)))) aa) \<and> (b aa \<or> SKIP aa = RelInv (W b (Rel C) (lfp (W b (Rel C)))) aa)"
                 using \<open>WHILE b DO C OD = RelInv (W b (Rel C) (lfp (W b (Rel C))))\<close> by fastforce }
             ultimately have "(\<not> b aa \<or> (C; WHILE b DO C OD) aa = RelInv (W b (Rel C) (lfp (W b (Rel C)))) aa) \<and> (b aa \<or> SKIP aa = RelInv (W b (Rel C) (lfp (W b (Rel C)))) aa)"
               by blast }
           then show ?thesis
             by (metis (no_types))
         qed*)
       
  finally show ?thesis
  by (simp add: \<open>RelInv (W b (Rel C) (lfp (W b (Rel C)))) = IF b THEN C; WHILE b DO C OD ELSE SKIP\<close> \<open>WHILE b DO C OD = RelInv (W b (Rel C) (lfp (W b (Rel C))))\<close>) 
qed
  

lemma WHILE2:
  assumes 1:"b = \<guillemotleft>True\<guillemotright>"
  shows "(WHILE b DO C OD) = (C; WHILE  b DO C OD)"
proof -
  have f1: "\<forall>A f. (bot (A::'a set)::'a set) = f (bot A::'a set)"
    by (metis (no_types) SEQ4 SEQ6 comp_apply)
  then have f2: "\<forall>f. _type_constraint_ = inv f; f"
    by auto
  obtain aa :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
    f3: "\<forall>f fa fb A. f = fb \<or> (fa; f) (aa fa A f fb) \<noteq> (fa; fb) (aa fa A f fb)"
    using f1 by blast
  have "\<forall>c ca. c = ca"
    using f2 by (metis K_record_comp) (* > 1.0 s, timed out *)
  then show ?thesis
    using f3 sorry (* > 1.0 s, timed out *)
qed
  



end