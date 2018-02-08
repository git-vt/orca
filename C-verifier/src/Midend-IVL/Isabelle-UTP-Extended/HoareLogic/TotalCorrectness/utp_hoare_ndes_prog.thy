(*****************************************************************************************)
(* Orca: A Functional Correctness Verifier for Imperative Programs Based on Isabelle/UTP *)
(*                                                                                       *)
(* Copyright (c) 2016-2018 Virginia Tech, USA                                            *)
(* This software may be distributed and modified according to the terms of               *)
(* the GNU Lesser General Public License version 3.0 or any later version.               *)
(* Note that NO WARRANTY is provided.                                                    *)
(* See CONTRIBUTORS, LICENSE and CITATION files for details.                             *)
(*****************************************************************************************)

theory utp_hoare_ndes_prog

imports "../../AlgebraicLaws/algebraic_laws_prog"

begin

section {*Helper*}    

text \<open>The below definition helps in asserting independence for a group of lenses, as otherwise the
number of assumptions required increases greatly. Unfortunately, it is not usable with lenses of
different types as Isabelle does not allow heterogenous lists; element types must be unifiable.\<close>

definition \<open>lens_indep_all lenses \<longleftrightarrow> (\<forall>l \<in> set lenses. vwb_lens l \<and> eff_lens l) \<and>
                                      (\<forall>i j. i < length lenses \<and> j < length lenses \<and>
                                             i \<noteq> j \<longrightarrow> lenses!i \<bowtie> lenses!j)\<close>

lemma lens_indep_all_alt:
  \<open>lens_indep_all lenses \<longleftrightarrow> (\<forall>l \<in> set lenses. vwb_lens l \<and> eff_lens l) \<and>
                              distinct lenses \<and>
                             (\<forall>a \<in> set lenses. \<forall>b \<in> set lenses. a \<noteq> b \<longrightarrow> a \<bowtie> b)\<close>
  unfolding lens_indep_all_def distinct_conv_nth
  apply (safe; simp?)
   apply (metis lens_indep_quasi_irrefl nth_mem vwb_lens_wb)
  apply (metis in_set_conv_nth)
  done

section {*Hoare logic for programs*}  

named_theorems hoare_sp_rules and hoare_wp_rules and hoare_wp_proof_annotation_rules

subsection {*Hoare triple definition*}

lift_definition hoare_prog_t :: "'\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>P") 
 is  hoare_d .

declare hoare_prog_t.rep_eq [prog_rep_eq]

lemma hoare_true_assisgns_prog_t[hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  "\<lbrace>p\<rbrace> \<langle>\<sigma>\<rangle>\<^sub>p \<lbrace>true\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma hoare_true_skip_prog_t[hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  "\<lbrace>p\<rbrace>SKIP\<lbrace>true\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma hoare_false_prog_t[hoare_sp_rules]: 
  "\<lbrace>false\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

subsection {*Precondition weakening*}

lemma pre_str_prog_hoare:
  assumes "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" and "\<lbrace>p\<^sub>2\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<^sub>1\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P" 
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Post-condition strengthening*}
  
lemma post_weak_prog_hoare:
  assumes "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>2\<rbrace>\<^sub>P" and "`q\<^sub>2 \<Rightarrow> q\<^sub>1`"
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>1\<rbrace>\<^sub>P" 
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Consequence rule*}  
  
lemma consequence_hoare_prog:
  assumes I0': "`p \<Rightarrow> p'`" 
  assumes induct_step:"\<lbrace>p'\<rbrace> C \<lbrace>q'\<rbrace>\<^sub>P" 
  assumes I0 :"`q' \<Rightarrow> q`"  
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P"
proof(rule post_weak_prog_hoare[OF _ I0], goal_cases)
  case 1
  then show ?case by (rule pre_str_prog_hoare[OF I0' induct_step ]) 
qed   
  
subsection {*Hoare and assertion logic*}

lemma hoare_prog_conj_prog_t: 
  assumes"\<lbrace>p\<rbrace>C\<lbrace>r\<rbrace>\<^sub>P" and "\<lbrace>p\<rbrace>C\<lbrace>s\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>C\<lbrace>r \<and> s\<rbrace>\<^sub>P"
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Hoare SKIP*}

lemma skip_prog_hoare_prog_t[hoare_sp_rules, hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  "\<lbrace>p\<rbrace>SKIP\<lbrace>p\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)
    
lemma skip_prog_hoare_prog_intro: 
  "`p \<Rightarrow> q`\<Longrightarrow>\<lbrace>p\<rbrace>SKIP\<lbrace>q\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)
    
subsection {*Hoare for assignment*}

lemma assigns_prog_hoare_prog_backward_t[hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  assumes"`p \<Rightarrow> \<sigma> \<dagger> q`" 
  shows  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>p\<lbrace>q\<rbrace>\<^sub>P"
  using assms  
  by (simp add: prog_rep_eq hoare_des)

lemma assigns_prog_hoare_prog_backward_t': 
  "\<lbrace>\<sigma> \<dagger> p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>p\<lbrace>p\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma assigns_prog_floyd_t[hoare_sp_rules]:
  assumes "vwb_lens x"
  shows \<open>\<lbrace>p\<rbrace>x :== e\<lbrace>\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrace>\<^sub>P\<close>
  using assms  
  by (simp add: assms prog_rep_eq hoare_des)

subsection {*Hoare for Sequential Composition*}

lemma seq_hoare_prog[hoare_sp_rules, hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  assumes"\<lbrace>p\<rbrace>C\<^sub>1\<lbrace>s\<rbrace>\<^sub>P" and "\<lbrace>s\<rbrace>C\<^sub>2\<lbrace>r\<rbrace>\<^sub>P" 
  shows"\<lbrace>p\<rbrace>C\<^sub>1 ; C\<^sub>2\<lbrace>r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)  

subsection {*Hoare for Conditional*}

lemma cond_prog_hoare_prog_t[hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  assumes "\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>P" and "\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>IF b THEN C\<^sub>1 ELSE C\<^sub>2 FI\<lbrace>q\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des) 

    
lemma cond_prog_hoare_prog_t'[hoare_sp_rules]:
  assumes \<open>\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>P\<close> and \<open>\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>s\<rbrace>\<^sub>P\<close>
  shows \<open>\<lbrace>p\<rbrace>IF b THEN C\<^sub>1 ELSE C\<^sub>2 FI\<lbrace>q \<or> s\<rbrace>\<^sub>P\<close>
  using assms
  by (simp add: prog_rep_eq hoare_des) 
    
subsection {*Hoare for recursion*}

lemma mono_Monotone_prog: (*This can be used to generate lemmas automatically*)
  assumes M:"mono F" 
  shows "Mono\<^bsub>uthy_order NDES\<^esub> (Rep_prog \<circ> F \<circ> Abs_prog \<circ> \<H>\<^bsub>NDES\<^esub>)"
  by (metis (no_types, lifting) Abs_prog_Rep_prog_Ncarrier Healthy_def M Mono_utp_orderI comp_apply less_eq_prog.rep_eq monoD)

lemma N_prog_funcset: (*This can be used to generate lemmas automatically*)
  "Rep_prog \<circ> F \<circ> Abs_prog \<circ> \<H>\<^bsub>NDES\<^esub> \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"  
  using Rep_prog by auto
   
lemma mu_prog_hoare_prog:
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<And> st P. \<lbrace>p \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace> P \<lbrace>q\<rbrace>\<^sub>P \<Longrightarrow> \<lbrace>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> F P \<lbrace>q\<rbrace>\<^sub>P"   
  shows "\<lbrace>p\<rbrace>\<mu>\<^sub>p F \<lbrace>q\<rbrace>\<^sub>P"
  apply (simp add: prog_rep_eq)
  apply (subst normal_design_theory_continuous.LFP_healthy_comp)  
  apply (rule mu_ndes_hoare_ndes[OF N_prog_funcset WF  mono_Monotone_prog[OF M] , 
                                    simplified, OF induct_step[unfolded prog_rep_eq]])
  apply (simp add: Abs_prog_Rep_prog_Ncarrier)   
  apply (simp add: Healthy_if is_Ncarrier_is_ndesigns)
  done
    
lemma mu_prog_hoare_prog':
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<And> st P. \<lbrace>p \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace> P \<lbrace>q\<rbrace>\<^sub>P \<Longrightarrow> \<lbrace>p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> F P \<lbrace>q\<rbrace>\<^sub>P" 
  assumes I0: "`p' \<Rightarrow> p`"  
  shows "\<lbrace>p'\<rbrace>\<mu>\<^sub>p F \<lbrace>q\<rbrace>\<^sub>P"
  by (simp add: pre_str_prog_hoare[OF I0 mu_prog_hoare_prog[OF WF M induct_step]])

subsection {*Hoare for frames*}
  
lemma antiframe_hoare_p_t:
  assumes "vwb_lens a"
  assumes "a \<sharp> r" 
  assumes "a \<natural> q"    
  assumes "\<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>P"  
  shows "\<lbrace>p \<and> r\<rbrace>a:[P]\<lbrace>q \<and> r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)

lemma antiframe_goare_p_t_stronger:
  assumes "vwb_lens a"
  assumes "a \<sharp> r" 
  assumes "a \<natural> q"    
  assumes "\<lbrace>p \<and> r\<rbrace>P\<lbrace>q\<rbrace>\<^sub>P"  
  shows "\<lbrace>p \<and> r\<rbrace>a:[P]\<lbrace>q \<and> r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)    
    
lemma frame_hoare_p_t:
  assumes "vwb_lens a"
  assumes "a \<natural> r" 
  assumes "a \<sharp> q"    
  assumes "\<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>P"  
  shows "\<lbrace>p \<and> r\<rbrace> a:\<lbrakk>P\<rbrakk> \<lbrace>q \<and> r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)

lemma frame_hoare_p_t_stronger:
  assumes "vwb_lens a"
  assumes "a \<natural> r" 
  assumes "a \<sharp> q"    
  assumes "\<lbrace>p \<and> r\<rbrace>P\<lbrace>q\<rbrace>\<^sub>P"  
  shows "\<lbrace>p \<and> r\<rbrace> a:\<lbrakk>P\<rbrakk> \<lbrace>q \<and> r\<rbrace>\<^sub>P"
  using assms 
  by (simp add: prog_rep_eq hoare_des)
    
lemma blah1: 
  assumes "vwb_lens g'" "vwb_lens l"
  assumes  "l \<bowtie> g'" 
  shows "vwb_lens  (g' +\<^sub>L l)" 
  using assms 
  by (simp add: lens_indep_sym plus_vwb_lens) 
   
lemma
  assumes 1:"vwb_lens g" 
  assumes 2:"vwb_lens g'" 
  assumes 3:"vwb_lens l"
  assumes 4:"l \<bowtie> g" 
  assumes 8:"g' \<subseteq>\<^sub>L g"
  assumes 5:"{&g', &l}:[C] = C" 
  assumes 6:"\<lbrace>p\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P"
  assumes 7:"`r \<Rightarrow> p`"     
  shows "\<lbrace>r\<rbrace> l:\<lbrakk>C\<rbrakk> \<lbrace>(\<exists> l \<bullet> q) \<and> (\<exists>g' \<bullet> r)\<rbrace>\<^sub>P"
  using 1 2 3 4 5 6 7 unfolding lens_indep_def
  apply (simp add: prog_rep_eq )
   apply rel_auto 
  apply (metis (no_types, lifting) vwb_lens_wb wb_lens.get_put)
  apply (rule_tac x="get\<^bsub> g'\<^esub> more" in exI) using 8 4 
proof -
  fix ok\<^sub>v :: bool and more :: 'b and ok\<^sub>v' :: bool and x :: 'b
  assume a1: "\<lbrakk>r\<rbrakk>\<^sub>e more"
  assume a2: "vwb_lens g"
  assume "\<forall>\<sigma> u. get\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> \<sigma> u) = get\<^bsub>g\<^esub> \<sigma>"
  assume a3: "\<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = more\<rparr>, \<lparr>ok\<^sub>v = True, \<dots> = x\<rparr>)"
  assume a4: "\<forall>ok\<^sub>v more ok\<^sub>v' morea. (ok\<^sub>v \<longrightarrow> ok\<^sub>v' \<and> (\<exists>x. \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = more\<rparr>, \<lparr>ok\<^sub>v = ok\<^sub>v', \<dots> = x\<rparr>) \<and> morea = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> more (get\<^bsub>l\<^esub> x)) (get\<^bsub>g'\<^esub> x))) = \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = ok\<^sub>v, \<dots> = more\<rparr>, \<lparr>ok\<^sub>v = ok\<^sub>v', \<dots> = morea\<rparr>)"
  assume a5: "\<forall>\<sigma> v u. put\<^bsub>l\<^esub> (put\<^bsub>g\<^esub> \<sigma> v) u = put\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> \<sigma> u) v"
  assume a6: "vwb_lens g'"
  assume a7: "vwb_lens l"
  have f8: "wb_lens g"
    using a2 vwb_lens_wb by blast
  have f9: "\<forall>l la b a c. \<not> vwb_lens l \<or> \<not> la \<subseteq>\<^sub>L l \<or> put\<^bsub>l\<^esub> (b::'b) (put\<^bsub>la /\<^sub>L l\<^esub> (a::'a) (c::'c)) = put\<^bsub>la\<^esub> (put\<^bsub>l\<^esub> b a) c"
    by (meson lens_put_of_quotient)
  then have f10: "put\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> x (get\<^bsub>l\<^esub> more)) (put\<^bsub>g' /\<^sub>L g\<^esub> (get\<^bsub>g\<^esub> x) (get\<^bsub>g'\<^esub> more)) = put\<^bsub>g'\<^esub> (put\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> x (get\<^bsub>l\<^esub> more)) (get\<^bsub>g\<^esub> x)) (get\<^bsub>g'\<^esub> more)"
    using a2 by (metis "8") (* > 1.0 s, timed out *)
  have f11: "\<forall>b ba bb bc. (\<not> b \<or> bb \<and> (\<exists>b. \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = ba\<rparr>, \<lparr>ok\<^sub>v = bb, \<dots> = b\<rparr>) \<and> bc = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> ba (get\<^bsub>l\<^esub> b)) (get\<^bsub>g'\<^esub> b))) = \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = b, \<dots> = ba\<rparr>, \<lparr>ok\<^sub>v = bb, \<dots> = bc\<rparr>)"
    using a4 by auto
  obtain bb :: "'b \<Rightarrow> bool \<Rightarrow> 'b \<Rightarrow> 'b" where
    "\<forall>x0 x1 x2. (\<exists>v4. \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = x2\<rparr>, \<lparr>ok\<^sub>v = x1, \<dots> = v4\<rparr>) \<and> x0 = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x2 (get\<^bsub>l\<^esub> v4)) (get\<^bsub>g'\<^esub> v4)) = (\<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = x2\<rparr>, \<lparr>ok\<^sub>v = x1, \<dots> = bb x0 x1 x2\<rparr>) \<and> x0 = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x2 (get\<^bsub>l\<^esub> (bb x0 x1 x2))) (get\<^bsub>g'\<^esub> (bb x0 x1 x2)))"
    by moura
  then have "\<forall>b ba bc bd. (b \<and> (\<not> bc \<or> (\<forall>b. \<not> \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = ba\<rparr>, \<lparr>ok\<^sub>v = bc, \<dots> = b\<rparr>) \<or> \<not> bd = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> ba (get\<^bsub>l\<^esub> b)) (get\<^bsub>g'\<^esub> b))) \<or> \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = b, \<dots> = ba\<rparr>, \<lparr>ok\<^sub>v = bc, \<dots> = bd\<rparr>)) \<and> ((\<not> b \<or> bc \<and> \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = ba\<rparr>, \<lparr>ok\<^sub>v = bc, \<dots> = bb bd bc ba\<rparr>) \<and> bd = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> ba (get\<^bsub>l\<^esub> (bb bd bc ba))) (get\<^bsub>g'\<^esub> (bb bd bc ba))) \<or> \<not> \<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = b, \<dots> = ba\<rparr>, \<lparr>ok\<^sub>v = bc, \<dots> = bd\<rparr>))"
    using f11 by metis (* > 1.0 s, timed out *)
  then have f12: "\<lbrakk>\<lbrakk>C\<rbrakk>\<^sub>p\<rbrakk>\<^sub>e (\<lparr>ok\<^sub>v = True, \<dots> = more\<rparr>, \<lparr>ok\<^sub>v = True, \<dots> = bb x True more\<rparr>) \<and> x = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> more (get\<^bsub>l\<^esub> (bb x True more))) (get\<^bsub>g'\<^esub> (bb x True more))"
    using a3 by (metis (no_types))
  have f13: "put\<^bsub>g\<^esub> (put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> more (get\<^bsub>l\<^esub> (bb x True more))) (get\<^bsub>g'\<^esub> (bb x True more))) (put\<^bsub>g' /\<^sub>L g\<^esub> (get\<^bsub>g\<^esub> x) (get\<^bsub>g'\<^esub> more)) = put\<^bsub>g'\<^esub> (put\<^bsub>g\<^esub> (put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> more (get\<^bsub>l\<^esub> (bb x True more))) (get\<^bsub>g'\<^esub> (bb x True more))) (get\<^bsub>g\<^esub> x)) (get\<^bsub>g'\<^esub> more)"
    using a2 f9 by (metis "8") (* > 1.0 s, timed out *)
  have f14: "put\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> more (get\<^bsub>l\<^esub> (bb x True more))) (put\<^bsub>g' /\<^sub>L g\<^esub> (get\<^bsub>g\<^esub> more) (get\<^bsub>g'\<^esub> more)) = put\<^bsub>g'\<^esub> (put\<^bsub>g\<^esub> (put\<^bsub>l\<^esub> more (get\<^bsub>l\<^esub> (bb x True more))) (get\<^bsub>g\<^esub> more)) (get\<^bsub>g'\<^esub> more)"
    using a2 f9 by (metis "8") (* > 1.0 s, timed out *)
  have "put\<^bsub>g\<^esub> more (put\<^bsub>g' /\<^sub>L g\<^esub> (get\<^bsub>g\<^esub> more) (get\<^bsub>g'\<^esub> more)) = put\<^bsub>g'\<^esub> (put\<^bsub>g\<^esub> more (get\<^bsub>g\<^esub> more)) (get\<^bsub>g'\<^esub> more)"
    using a2 f9 by (metis "8") (* > 1.0 s, timed out *)
  then show "\<lbrakk>r\<rbrakk>\<^sub>e (put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x (get\<^bsub>l\<^esub> more)) (get\<^bsub>g'\<^esub> more))"
    using f14 f13 f12 f10 f8 a7 a6 a5 a1 by (metis mwb_lens.put_put vwb_lens_mwb vwb_lens_wb wb_lens.get_put)
qed 
  

subsection {*Hoare for while loop*}   

lemma while_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`" 
  assumes induct_step:"\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"    
  shows "\<lbrace>p\<rbrace>WHILE b DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding while_lfp_prog_mu_prog
proof (rule pre_str_prog_hoare[OF seq_step mu_prog_hoare_prog[OF WF if_prog_mono cond_prog_hoare_prog_t, of _ e] ], goal_cases)
  case (1 st X)
  assume *:"\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>X\<lbrace>\<not> b \<and> invar\<rbrace>\<^sub>P"  
  show ?case
  proof (rule seq_hoare_prog[of _ _ "invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>"], goal_cases)
    case 1
    then show ?case using induct_step[of st] by assumption 
  next
    case 2
    then show ?case using * by assumption
  qed
next
  case (2 st X)
  assume "\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>X\<lbrace>\<not> b \<and> invar\<rbrace>\<^sub>P"  
  show ?case by (rule skip_prog_hoare_prog_intro, pred_blast) 
qed 
    
lemma while_invr_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`" 
  assumes induct_step:"\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"    
  shows "\<lbrace>p\<rbrace>INVAR invar WHILE b DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding while_lfp_invr_prog_def
  using assms while_hoare_prog_minimal
  by blast  

lemma while_invr_vrt_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`" 
  assumes induct_step:"\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"    
  shows "\<lbrace>p\<rbrace>INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding while_lfp_invr_vrt_prog_def
  using assms while_hoare_prog_minimal
  by blast  
    
lemma while_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P" 
  by (rule consequence_hoare_prog[OF seq_step _ PHI, 
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF I0' induct_step I0]])

lemma while_invr_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>INVAR invar WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P" 
  unfolding while_lfp_invr_prog_def
  by (rule consequence_hoare_prog[OF seq_step _ PHI, 
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF I0' induct_step I0]])

lemma while_invr_vrt_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P" 
  unfolding while_lfp_invr_vrt_prog_def  
  by (rule consequence_hoare_prog[OF seq_step _ PHI, 
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF I0' induct_step I0]])
                              
lemma while_hoare_prog_wp:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P" 
  by (rule consequence_hoare_prog[OF seq_step _ PHI,
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF I0' induct_step uimp_refl]])

lemma while_invr_hoare_prog_wp:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>INVAR invar WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P"                              
  unfolding while_lfp_invr_prog_def
  by (rule consequence_hoare_prog[OF seq_step _ PHI,
                                 OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                 OF consequence_hoare_prog[OF I0' induct_step uimp_refl]])

lemma while_invr_vrt_hoare_prog_wp[hoare_wp_rules]:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P"                              
  unfolding while_lfp_invr_vrt_prog_def
  by (rule consequence_hoare_prog[OF seq_step _ PHI,
                                 OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                 OF consequence_hoare_prog[OF I0' induct_step uimp_refl]])
                                
lemma while_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>WHILE b DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P" 
  by (rule consequence_hoare_prog[OF seq_step _ uimp_refl, 
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF uimp_refl induct_step I0]])                              
                              
lemma while_invr_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>INVAR invar WHILE b DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P" 
  unfolding while_lfp_invr_prog_def  
  by (rule consequence_hoare_prog[OF seq_step _ uimp_refl, 
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF uimp_refl induct_step I0]])

lemma while_invr_vrt_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "`p \<Rightarrow> invar`"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes  I0: "\<And> st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> `"
  shows "\<lbrace>p\<rbrace>INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P" 
  unfolding while_lfp_invr_vrt_prog_def  
  by (rule consequence_hoare_prog[OF seq_step _ uimp_refl, 
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF uimp_refl induct_step I0]])
  
subsection {*Hoare for from_until_loop*}     

lemma from_until_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>FROM init UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P"
  unfolding from_until_lfp_prog_def_alt while_lfp_prog_mu_prog
  by (rule seq_hoare_prog[OF seq_step, 
                          OF mu_prog_hoare_prog[OF WF if_prog_mono cond_prog_hoare_prog_t, of _ e],
                          OF seq_hoare_prog[OF induct_step], OF _ skip_prog_hoare_prog_intro],                             
      pauto)

lemma from_until_invr_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P"
  unfolding from_until_lfp_invr_prog_def 
  using     from_until_hoare_prog_minimal [OF WF seq_step induct_step] .
    
lemma from_until_invr_vrt_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar VRT \<guillemotleft>R\<guillemotright> UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P"
  unfolding from_until_lfp_invr_vrt_prog_def 
  using     from_until_hoare_prog_minimal [OF WF seq_step induct_step] .

lemma from_until_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init UNTIL exit DO body OD\<lbrace>q\<rbrace>\<^sub>P" 
  unfolding from_until_lfp_prog_def_alt
  by (simp add: uintro PHI seq_hoare_prog[OF seq_step] 
                       while_hoare_prog_consequence[OF WF uimp_refl _ I0' induct_step I0])

lemma from_until_invr_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar UNTIL exit DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding from_until_lfp_invr_prog_def 
  using     from_until_hoare_prog_consequence [OF WF seq_step PHI I0' induct_step I0].
    
lemma from_until_invr_vrt_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar VRT \<guillemotleft>R\<guillemotright> UNTIL exit DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding from_until_lfp_invr_vrt_prog_def
  using     from_until_hoare_prog_consequence [OF WF seq_step PHI I0' induct_step I0].
 
lemma from_until_hoare_prog_wp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>FROM init UNTIL exit DO body OD\<lbrace>q\<rbrace>\<^sub>P" 
  unfolding from_until_lfp_prog_def_alt
  by (simp add: uintro PHI seq_hoare_prog[OF seq_step] 
                       while_hoare_prog_consequence[OF WF uimp_refl _ I0' induct_step uimp_refl])

lemma from_until_invr_hoare_prog_wp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar UNTIL exit DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding from_until_lfp_invr_prog_def
  using from_until_hoare_prog_wp [OF WF seq_step PHI I0' induct_step] .
    
lemma from_until_invr_vrt_hoare_prog_wp[hoare_wp_rules]:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar VRT \<guillemotleft>R\<guillemotright> UNTIL exit DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding from_until_lfp_invr_vrt_prog_def
  using from_until_hoare_prog_wp [OF WF seq_step PHI I0' induct_step] .
    
lemma from_until_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P" 
  unfolding from_until_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] 
                       while_hoare_prog_consequence[OF WF uimp_refl _ uimp_refl induct_step I0])

lemma from_until_invr_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P" 
  unfolding from_until_lfp_invr_prog_def
  using from_until_hoare_prog_sp[OF WF seq_step induct_step I0] .  

lemma from_until_invr_vrt_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar VRT \<guillemotleft>R\<guillemotright> UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P" 
  unfolding from_until_lfp_invr_vrt_prog_def
  using from_until_hoare_prog_sp[OF WF seq_step induct_step I0] .

subsection {*Hoare for do_while_loop*}     

lemma do_while_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and>  e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows" \<lbrace>p\<rbrace>DO body WHILE b OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"  
  unfolding do_while_lfp_prog_def_alt
  by (rule seq_hoare_prog[OF seq_step while_hoare_prog_minimal[OF WF uimp_refl induct_step]])  

lemma do_while_invr_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and>  e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows" \<lbrace>p\<rbrace>DO body INVAR invar WHILE b OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"  
  unfolding do_while_lfp_invr_prog_def
  by (rule do_while_hoare_prog_minimal[OF WF seq_step induct_step])  

lemma do_while_invr_vrt_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and>  e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows" \<lbrace>p\<rbrace>DO body INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"  
  unfolding do_while_lfp_invr_vrt_prog_def
  by (rule do_while_hoare_prog_minimal[OF WF seq_step induct_step])  
    
lemma do_while_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body WHILE b OD\<lbrace>q\<rbrace>\<^sub>P" 
  unfolding do_while_lfp_prog_def_alt
  by (rule seq_hoare_prog[OF seq_step 
                             while_hoare_prog_consequence[OF WF uimp_refl PHI I0' induct_step I0]])
    
lemma do_while_invr_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body INVAR invar WHILE b OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_prog_def
  by (rule do_while_hoare_prog_consequence[OF WF seq_step PHI I0' induct_step I0])  

lemma do_while_invr_vrt_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_vrt_prog_def
  by (rule do_while_hoare_prog_consequence[OF WF seq_step PHI I0' induct_step I0])  
    
lemma do_while_hoare_prog_wp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>DO body WHILE b OD\<lbrace>q\<rbrace>\<^sub>P"
  by (rule do_while_hoare_prog_consequence[OF WF seq_step PHI I0' induct_step uimp_refl])  

lemma do_while_invr_hoare_prog_wp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>DO body INVAR invar WHILE b OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_prog_def
  by (rule do_while_hoare_prog_consequence[OF WF seq_step PHI I0' induct_step uimp_refl])  
    
lemma do_while_invr_vrt_hoare_prog_wp[hoare_wp_rules]:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>DO body INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_vrt_prog_def    
  by (rule do_while_hoare_prog_consequence[OF WF seq_step PHI I0' induct_step uimp_refl])  
    
lemma do_while_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body WHILE b OD\<lbrace>\<not>b  \<and> invar\<rbrace>\<^sub>P" 
  by (rule do_while_hoare_prog_consequence[OF WF seq_step uimp_refl uimp_refl induct_step I0])  
 
lemma do_while_invr_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body INVAR invar WHILE b OD\<lbrace>\<not>b  \<and> invar\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_prog_def  
  by (rule do_while_hoare_prog_consequence[OF WF seq_step uimp_refl uimp_refl induct_step I0])  

lemma do_while_invr_vrt_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b OD\<lbrace>\<not>b  \<and> invar\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_vrt_prog_def  
  by (rule do_while_hoare_prog_consequence[OF WF seq_step uimp_refl uimp_refl induct_step I0])  

subsection {*Hoare for for_loop*}     
    
lemma for_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body ; incr\<lbrace>invar \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>FOR (init, b, incr) DO body OD \<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding for_lfp_prog_def
  by (simp add: from_until_hoare_prog_minimal [OF WF seq_step, of _ e] induct_step)  

lemma for_invr_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body ; incr\<lbrace>invar \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>FOR (init, b, incr) INVAR invar DO body OD \<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_prog_def for_lfp_prog_def
  by (simp add: from_until_hoare_prog_minimal [OF WF seq_step, of _ e] induct_step)  

lemma for_invr_vrt_hoare_prog_minimal:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body ; incr\<lbrace>invar \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>FOR (init, b, incr) INVAR invar VRT \<guillemotleft>R\<guillemotright> DO body OD \<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_vrt_prog_def for_lfp_prog_def
  by (simp add: from_until_hoare_prog_minimal [OF WF seq_step, of _ e] induct_step)      

lemma for_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step:  "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"
  shows "\<lbrace>p\<rbrace>FOR (init, b, incr) DO body OD\<lbrace>q\<rbrace>\<^sub>P"  
  unfolding for_lfp_prog_def
  by(simp add: from_until_hoare_prog_consequence [OF WF seq_step PHI _ induct_step I0] I0')

lemma for_invr_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step:  "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"
  shows "\<lbrace>p\<rbrace>FOR (init, b, incr) INVAR invar DO body OD\<lbrace>q\<rbrace>\<^sub>P"  
  unfolding for_lfp_prog_def for_lfp_invr_prog_def
  by(simp add: from_until_hoare_prog_consequence [OF WF seq_step PHI _ induct_step I0] I0')

lemma for_invr_vrt_hoare_prog_consequence:
  assumes WF: "wf R"
  assumes seq_step:  "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"
  shows "\<lbrace>p\<rbrace>FOR (init, b, incr) INVAR invar VRT \<guillemotleft>R\<guillemotright> DO body OD\<lbrace>q\<rbrace>\<^sub>P"  
  unfolding for_lfp_prog_def for_lfp_invr_vrt_prog_def
  by(simp add: from_until_hoare_prog_consequence [OF WF seq_step PHI _ induct_step I0] I0')
    
lemma for_hoare_prog_wp:
  assumes WF : "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e=\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  by (rule for_hoare_prog_consequence[OF WF seq_step PHI I0' induct_step uimp_refl])

lemma for_invr_hoare_prog_wp:
  assumes WF : "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e=\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) INVAR invar DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_prog_def  
  by (rule for_hoare_prog_consequence[OF WF seq_step PHI I0' induct_step uimp_refl])

lemma for_invr_vrt_hoare_prog_wp[hoare_wp_rules]:
  assumes WF : "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e=\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) INVAR invar VRT \<guillemotleft>R\<guillemotright>DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_vrt_prog_def  
  by (rule for_hoare_prog_consequence[OF WF seq_step PHI I0' induct_step uimp_refl])

lemma for_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  by (rule for_hoare_prog_consequence[OF WF seq_step uimp_refl  uimp_refl induct_step I0])

lemma for_invr_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) INVAR invar DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_prog_def  
  by (rule for_hoare_prog_consequence[OF WF seq_step uimp_refl  uimp_refl induct_step I0])    
    
lemma for_invr_vrt_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) INVAR invar VRT \<guillemotleft>R\<guillemotright>DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_vrt_prog_def  
  by (rule for_hoare_prog_consequence[OF WF seq_step uimp_refl  uimp_refl induct_step I0])
    
lemmas loop_invr_vrt_hoare_prog_sp_instantiated [hoare_sp_rules] = 
       while_invr_vrt_hoare_prog_sp [where e = "&\<Sigma>"]
       for_invr_vrt_hoare_prog_sp [where e = "&\<Sigma>"]
       do_while_invr_vrt_hoare_prog_sp [where e = "&\<Sigma>"]
       from_until_invr_vrt_hoare_prog_sp[where e = "&\<Sigma>"]

term "(measure o Rep_uexpr) ((&y + 1) - &x)"  
  
section {*VCG*} 
    
named_theorems beautify_thms     
lemma thin_vwb_lens[beautify_thms]: "vwb_lens l \<Longrightarrow> P \<Longrightarrow> P" . 
lemma thin_weak_lens[beautify_thms]: "weak_lens l \<Longrightarrow> P \<Longrightarrow> P" .    
lemma [beautify_thms]: "\<not> ief_lens i \<Longrightarrow> P \<Longrightarrow> P" .  
lemma [beautify_thms]: "i\<bowtie>j \<Longrightarrow> P \<Longrightarrow> P" .  
lemma [beautify_thms]: "i\<noteq>(j::_\<Longrightarrow>_) \<Longrightarrow> P \<Longrightarrow> P" .
lemma [beautify_thms]: "i\<noteq>(j::_\<Longrightarrow>_) \<longrightarrow> i \<bowtie> j \<Longrightarrow> P \<Longrightarrow> P" .    
lemma [beautify_thms]: "get\<^bsub>i\<^esub> A = x \<Longrightarrow> P \<Longrightarrow> P" .  
      
method_setup insert_assms = \<open>Scan.succeed (fn _ => CONTEXT_METHOD (fn facts => fn (ctxt,st) => let
   val tac = HEADGOAL (Method.insert_tac ctxt facts)
   val ctxt = Method.set_facts [] ctxt
 in Method.CONTEXT ctxt (tac st)
 end))\<close>                      
                       
text {* The defer processing and the thin)tac processing in the sequel was inspired by tutorial5.thy in Peter Lammich course
        \url{https://bitbucket.org/plammich/certprog_public/downloads/}*}
 
subsection \<open>Deterministic Repeated Elimination Rule\<close>
text \<open>Attention: Slightly different semantics than @{method elim}: repeats the 
  rule as long as possible, but only on the first subgoal.\<close>

method_setup vcg_elim_determ = \<open>
  Attrib.thms >> (fn thms => fn ctxt => 
    SIMPLE_METHOD (REPEAT_DETERM1 (HEADGOAL (ematch_tac ctxt thms))))\<close>
text \<open>The \<open>DETERM\<close> combinator on method level\<close>
  
method_setup determ = \<open>
  Method.text_closure >>
    (fn (text) => fn ctxt => fn using => fn st =>
      Seq.DETERM (Method.evaluate_runtime text ctxt using) st
    )
\<close>        
(*method insert_assms =  tactic \<open>@{context} |>  Assumption.all_prems_of |> (@{context} |>  Method.insert_tac) |> FIRSTGOAL\<close>*)
                      
method hoare_sp_vcg_pre = (simp only: seqr_assoc[symmetric])?, rule post_weak_prog_hoare  

method hoare_sp_rule_apply = rule hoare_sp_rules

method hoare_wp_rule_apply = rule hoare_wp_rules

method hoare_annotaion_rule_apply = rule hoare_wp_rules  
named_theorems lens_laws_vcg_simps
lemmas [lens_laws_vcg_simps] =
  lens_indep.lens_put_irr1
  lens_indep.lens_put_irr2
  
method vcg_default_solver = assumption|pred_simp?;(simp add: LENS_GET_TAG_def lens_laws_vcg_simps)?;fail

method  vcg_pp_solver = ((unfold lens_indep_all_alt LENS_GET_TAG_def)?, (simp add:  lens_laws_vcg_simps)?, safe?; (simp add:  lens_laws_vcg_simps)?)
  
method vcg_default_goal_post_processing = 
       ((pred_simp+)?; vcg_pp_solver?;vcg_elim_determ beautify_thms)?
  
method vcg_step_solver methods solver = 
       (hoare_sp_rule_apply | solver)

  
definition DEFERRED :: "bool \<Rightarrow> bool" where "DEFERRED P = P"
lemma DEFERREDD: "DEFERRED P \<Longrightarrow> P" by (auto simp: DEFERRED_def)

lemma LENS_GET_RULE: "P  \<Longrightarrow> LENS_GET_TAG P" by simp

method vcg_can_defer =
  (match conclusion 
      in "DEFERRED _" \<Rightarrow> fail  -- \<open>Refuse to defer already deferred goals\<close>
       \<bar>
         "\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>P" \<Rightarrow> fail  -- \<open>Refuse to defer Hoare triples (They are no VCs!)\<close>
       \<bar> 
         "_" \<Rightarrow> succeed)
       
method vcg_can_elim =
  (match conclusion 
      in "get\<^bsub>_\<^esub> _ = _" \<Rightarrow> succeed  -- \<open>elim get function from conclusions\<close>
       \<bar> 
         "_" \<Rightarrow> fail)  
       
method vcg_defer = (vcg_can_defer, rule DEFERREDD, tactic \<open>FIRSTGOAL defer_tac\<close>)

method  hoare_sp_vcg_step = (hoare_sp_rule_apply | vcg_defer)
  
method  hoare_sp_vcg_steps = hoare_sp_vcg_pre, hoare_sp_vcg_step+ , (unfold DEFERRED_def)

method  hoare_sp_vcg_steps_pp = hoare_sp_vcg_steps; pred_simp?
  
method hoare_sp_default_vcg_all = (hoare_sp_vcg_pre, (vcg_step_solver \<open>vcg_default_solver\<close>| vcg_defer)+, (unfold DEFERRED_def)?)

method hoare_sp_pp_vcg_all = (hoare_sp_default_vcg_all; vcg_default_goal_post_processing)

section {*Experiments on VCG*}

subsection {* Through these experiments I want to observe the follwoing problems: 
              - I want to deal with the problem of nested existential
              - I want to deal with the problem of blow up due to the semantic machinary comming with lenses
              - I want to have modularity

*}
  
declare LENS_GET_TAG_def[simp del]   (*continue from here + add LENS_PUT_TAG*)  

definition LENS_GET_STOP :: "'t \<Rightarrow>'t" 
  where "LENS_GET_STOP v = v"
      
lemma increment_method: 
  assumes "vwb_lens x" "x \<bowtie> y" "vwb_lens y"
  shows  
    "\<lbrace>&y >\<^sub>u 0\<rbrace>
      x :== 0 ; 
      INVAR &y >\<^sub>u 0 \<and> &y \<ge>\<^sub>u &x 
      VRT \<guillemotleft>(measure o Rep_uexpr) (&y - &x)\<guillemotright> 
      WHILE &x <\<^sub>u &y DO x:== (&x + 1) OD
    \<lbrace>&y =\<^sub>u &x\<rbrace>\<^sub>P"
  apply (insert assms) (*Make this automatic *)
     apply (hoare_sp_pp_vcg_all)   
  done
  
subsection {*even count program*} 

lemma even_count_gen:
  assumes "lens_indep_all [i,j, endd]"
  assumes "vwb_lens x" "vwb_lens i" "vwb_lens j"  
  shows  
    "\<lbrace>&endd >\<^sub>u 0 \<rbrace>
       i :== \<guillemotleft>0::int\<guillemotright>;
       j :== 0 ; 
       INVAR  (&j =\<^sub>u (&i + 1) div 2 \<and> &i \<le>\<^sub>u &endd) 
       VRT \<guillemotleft>measure (nat o (Rep_uexpr (&endd - &i)))\<guillemotright>
       WHILE &i <\<^sub>u &endd
       DO
         IF &i mod 2 =\<^sub>u 0 
         THEN j :== (&j + 1)
         ELSE SKIP 
         FI;
        i :== (&i + 1)
       OD
    \<lbrace>&j =\<^sub>u (&endd + 1)div 2\<rbrace>\<^sub>P"  
  apply (insert assms)(*Make this automatic*)
  apply (hoare_sp_pp_vcg_all)
    apply (simp_all add: zdiv_zadd1_eq)
  done    
    
subsection {*sqrt program*}
  
definition Isqrt :: "int \<Rightarrow> int \<Rightarrow> bool" 
   where "Isqrt n\<^sub>0 r \<equiv> 0\<le>r \<and> (r-1)\<^sup>2 \<le> n\<^sub>0" 
     
lemma Isqrt_aux:
  "0 \<le> n\<^sub>0 \<Longrightarrow> Isqrt n\<^sub>0 1"
  "\<lbrakk>0 \<le> n\<^sub>0; r * r \<le> n\<^sub>0; Isqrt n\<^sub>0 r\<rbrakk> \<Longrightarrow> Isqrt n\<^sub>0 (r + 1)"
  "\<lbrakk>0 \<le> n\<^sub>0; \<not> r * r \<le> n\<^sub>0; Isqrt n\<^sub>0 r\<rbrakk> \<Longrightarrow> (r - 1)\<^sup>2 \<le> n\<^sub>0 \<and> n\<^sub>0 < r\<^sup>2"
  "Isqrt n\<^sub>0 r \<Longrightarrow> r * r \<le> n\<^sub>0 \<Longrightarrow> r\<le>n\<^sub>0"
  "\<lbrakk>0 \<le> n\<^sub>0; \<not> r * r \<le> n\<^sub>0; Isqrt n\<^sub>0 r\<rbrakk> \<Longrightarrow> 0 < r"
  apply (auto simp: Isqrt_def power2_eq_square algebra_simps)
  by (smt combine_common_factor mult_right_mono semiring_normalization_rules(3))
      
lemma sqrt_prog_correct:
  assumes "lens_indep_all [n, r]"
  assumes "vwb_lens r" "vwb_lens n" 
  shows
 "\<lbrace>0 \<le>\<^sub>u &n \<rbrace>
      r :== 1 ; 
      INVAR 0\<le>\<^sub>u &n \<and> bop Isqrt (&n) (&r)
      VRT  \<guillemotleft>measure (nat o (Rep_uexpr ((&n + 1) - &r)))\<guillemotright>
      WHILE (&r * &r \<le>\<^sub>u &n)
      DO 
       r :== (&r + 1)
      OD;
      r :== (&r - 1)
   \<lbrace>0\<le>\<^sub>u &r \<and> uop power2 (&r) \<le>\<^sub>u &n \<and> &n <\<^sub>u uop power2 (&r + 1)\<rbrace>\<^sub>P" 
  apply (insert assms)
   supply Isqrt_aux [simp]
  apply (hoare_sp_pp_vcg_all)
   (* I still have the problem with read only vars, ie., if a var is read only the get function show up in the goal
                                  One solution is to have an alternative definition for usubst_lookup*)
  done    
    
subsection {*gcd*}
    
lemma gcd_correct:
  assumes "lens_indep_all [a,r, b, x]"
  assumes "vwb_lens a" "vwb_lens r" "vwb_lens x" "vwb_lens b"
  shows  
"\<lbrace>&r =\<^sub>u &a \<and> &x =\<^sub>u &b \<and> &b>\<^sub>u 0 \<and> &a>\<^sub>u 0\<rbrace> 
   INVAR &r >\<^sub>u0 \<and> &x >\<^sub>u 0 \<and> bop gcd (&r) (&x) =\<^sub>u  bop gcd (&a) (&b)
   VRT \<guillemotleft>measure (Rep_uexpr (trop If (&r >\<^sub>u &x) (&r) (&x)))\<guillemotright>
   WHILE \<not>(&r =\<^sub>u &x)
   DO
    IF &r >\<^sub>u &x
    THEN r :== (&r - &x)
    ELSE x :== (&x - &r)
    FI
   OD
 \<lbrace>&r =\<^sub>u bop gcd (&a) (&b)\<rbrace>\<^sub>P"
  apply (insert assms)    
  apply (hoare_sp_pp_vcg_all)   
     apply (simp add: gcd_diff1_nat)+
   apply (metis gcd.commute gcd_diff1_nat not_le)+
  done       
    
subsection {*filter program*}
  
definition \<open>swap i j xs = xs[i := xs!j, j := xs!i]\<close>
abbreviation \<open>swap\<^sub>u \<equiv> trop swap\<close>

lemma set_swap[simp]:
  assumes \<open>i < length xs\<close>
      and \<open>j < length xs\<close>
    shows \<open>set (swap i j xs) = set xs\<close>
  using assms unfolding swap_def
  by simp

lemma swap_commute:
  \<open>swap i j xs = swap j i xs\<close>
  unfolding swap_def
  by (cases \<open>i = j\<close>) (auto simp: list_update_swap)

lemma swap_id[simp]:
  assumes \<open>i < length xs\<close>
  shows \<open>swap i i xs = xs\<close>
  using assms unfolding swap_def
  by simp

lemma drop_swap[simp]:
  assumes \<open>i < n\<close>
      and \<open>j < n\<close>
  shows \<open>drop n (swap i j xs) = drop n xs\<close>
  using assms unfolding swap_def
  by simp

lemma take_swap[simp]:
  assumes \<open>n \<le> i\<close>
      and \<open>n \<le> j\<close>
  shows \<open>take n (swap i j xs) = take n xs\<close>
  using assms unfolding swap_def
  by simp

lemma swap_length_id[simp]:
  assumes \<open>i < length xs\<close>
      and \<open>j < length xs\<close>
  shows \<open>length (swap i j xs) = length xs\<close>
  using assms unfolding swap_def
  by simp

lemma swap_nth1[simp]:
  assumes \<open>i < length xs\<close>
      and \<open>j < length xs\<close>
  shows \<open>swap i j xs ! i = xs ! j\<close>
  using assms unfolding swap_def
  by (simp add: nth_list_update)

lemma swap_nth2[simp]:
  assumes \<open>i < length xs\<close>
      and \<open>j < length xs\<close>
  shows \<open>swap i j xs ! j = xs ! i\<close>
  using assms unfolding swap_def
  by (simp add: nth_list_update)

lemma take_empty[simp]: 
  "take 0 a = []"
  " h = length a \<Longrightarrow>take h a = [] \<longleftrightarrow> h = 0"
  by auto+
    
lemma take_bwd_simp:"length a = h \<Longrightarrow> take h a = (if  0 < h then take (h -1) a @ [nth  a (h-1)] else [])" 
  by (metis One_nat_def Suc_pred diff_less hd_drop_conv_nth neq0_conv take_eq_Nil take_hd_drop zero_less_one)

lemma take_append1[simp]:
  " length a = h +1 \<Longrightarrow>take (h + 1) a = take h a  @ [nth a h]"
  apply (subst (1) take_bwd_simp)
   apply auto
  done  

lemma take_tail[simp]: 
  "h = length a \<Longrightarrow>  take h (drop 1 a)  = tl (take h a)"
  by (simp add: drop_Suc)
    
lemma take_butlast[simp]: 
  "h = length a \<Longrightarrow> take (h-1) a = butlast (take h a)"
  by (metis butlast_take le_refl)

lemma take_upd_outside[simp]:
  "i<0 \<Longrightarrow> h = length a\<Longrightarrow>take  h (a[i:=x])  = take h a"
  "h\<le>i \<Longrightarrow> h = length a\<Longrightarrow> take h (a[i:=x])  = take h a"
  by auto
 
lemma take_eq_iff: 
  "h = length a \<Longrightarrow> h = length a' \<Longrightarrow>
   take h a = take h a' \<longleftrightarrow> (\<forall>i. 0\<le>i \<and> i<h \<longrightarrow>  nth a i = nth a' i)"
  by (metis le0 nth_equalityI order_refl take_all)

definition 
  "filter_inv1 a r w (a\<^sub>0::int list) w\<^sub>0 r\<^sub>0= 
   (*execution path1*)
 ( &r \<le>\<^sub>u  #\<^sub>u(&a) \<and> &w \<le>\<^sub>u  &r \<and> 0 \<le>\<^sub>u  &w \<and> 0 \<le>\<^sub>u  &r \<and>
   (
   (5 <\<^sub>u bop nth (\<guillemotleft>a\<^sub>0\<guillemotright>)(\<guillemotleft>r\<^sub>0\<guillemotright>) \<and> \<guillemotleft>r\<^sub>0\<guillemotright> <\<^sub>u #\<^sub>u(\<guillemotleft>a\<^sub>0\<guillemotright>)  \<and>
   (*&a =\<^sub>u swap\<^sub>u \<guillemotleft>w\<^sub>0\<guillemotright> (\<guillemotleft>r\<^sub>0\<guillemotright>) \<guillemotleft>a\<^sub>0\<guillemotright> \<and>
   &w =\<^sub>u (\<guillemotleft>w\<^sub>0\<guillemotright> + 1) \<and>*) 
   (take\<^sub>u(\<guillemotleft>w\<^sub>0\<guillemotright> , &a)) =\<^sub>u (bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) (take\<^sub>u(\<guillemotleft>r\<^sub>0\<guillemotright>, \<guillemotleft>a\<^sub>0\<guillemotright>)))) \<or>
  
  (*execution path2*)
  (
   \<not>(5 <\<^sub>u bop nth (&a)(\<guillemotleft>r\<^sub>0\<guillemotright>)) \<and> \<guillemotleft>r\<^sub>0\<guillemotright> <\<^sub>u #\<^sub>u(&a) \<and>
   take\<^sub>u(#\<^sub>u(drop\<^sub>u(\<guillemotleft>r\<^sub>0\<guillemotright>, &a)),drop\<^sub>u(\<guillemotleft>r\<^sub>0\<guillemotright>, &a)) =\<^sub>u take\<^sub>u(#\<^sub>u(drop\<^sub>u(\<guillemotleft>r\<^sub>0\<guillemotright>, &a)),drop\<^sub>u(\<guillemotleft>r\<^sub>0\<guillemotright>,  &a)))) \<and> 
     &r =\<^sub>u (\<guillemotleft>r\<^sub>0\<guillemotright> + 1)

)"

term "(\<^bold>\<forall>(a\<^sub>0, r\<^sub>0, w\<^sub>0 , h\<^sub>0)\<bullet> \<^bold>\<exists>(a:: int list \<Longrightarrow> 'a, r, w, h)\<bullet> 
       &r \<le>\<^sub>u  #\<^sub>u(&a) \<and> &w \<le>\<^sub>u  &r \<and> 0 \<le>\<^sub>u  &w \<and> 0 \<le>\<^sub>u  &r \<and> &r =\<^sub>u (\<guillemotleft>r\<^sub>0\<guillemotright> + 1))"  
lemma " \<exists>a. a \<le> length(a\<^sub>0) \<and> (\<exists>b. take a b = filter (op < 5) a\<^sub>0)"
  using length_filter_le take_all by blast
lemma " \<exists>a. a \<le> length(a\<^sub>0) \<and> (\<exists>b. take a b = filter (op < 5) a\<^sub>0)"
  using length_filter_le take_all by blast

lemma
  assumes "vwb_lens (r:: nat \<Longrightarrow> 'b)"
  assumes " r \<sharp> (r\<^sub>0:: (nat, 'b) uexpr)" (*somehow logical variables are all variables satisfying this*)
  shows  
  "\<lbrace>&r =\<^sub>u r\<^sub>0\<rbrace> 
     r:== (&r+1)
    \<lbrace> &r =\<^sub>u (r\<^sub>0 + 1) \<rbrace>\<^sub>P"
  apply (insert assms)
  apply (hoare_sp_default_vcg_all)
  done
    
lemma filter_prog_loop_body_correct:
  assumes "lens_indep_all [r, w]"
  assumes "a \<bowtie> r" "a \<bowtie> w"  "r \<bowtie> w" 
  assumes "vwb_lens a" "vwb_lens r" "vwb_lens w"
  shows  
   "\<lbrace>&w =\<^sub>u \<guillemotleft>w\<^sub>0\<guillemotright> \<and> &r =\<^sub>u \<guillemotleft>r\<^sub>0\<guillemotright> \<and> &a =\<^sub>u \<guillemotleft>a\<^sub>0\<guillemotright>\<rbrace> 
        IF (&a)(&r)\<^sub>a >\<^sub>u (5)
        THEN a :== swap\<^sub>u (&w) (&r) (&a);
             w :== (&w + 1)
        ELSE SKIP
        FI ;
        r:== (&r+1)
    \<lbrace>((\<not>(\<guillemotleft>a\<^sub>0\<guillemotright>(\<guillemotleft>r\<^sub>0\<guillemotright>)\<^sub>a >\<^sub>u 5) \<and> &a =\<^sub>u \<guillemotleft>a\<^sub>0\<guillemotright> \<and>  &w =\<^sub>u \<guillemotleft>w\<^sub>0\<guillemotright>) \<or> 
      (\<guillemotleft>a\<^sub>0\<guillemotright>(\<guillemotleft>r\<^sub>0\<guillemotright>)\<^sub>a >\<^sub>u 5 \<and> &a =\<^sub>u swap\<^sub>u \<guillemotleft>w\<^sub>0\<guillemotright> \<guillemotleft>r\<^sub>0\<guillemotright> \<guillemotleft>a\<^sub>0\<guillemotright> \<and>  &w =\<^sub>u (\<guillemotleft>w\<^sub>0\<guillemotright> + 1))) \<and> 
       &r =\<^sub>u (\<guillemotleft>r\<^sub>0\<guillemotright> +1) \<rbrace>\<^sub>P"
   apply (insert assms)
   apply (hoare_sp_pp_vcg_all)
  done
   
     
lemma "5 < nth xb x \<Longrightarrow> x < get\<^bsub>h\<^esub> A \<Longrightarrow> h\<^sub>0 = get\<^bsub>h\<^esub> A \<Longrightarrow> xb = a\<^sub>0\<Longrightarrow>  h\<^sub>0 = length a\<^sub>0 \<Longrightarrow>
        take (Suc 0) (swap 0 x xb) = filter (op < 5) (take (Suc ( x)) a\<^sub>0)"
  unfolding swap_def
  apply auto
   
 oops
lemma filter_prog_correct:
  assumes "lens_indep_all [h,r, w]"
  assumes "a \<bowtie> h"  "a \<bowtie> r" "a \<bowtie> w" 
  assumes "vwb_lens a" "vwb_lens h" "vwb_lens r" "vwb_lens w"
  shows  
 "\<lbrace>&a =\<^sub>u \<guillemotleft>a\<^sub>0\<guillemotright> \<and> &h =\<^sub>u \<guillemotleft>h\<^sub>0\<guillemotright> \<and> \<guillemotleft>h\<^sub>0\<guillemotright> =\<^sub>u uop length \<guillemotleft>a\<^sub>0\<guillemotright>\<rbrace> 
      r:== 0; w :==0;
      INVR &h =\<^sub>u \<guillemotleft>h\<^sub>0\<guillemotright> \<and> &r \<le>\<^sub>u  &h \<and> &w \<le>\<^sub>u  &r \<and> 
           (take\<^sub>u(&w,  swap\<^sub>u (&w) (&r) (&a) ) =\<^sub>u (bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) take\<^sub>u(&r,  \<guillemotleft>a\<^sub>0\<guillemotright>) ))
             
      VRT  \<guillemotleft>measure ((Rep_uexpr (&h - &r)))\<guillemotright>
      WHILE &r<\<^sub>u &h
      DO 
       IF (&a)(&r)\<^sub>a >\<^sub>u (5)
       THEN a :== swap\<^sub>u (&w) (&r) (&a);
            w :== (&w + 1)
       ELSE SKIP
       FI ;
       r:== (&r+1)
      OD;
      h :==&w
 \<lbrace>&h \<le>\<^sub>u \<guillemotleft>h\<^sub>0\<guillemotright> \<and> ( take\<^sub>u(&h, &a) =\<^sub>u (bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) \<guillemotleft>a\<^sub>0\<guillemotright>) ) \<rbrace>\<^sub>P" 
  apply (insert assms)
      
  apply (hoare_sp_pp_vcg_all)  
    prefer 3
    
  oops
 term "gcd"   
  
lemma 
  assumes "lens_indep_all [h,r, w]"
  assumes "a \<bowtie> h"  "a \<bowtie> r" "a \<bowtie> w" 
  assumes "vwb_lens a" "vwb_lens h" "vwb_lens r" "vwb_lens w"
  shows  
 "\<lbrace>&w =\<^sub>u \<guillemotleft>w\<^sub>0\<guillemotright> \<and> &r =\<^sub>u \<guillemotleft>r\<^sub>0\<guillemotright> \<and> &a =\<^sub>u \<guillemotleft>a\<^sub>0\<guillemotright> \<and> &h =\<^sub>u \<guillemotleft>h\<^sub>0\<guillemotright> \<and>  
   \<guillemotleft>h\<^sub>0\<guillemotright> =\<^sub>u uop length \<guillemotleft>a\<^sub>0\<guillemotright>\<rbrace> 
      r:== 0; w :==0;
      INVR  &h =\<^sub>u \<guillemotleft>h\<^sub>0\<guillemotright> \<and> &r \<le>\<^sub>u  &h \<and> &w \<le>\<^sub>u  &r \<and>
            take\<^sub>u(&w, &a) =\<^sub>u (bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) (take\<^sub>u(&r ,(swap\<^sub>u (&w) (&r) ( \<guillemotleft>a\<^sub>0\<guillemotright>)))))
      VRT  \<guillemotleft>measure ((Rep_uexpr (&h - &r)))\<guillemotright>
      WHILE &r<\<^sub>u &h
      DO 
       IF (&a)(&r)\<^sub>a >\<^sub>u (5)
       THEN a :== swap\<^sub>u (&w) (&r) (&a);
            w :== (&w + 1)
       ELSE SKIP
       FI ;
       r:== (&r+1)
      OD;
      h :==&w
 \<lbrace>&h \<le>\<^sub>u \<guillemotleft>h\<^sub>0\<guillemotright>   \<and>
            take\<^sub>u(&h, &a) =\<^sub>u (bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) \<guillemotleft>a\<^sub>0\<guillemotright>) \<rbrace>\<^sub>P" 
   apply (insert assms)
  apply (hoare_sp_pp_vcg_all)
  unfolding swap_def


  oops
    
lemma 
  assumes "lens_indep_all [l, h, h\<^sub>0 ,r, w]"
  assumes "a \<bowtie> l"  "a \<bowtie> h" "a \<bowtie> h\<^sub>0" "a \<bowtie> r" "a \<bowtie> w"
  assumes "a\<^sub>0 \<bowtie> l"  "a\<^sub>0 \<bowtie> a" "a\<^sub>0 \<bowtie> h" "a\<^sub>0 \<bowtie> h\<^sub>0" "a\<^sub>0 \<bowtie> r" "a\<^sub>0 \<bowtie> w"  
  assumes "vwb_lens a" "vwb_lens l" "vwb_lens h" "vwb_lens r" "vwb_lens w"
  shows  
    (* a=a\<^sub>0 \<and> h=h\<^sub>0 \<and> l\<le>h*)
 "\<lbrace>&h =\<^sub>u \<guillemotleft>7::nat\<guillemotright> \<and> 0 \<le>\<^sub>u &h  \<and> &a =\<^sub>u \<guillemotleft>[1,6,7,8,3,2,9::int]\<guillemotright>\<rbrace> 
      r:== 0; w :==0;
      INVR  0 \<le>\<^sub>u &h \<and> &h =\<^sub>u \<guillemotleft>7\<guillemotright> \<and>
            0 \<le>\<^sub>u &w \<and> &w \<le>\<^sub>u &r \<and> &r\<le>\<^sub>u &h \<and> 
            &w =\<^sub>u  #\<^sub>u(bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) take\<^sub>u(&r, swap\<^sub>u (&w) (&r) (\<guillemotleft>[1,6,7,8,3,2,9::int]\<guillemotright>)))
            (*\<and> 
           (take\<^sub>u(&w , &a)) =\<^sub>u (bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) (take\<^sub>u(&r, \<guillemotleft>[1,6,7,9,3,2,9::int]\<guillemotright>)))

             \<and>
           
            ((take\<^sub>u(&w , &a)) =\<^sub>u (bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) (take\<^sub>u(&r, &a\<^sub>0))))
           \<and>
           (drop\<^sub>u((&r + 1), &a)) =\<^sub>u (drop\<^sub>u((&r + 1), &a\<^sub>0)) 

      I=\<lambda>(h\<^sub>0,a\<^sub>0). vars l h (a:imap) r w in 
      h=h\<^sub>0 \<and> l\<le>w \<and> w\<le>r \<and> r\<le>h \<and>
      lran a l w = filter (\<lambda>x. 5<x) (lran a\<^sub>0 l r) \<and>
      lran a r h = lran a\<^sub>0 r h*)
      VRT  \<guillemotleft>measure ((Rep_uexpr (&h - &r)))\<guillemotright>
      WHILE &r<\<^sub>u &h
      DO 
       IF (&a)(&r)\<^sub>a >\<^sub>u (5)
       THEN a :== swap\<^sub>u (&w) (&r) (\<guillemotleft>[1,6,7,8,3,2,9::int]\<guillemotright>);
            w :== (&w + 1)
       ELSE SKIP
       FI ;
       r:== (&r+1)
      OD;
      h :==&w
      (*  h\<le>h\<^sub>0 \<and> lran a l h = filter (\<lambda>x. 5<x) (lran a\<^sub>0 l h\<^sub>0)*)
     \<lbrace>&h =\<^sub>u 4 \<rbrace>\<^sub>P"
  apply (insert assms) (* Make this automatic*)
  apply hoare_sp_default_vcg_all
    apply vcg_default_goal_post_processing
   apply vcg_default_goal_post_processing
  unfolding swap_def     
    apply vcg_default_goal_post_processing
    
   oops  
          
find_theorems name: "LENS_GET_TAG_THMS"    
find_theorems name: "rep_eq" "(Rep_uexpr ?e = ?t)"  
update_uexpr_rep_eq_thms -- {* Read @{thm [source] uexpr_rep_eq_thms} here. *}  
thm uexpr_rep_eq_thms  
 
lemma 
  assumes "lens_indep_all [l, h, r, w]"
  assumes "a \<bowtie> l"  "a \<bowtie> h" "a \<bowtie> r" "a \<bowtie> w"
  assumes "old_a \<bowtie> l"  "old_a \<bowtie> a" "old_a \<bowtie> h" "old_a \<bowtie> r" "old_a \<bowtie> w"  
  assumes "vwb_lens a" "vwb_lens l" "vwb_lens h" "vwb_lens r" "vwb_lens w"
  shows  
 "\<lbrace>&l =\<^sub>u 0 \<and>  &l \<le>\<^sub>u &h \<and> #\<^sub>u(&a::(int list, _)uexpr)=\<^sub>u &h\<rbrace> 
      r:== &l; w :==&l;
      INVR &l =\<^sub>u 0 \<and>  #\<^sub>u(&a)  =\<^sub>u &h  \<and>
           &l \<le>\<^sub>u &h \<and> &l \<le>\<^sub>u &w \<and> &w \<le>\<^sub>u &r \<and> &r\<le>\<^sub>u &h \<and>
            &a =\<^sub>u  (bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) (take\<^sub>u(&r  - &l, &a)))\<and>
           take\<^sub>u(&w- &l, &a) =\<^sub>u  
           (bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) (take\<^sub>u(&r  - &l, &a)))
      VRT  \<guillemotleft>measure ((Rep_uexpr (&h - &r)))\<guillemotright>
      WHILE &r<\<^sub>u &h
      DO 
       IF (&a)(&r)\<^sub>a >\<^sub>u (5)
       THEN a :== (trop list_update (&a) (&w) (&a(&r)\<^sub>a)) ;
            w :== (&w + 1)
       ELSE SKIP
       FI ;
       r:== (&r+1)
      OD;
      h :==&w
     \<lbrace>(drop\<^sub>u(&r - &w, &a)) =\<^sub>u bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) (drop\<^sub>u(&r - &w, &a))\<rbrace>\<^sub>P"
  apply (insert assms) (*Make this automatic*)
  apply (hoare_sp_default_vcg_all) 
    apply pred_simp
  oops  
    
lemma lens_indepE:
  assumes "x \<bowtie> y"
  assumes " \<And> v u \<sigma>. put\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> \<sigma> v) u = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> \<sigma> u) v \<Longrightarrow> 
                   get\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> \<sigma> u) = get\<^bsub>y\<^esub> \<sigma> \<Longrightarrow> 
                   get\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> \<sigma> v) = get\<^bsub>x\<^esub> \<sigma> \<Longrightarrow> Q"
  shows Q
  using assms unfolding lens_indep_def
  by auto
    
lemma get_intro: (*generalise this law for any binary operation*)
  "(\<And>v. get\<^bsub>a\<^esub> A = v  \<Longrightarrow> v = uexpression) \<Longrightarrow> get\<^bsub>a\<^esub> A = uexpression"
  by auto
    

(*
  CLR r;; CLR w;;
  r::=$l;; w::=$l;;
  WHILE $r<$h DO (
    IF a\<^bold>[$r\<^bold>] > \<acute>5 THEN
      a\<^bold>[$w\<^bold>] ::= a\<^bold>[$r\<^bold>];;
      w::=$w+\<acute>1
    ELSE SKIP;;
    r::=$r+\<acute>1
  );;
  h::=$w

l=l\<^sub>0 \<and> h=h\<^sub>0 \<and> l\<^sub>0\<le>w \<and> w\<le>r \<and> r\<le>h \<and>
      lran a l w = filter (\<lambda>x. 5<x) (lran a\<^sub>0 l r) \<and>
      lran a r h = lran a\<^sub>0 r h
*)  

ML {*

val exists_get  = (Subgoal.FOCUS (fn focus => let 
                                val term_concl =  Thm.term_of(focus |> #concl);
                                val term_get = (Const (@{const_name "Lens_Laws.lens_get"}, @{typ "('a, 'b, 'c) lens_scheme \<Rightarrow> 'b \<Rightarrow> 'a"}));
                                val term_get_safe_extract = (term_get) (*|> Thm.cterm_of (focus |> #context)|> Thm.term_of*)
                                val exists_subterm_get = (term_concl |> ((fn c => c = term_get_safe_extract) |> Term.exists_subterm))
                              in
                                if exists_subterm_get 
                                then  no_tac
                                else  all_tac 
                              end)) ;
*}                                                  
ML 
{* open HOLogic;
mk_binop
*} 
term "lens_put X y d"
ML 
{*
val term_put = @{term "lens_put X s v"};

@{term "lens_get X (lens_put Y (lens_put Xy \<sigma> v) v)"} |> ((fn c => c = term_put)|> Term.exists_subterm)
*}

ML 
{*
val term_get = @{term "lens_get"};(*I l faut trouver une representation plus generale pour comparer
                                   SINON utilise le type de get  *)

@{term "lens_get X (lens_get X s)"} |> ((fn c => c = term_get)|> Term.exists_subterm)
*}
ML 
{*
fun ex P tm = P tm orelse
      (case tm of
        t $ u => ex P t orelse ex P u
      | Abs (_, _, t) => ex P t
      | _ => false);

@{term "lens_get X (lens_put Y (lens_put y \<sigma> v) v)"} |> ((fn c => c = term_get)|> ex);

@{term "lens_get X (lens_get X s)"}|> ((fn c => (case c of Const (_,@{typ "(_, _, _) lens_scheme \<Rightarrow> _ \<Rightarrow> _"}) => true 
                                                         | _ $ Const (_,@{typ "(_, _, _) lens_scheme \<Rightarrow> _ \<Rightarrow> _"}) => true
                                                         | Const (_,@{typ "(_, _, _) lens_scheme \<Rightarrow> _ \<Rightarrow> _"})$ _ => true
                                                         | _ $Const (_,@{typ "(_, _, _) lens_scheme \<Rightarrow> _ \<Rightarrow> _"})$ _ => true  
                                                         | _ => false))|> Term.exists_subterm);
@{term "lens_get X (lens_get X s)"}
*}


ML {*Theory.setup (Method.setup @{binding exists_get_tac} 
                  (Scan.succeed (fn ctxt => ((SIMPLE_METHOD' (exists_get ctxt)))))
                  "checks occurens of get_lens in a given goal conclusion");


*}
  
lemma aext_rep_eq':
  "LENS_GET_TAG (\<lbrakk>x \<oplus>\<^sub>p xa\<rbrakk>\<^sub>e = (\<lambda>b. \<lbrakk>x\<rbrakk>\<^sub>e (get\<^bsub>xa\<^esub> b)))"
  unfolding LENS_GET_TAG_def
  by (simp add: utp_tactics.uexpr_rep_eq_thms(8))  
find_theorems name: "rep_eq" "LENS_GET_TAG (Rep_uexpr ?e = ?t)"
(*
On a trois theorem qui genere get functions:
  - utp_expr.var.rep_eq
  - utp_subst.usubst_lookup.rep_eq
  - utp_rel.rel_alpha_ext.rep_eq

In order to tag this laws with GET_TAG, we add a definition: GET_TAG P = P
We use this definition as a wrapper for the 3 theorems listed above.

In order to make pred_simp use this get tag:

- We add GET_TAG to the simpset in order we do not affact the UTP setup
- We remove GET_TAG from simpset in the VCG theory in order it appears in our goals

Once we have GET_TAG in our goals we can control these goals...

*)
thm utp_expr.var.rep_eq  
 
lemma 
  assumes "lens_indep_all [l, h, r, w]"
  assumes "a \<bowtie> l"  "a \<bowtie> h" "a \<bowtie> r" "a \<bowtie> w"
  assumes "old_a \<bowtie> l"  "old_a \<bowtie> h" "old_a \<bowtie> r" "old_a \<bowtie> w"  
  assumes "vwb_lens a" "vwb_lens l" "vwb_lens h" "vwb_lens r" "vwb_lens w"
  shows  
 "\<lbrace>  &l =\<^sub>u 0 \<and> #\<^sub>u(&old_a::(int list, _)uexpr) =\<^sub>u &h \<and> &l \<le>\<^sub>u &h \<and>&a =\<^sub>u &old_a  \<rbrace> 
      r:== &l; w :==&l;
      INVR  #\<^sub>u(&old_a)  =\<^sub>u &h  \<and> &l =\<^sub>u 0 \<and>
           &l \<le>\<^sub>u &w \<and> &w \<le>\<^sub>u &r \<and> &r\<le>\<^sub>u &h \<and>
            &a =\<^sub>u  (bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) (take\<^sub>u(&r  - &l, &old_a)))\<and>
           take\<^sub>u(&w- &l, &a) =\<^sub>u  
           (bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) (take\<^sub>u(&r  - &l, &old_a)))\<and>
           drop\<^sub>u(&h- &r, &a) =\<^sub>u drop\<^sub>u(&h- &r, &old_a)
   
      VRT  \<guillemotleft>measure ((Rep_uexpr (&h - &r)))\<guillemotright>
      WHILE &r<\<^sub>u &h
      DO 
       IF (&a)(&r)\<^sub>a >\<^sub>u (5)
       THEN a :== (trop list_update (&a) (&w) (&a(&r)\<^sub>a)) ;
            w :== (&w + 1)
       ELSE SKIP
       FI ;
       r:== (&r+1)
      OD;
      h :==&w
     \<lbrace> (take\<^sub>u(&h  - &l, &a)) =\<^sub>u bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) (take\<^sub>u(&h  - &l, &old_a))\<rbrace>\<^sub>P"
 
  apply (insert assms) (*Make this automatic*)
  apply (hoare_sp_pp_vcg_all)

           apply (vcg_elim_determ beautify_thms)
           apply (vcg_can_elim, determ \<open>(rule get_intro_gen)\<close>)+
  oops
    
subsection {* I want to solve the problem of nested existential*}
   
term "Abs_uexpr (\<lambda> st. (Rep_uexpr (&y) st)  = y\<^sub>0  \<and> y\<^sub>0 > 0)" 
term "Abs_uexpr (\<lambda> st. (Rep_uexpr (&y) st) =  y\<^sub>0 \<and> (Rep_uexpr (&x) st) \<le> y\<^sub>0 \<and> y\<^sub>0 > 0)"    
term "Abs_uexpr (\<lambda> st. (Rep_uexpr (&y) st)  = y\<^sub>0 \<and> (Rep_uexpr (&x) st) = y\<^sub>0) "  
term "(\<lambda> x \<bullet> &y >\<^sub>u x)  "
term "((\<lambda> f x. f x) o Rep_uexpr) (&y >\<^sub>u 0)"  
term "\<guillemotleft>\<lambda> st. x = (Rep_uexpr (&y >\<^sub>u 0) st)\<guillemotright>"
term "\<guillemotleft>\<lambda> st. y\<^sub>0 = Rep_uexpr (&y) st\<guillemotright> "
term "(&y >\<^sub>u 0)"  


lemma udeduct_tautI': "\<forall> b. \<lbrakk>p\<rbrakk>\<^sub>eb  \<Longrightarrow> `p`"
  using taut.rep_eq by blast    
lemma blahblah: 
  assumes "vwb_lens x" "x \<bowtie> y" "vwb_lens y"
  shows  
    "\<lbrace>Abs_uexpr (\<lambda> st. (Rep_uexpr (&y) st) = y\<^sub>0  \<and> y\<^sub>0 > 0)\<rbrace>
      x :== 0 ; 
      INVR Abs_uexpr (\<lambda> st. (Rep_uexpr (&y) st) =  y\<^sub>0 \<and> (Rep_uexpr (&x) st) \<le> y\<^sub>0 \<and> y\<^sub>0 > 0)
      VRT \<guillemotleft>(measure o Rep_uexpr) ((&y + 1) - &x)\<guillemotright> 
      WHILE &x <\<^sub>u &y DO x:== (&x + 1) OD
    \<lbrace>Abs_uexpr (\<lambda> st. (Rep_uexpr (&y) st) = y\<^sub>0 \<and> (Rep_uexpr (&x) st) = y\<^sub>0)\<rbrace>\<^sub>P"
  apply (insert assms) (*Make this automatic*)
  apply (hoare_sp_vcg_steps; pred_simp?) 
   apply (unfold lens_indep_all_alt) 
   apply (simp_all add: lens_laws_vcg_simps)
  apply (elim disjE conjE) 
    apply (simp)
       apply simp
      apply simp
     apply (simp add: usubst)
     apply (rule  udeduct_tautI)
    apply (rule uintro)
     apply (erule ushExE)
     apply (erule ushExE')
    apply (subst (asm) Abs_uexpr_inverse)
     apply (subst Abs_uexpr_inverse)
    
  find_theorems name:"Abs_uexp"
    find_theorems name:"Rep_uexp"
    thm utp_expr.rep_eq
    apply simp
     apply pred_simp
    apply (subst (asm) HOL.eq_commute[symmetric])
    apply (simp)
    apply (vcg_default_solver)+
  apply (hoare_sp_vcg_all) 
 done    
(*
TODO List for next iteration:

- Create an instantiation of while loop where E = "&\<Sigma>"
- Make an eisbach version for vcg_step
- Hide lens_indep in hoare triple 
- Hide lens properties: such as vwb_lens
*)          
find_theorems name:"H1_H2_impl_"    

end

