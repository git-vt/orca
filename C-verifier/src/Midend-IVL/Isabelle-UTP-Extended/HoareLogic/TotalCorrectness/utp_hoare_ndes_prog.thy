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


subsection {*Hoare triple definition*}

lift_definition hoare_prog_t :: "'\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>P") 
 is  hoare_d .

declare hoare_prog_t.rep_eq [prog_rep_eq]

lemma hoare_true_assisgns_prog_t: 
  "\<lbrace>p\<rbrace> \<langle>\<sigma>\<rangle>\<^sub>p \<lbrace>true\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma hoare_true_skip_prog_t: 
  "\<lbrace>p\<rbrace>SKIP\<lbrace>true\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma hoare_false_prog_t: 
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

lemma assigns_prog_hoare_prog_backward_t: 
  assumes"`p \<Rightarrow> \<sigma> \<dagger> q`" 
  shows  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>p\<lbrace>q\<rbrace>\<^sub>P"
  using assms  
  by (simp add: prog_rep_eq hoare_des)

lemma assigns_prog_hoare_prog_backward_t'[hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  "\<lbrace>\<sigma> \<dagger> p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>p\<lbrace>p\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma assigns_prog_floyd_t[hoare_sp_rules]:
  assumes "vwb_lens x"
  shows \<open>\<lbrace>p\<rbrace>x :== e\<lbrace>\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrace>\<^sub>P\<close>
  using assms  
  by (simp add: assms prog_rep_eq hoare_des)

subsection {*Hoare for Sequential Composition*}
lemma seq_hoare_invariant: 
 "\<lbrakk> \<lbrace>p\<rbrace>Q\<^sub>1\<lbrace>p\<rbrace>\<^sub>P ; \<lbrace>p\<rbrace>Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>P \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>Q\<^sub>1 ; Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>P"

  apply (simp add: prog_rep_eq ) 
  apply rel_blast 
  done
    
lemma seq_hoare_stronger_pre_1: 
  "\<lbrakk> \<lbrace>p \<and> q\<rbrace>Q\<^sub>1\<lbrace>p \<and> q\<rbrace>\<^sub>P ; \<lbrace>p \<and> q\<rbrace>Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>P \<rbrakk> \<Longrightarrow> \<lbrace>p \<and> q\<rbrace>Q\<^sub>1 ; Q\<^sub>2\<lbrace>q\<rbrace>\<^sub>P"
 apply (simp add: prog_rep_eq ) 
  apply rel_blast 
  done

lemma seq_hoare_stronger_pre_2: 
  "\<lbrakk> \<lbrace>p \<and> q\<rbrace>Q\<^sub>1\<lbrace>p \<and> q\<rbrace>\<^sub>P ; \<lbrace>p \<and> q\<rbrace>Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>P \<rbrakk> \<Longrightarrow> \<lbrace>p \<and> q\<rbrace>Q\<^sub>1 ; Q\<^sub>2\<lbrace>p\<rbrace>\<^sub>P"
 apply (simp add: prog_rep_eq ) 
  apply rel_blast 
  done
    
lemma seq_hoare_prog[hoare_wp_rules, hoare_sp_rules]: 
  assumes"\<lbrace>p\<rbrace>C\<^sub>1\<lbrace>s\<rbrace>\<^sub>P" and "\<lbrace>s\<rbrace>C\<^sub>2\<lbrace>r\<rbrace>\<^sub>P" 
  shows"\<lbrace>p\<rbrace>C\<^sub>1 ; C\<^sub>2\<lbrace>r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)  

subsection {*Hoare for Conditional*}

lemma cond_prog_hoare_prog_t: 
  assumes "\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>P" and "\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>IF b THEN C\<^sub>1 ELSE C\<^sub>2 FI\<lbrace>q\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des) 

lemma cond_prog_hoare_prog_wp'[hoare_wp_rules, hoare_wp_proof_annotation_rules]: 
  assumes "\<lbrace>p'\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>P" and "\<lbrace>p''\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>P"
  shows "\<lbrace>(b \<and> p')\<or> (\<not>b \<and> p'')\<rbrace>IF b THEN C\<^sub>1 ELSE C\<^sub>2 FI\<lbrace>q\<rbrace>\<^sub>P"
  using assms
  apply (simp add: prog_rep_eq ) 
  apply pred_simp
  done  
    
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
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>P"
  shows "\<lbrace>invar\<rbrace>WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P" 
  by (rule consequence_hoare_prog[OF uimp_refl _ PHI,
                                  OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                  OF consequence_hoare_prog[OF I0' induct_step uimp_refl]])

lemma while_invr_hoare_prog_wp:
  assumes WF: "wf R"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>P"
  shows "\<lbrace>invar\<rbrace>INVAR invar WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P"                              
  unfolding while_lfp_invr_prog_def
  by (rule consequence_hoare_prog[OF uimp_refl _ PHI,
                                 OF while_hoare_prog_minimal[OF WF uimp_refl, of _ _ e],
                                 OF consequence_hoare_prog[OF I0' induct_step uimp_refl]])

lemma while_invr_vrt_hoare_prog_wp:
  assumes WF: "wf R"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<rbrace>\<^sub>P"
  shows "\<lbrace>invar\<rbrace>INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b DO body OD\<lbrace>q\<rbrace>\<^sub>P"                              
  unfolding while_lfp_invr_vrt_prog_def
  by (rule consequence_hoare_prog[OF uimp_refl _ PHI,
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
  by (simp add: uintro PHI seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF uimp_refl]
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
    
lemma from_until_invr_vrt_hoare_prog_wp:
  assumes WF: "wf R"   
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`exit \<and> invar \<Rightarrow> q`"  
  assumes I0': "\<And>st. `\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar VRT \<guillemotleft>R\<guillemotright> UNTIL exit DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding from_until_lfp_invr_vrt_prog_def
  using from_until_hoare_prog_wp [OF WF  seq_step PHI I0' induct_step] .
    
lemma from_until_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0': "`q'' \<Rightarrow> invar`"    
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P" 
  unfolding from_until_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0']
                       while_hoare_prog_consequence[OF WF uimp_refl _ uimp_refl induct_step I0])

lemma from_until_invr_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P" 
  unfolding from_until_lfp_invr_prog_def
  using from_until_hoare_prog_sp[OF WF seq_step I0' induct_step I0] .  

lemma from_until_invr_vrt_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>P"
   assumes I0': "`q'' \<Rightarrow> invar`"    
  assumes induct_step: "\<And>st. \<lbrace>\<not> exit \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P" 
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and>(e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"     
  shows "\<lbrace>p\<rbrace>FROM init INVAR invar VRT \<guillemotleft>R\<guillemotright> UNTIL exit DO body OD\<lbrace>exit \<and> invar\<rbrace>\<^sub>P" 
  unfolding from_until_lfp_invr_vrt_prog_def
  using from_until_hoare_prog_sp[OF WF seq_step I0' induct_step I0] .

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
  assumes seq_step: "\<lbrace>invar\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>invar\<rbrace>DO body WHILE b OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding do_while_lfp_prog_def_alt 
  by (simp add: uimp_refl seq_hoare_prog[OF seq_step] 
                   while_hoare_prog_wp[OF WF PHI I0' induct_step])

lemma do_while_invr_hoare_prog_wp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>invar\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>invar\<rbrace>DO body INVAR invar WHILE b OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_prog_def do_while_lfp_prog_def_alt
  by (simp add: uimp_refl seq_hoare_prog[OF seq_step]
                while_hoare_prog_wp[OF WF PHI I0' induct_step])

lemma do_while_invr_vrt_hoare_prog_wp:
  assumes WF: "wf R"  
  assumes seq_step: "\<lbrace>invar\<rbrace>body\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI : "`\<not>b  \<and> invar \<Rightarrow> q`"
  assumes I0': "\<And>st. `b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"  
  assumes induct_step: "\<And> st. \<lbrace>p' st\<rbrace>body\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>invar\<rbrace>DO body INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_vrt_prog_def do_while_lfp_invr_prog_def do_while_lfp_prog_def_alt
  by (simp add: seq_hoare_prog[OF seq_step] 
                while_hoare_prog_wp[OF WF PHI I0' induct_step])

lemma do_while_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body WHILE b OD\<lbrace>\<not>b  \<and> invar\<rbrace>\<^sub>P"
  unfolding  do_while_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0']
                   while_hoare_prog_sp[OF WF uimp_refl induct_step I0])
                 
lemma do_while_invr_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body INVAR invar WHILE b OD\<lbrace>\<not>b  \<and> invar\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_prog_def do_while_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0']
                   while_hoare_prog_sp[OF WF uimp_refl induct_step I0])
                 
lemma do_while_invr_vrt_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>body\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And> st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>DO body INVAR invar VRT \<guillemotleft>R\<guillemotright> WHILE b OD\<lbrace>\<not>b  \<and> invar\<rbrace>\<^sub>P"
  unfolding do_while_lfp_invr_vrt_prog_def do_while_lfp_prog_def_alt
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0']
                   while_hoare_prog_sp[OF WF uimp_refl induct_step I0])
                 
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
  unfolding for_lfp_prog_def_alt
  by (simp add: uimp_refl seq_hoare_prog[OF seq_step]
                while_hoare_prog_wp[OF WF PHI I0' induct_step])

lemma for_invr_hoare_prog_wp:
  assumes WF : "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e=\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) INVAR invar DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_prog_def for_lfp_prog_def_alt
  by (simp add: uimp_refl seq_hoare_prog[OF seq_step] 
                while_hoare_prog_wp[OF WF PHI I0' induct_step])

lemma for_invr_vrt_hoare_prog_wp:
  assumes WF : "wf R"
  assumes seq_step: "\<lbrace>p\<rbrace>init\<lbrace>invar\<rbrace>\<^sub>P"
  assumes PHI: "`\<not>b \<and> invar \<Rightarrow>q`"  
  assumes I0': "\<And>st. `b \<and> invar \<and> e=\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> p' st`"
  assumes induct_step: "\<And>st. \<lbrace>p' st\<rbrace>body;incr\<lbrace>invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) INVAR invar VRT \<guillemotleft>R\<guillemotright>DO body OD\<lbrace>q\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_vrt_prog_def for_lfp_prog_def_alt
  by (simp add: seq_hoare_prog[OF seq_step]
                while_hoare_prog_wp[OF WF  PHI I0' induct_step])

lemma for_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0': "`q'' \<Rightarrow> invar`"  
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding for_lfp_prog_def_alt  
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0']
                while_hoare_prog_sp[OF WF uimp_refl induct_step I0])
 
lemma for_invr_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0':  "`q'' \<Rightarrow> invar`"
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) INVAR invar DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_prog_def for_lfp_prog_def_alt  
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0']
                while_hoare_prog_sp[OF WF uimp_refl induct_step I0])
     
    
lemma for_invr_vrt_hoare_prog_sp:
  assumes WF: "wf R"
  assumes seq_step:"\<lbrace>p\<rbrace>init\<lbrace>q''\<rbrace>\<^sub>P"
  assumes I0':"`q''\<Rightarrow> invar`" 
  assumes induct_step: "\<And>st. \<lbrace>b \<and> invar \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body;incr\<lbrace>q' st\<rbrace>\<^sub>P"
  assumes I0: "\<And>st. `q' st \<Rightarrow> invar \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>`"  
  shows "\<lbrace>p\<rbrace>FOR (init,b,incr) INVAR invar VRT \<guillemotleft>R\<guillemotright>DO body OD\<lbrace>\<not>b \<and> invar\<rbrace>\<^sub>P"
  unfolding for_lfp_invr_vrt_prog_def for_lfp_prog_def_alt  
  by (simp add: uintro uimp_refl seq_hoare_prog[OF seq_step] pre_str_prog_hoare[OF I0']
                while_hoare_prog_sp[OF WF uimp_refl induct_step I0])
     
lemmas loop_invr_vrt_hoare_prog_sp_instantiated [hoare_sp_rules] = 
       while_invr_vrt_hoare_prog_sp [where e = "&\<Sigma>"]
       for_invr_vrt_hoare_prog_sp [where e = "&\<Sigma>"]
       do_while_invr_vrt_hoare_prog_sp [where e = "&\<Sigma>"]
       from_until_invr_vrt_hoare_prog_sp[where e = "&\<Sigma>"]

lemmas loop_invr_vrt_hoare_prog_wp_instantiated [hoare_wp_rules] = 
       while_invr_vrt_hoare_prog_wp [where e = "&\<Sigma>"]
       for_invr_vrt_hoare_prog_wp [where e = "&\<Sigma>"]
       do_while_invr_vrt_hoare_prog_wp [where e = "&\<Sigma>"]
       from_until_invr_vrt_hoare_prog_wp[where e = "&\<Sigma>"]
    
end

