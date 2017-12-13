theory utp_hoare_ndes_prog

imports "../../../AlgebraicLaws/IMP_Prog/algebraic_laws_prog"

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

named_theorems hoare_prog and hoare_sp_vcg_rules

subsection {*Hoare triple definition*}

lift_definition hoare_prog_t :: "'\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>P") 
 is  hoare_d .

declare hoare_prog_t.rep_eq [prog_rep_eq]

lemma hoare_true_assisgns_prog_t[hoare_prog]: 
  "\<lbrace>p\<rbrace> \<langle>\<sigma>\<rangle>\<^sub>p \<lbrace>true\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma hoare_true_skip_prog_t[hoare_prog]: 
  "\<lbrace>p\<rbrace>SKIP\<lbrace>true\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma hoare_false_prog_t[hoare_prog]: 
  "\<lbrace>false\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

subsection {*Precondition weakening*}

lemma hoare_pre_str_prog_t[hoare_prog]:
  assumes "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" and "\<lbrace>p\<^sub>2\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<^sub>1\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P" 
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Post-condition strengthening*}

lemma hoare_post_weak_prog_t[hoare_prog]:
  assumes "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>2\<rbrace>\<^sub>P" and "`q\<^sub>2 \<Rightarrow> q\<^sub>1`"
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>1\<rbrace>\<^sub>P" 
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Hoare and assertion logic*}

lemma hoare_prog_conj_prog_t [hoare_prog]: 
  assumes"\<lbrace>p\<rbrace>C\<lbrace>r\<rbrace>\<^sub>P" and "\<lbrace>p\<rbrace>C\<lbrace>s\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>C\<lbrace>r \<and> s\<rbrace>\<^sub>P"
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Hoare SKIP*}

lemma skip_prog_hoare_prog_t [hoare_prog]: 
  "\<lbrace>p\<rbrace>SKIP\<lbrace>p\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

subsection {*Hoare for assignment*}

lemma assigns_prog_hoare_prog_backward_t [hoare_prog]: 
  assumes"`p \<Rightarrow> \<sigma> \<dagger> q`" 
  shows  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>p\<lbrace>q\<rbrace>\<^sub>P"
  using assms  
  by (simp add: prog_rep_eq hoare_des)

lemma assigns_prog_hoare_prog_backward_t' [hoare_prog]: 
  "\<lbrace>\<sigma> \<dagger> p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>p\<lbrace>p\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma assigns_prog_floyd_t [hoare_prog]:
  assumes "vwb_lens x"
  shows \<open>\<lbrace>p\<rbrace>x :== e\<lbrace>\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrace>\<^sub>P\<close>
  using assms  
  by (simp add: assms prog_rep_eq hoare_des)

subsection {*Hoare for Sequential Composition*}

lemma seq_hoare_prog_t [hoare_prog]: 
  assumes"\<lbrace>p\<rbrace>C\<^sub>1\<lbrace>s\<rbrace>\<^sub>P" and "\<lbrace>s\<rbrace>C\<^sub>2\<lbrace>r\<rbrace>\<^sub>P" 
  shows"\<lbrace>p\<rbrace>C\<^sub>1 ; C\<^sub>2\<lbrace>r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)  

subsection {*Hoare for Conditional*}

lemma cond_prog_hoare_prog_t [hoare_prog]: 
  assumes "\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>P" and "\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>IF b THEN C\<^sub>1 ELSE C\<^sub>2 FI\<lbrace>q\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des) 

    
lemma cond_prog_hoare_prog_t'[hoare_des]:
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
   
lemma mu_prog_rec_hoare_prog_t [hoare_prog]:
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<And> st P. \<lbrace>Pre \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace> P \<lbrace>Post\<rbrace>\<^sub>P \<Longrightarrow> \<lbrace>Pre \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> F P \<lbrace>Post\<rbrace>\<^sub>P"   
  shows "\<lbrace>Pre\<rbrace>\<mu>\<^sub>p F \<lbrace>Post\<rbrace>\<^sub>P"
  apply (simp add: prog_rep_eq)
  apply (subst normal_design_theory_continuous.LFP_healthy_comp)  
  apply (rule mu_d_rec_hoare_d_t[OF WF mono_Monotone_prog[OF M] N_prog_funcset, 
                                    simplified, OF induct_step[unfolded prog_rep_eq]])
  apply (simp add: Abs_prog_Rep_prog_Ncarrier)   
  apply (simp add: Healthy_if is_Ncarrier_is_ndesigns)
  done
    
lemma mu_prog_rec_hoare_prog_t' [hoare_prog]:
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<And> st P. \<lbrace>Pre \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace> P \<lbrace>Post\<rbrace>\<^sub>P \<Longrightarrow> \<lbrace>Pre \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> F P \<lbrace>Post\<rbrace>\<^sub>P" 
  assumes I0: "`Pre' \<Rightarrow> Pre`"  
  shows "\<lbrace>Pre'\<rbrace>\<mu>\<^sub>p F \<lbrace>Post\<rbrace>\<^sub>P"
  by (simp add: hoare_pre_str_prog_t[OF I0 mu_prog_rec_hoare_prog_t[OF WF M induct_step]])

subsection {*Hoare for frames*}
  
lemma antiframe_hoare_p_t[hoare_prog]:
  assumes "vwb_lens a"
  assumes "a \<sharp> r" 
  assumes "a \<natural> q"    
  assumes "\<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>P"  
  shows "\<lbrace>p \<and> r\<rbrace>a:[P]\<lbrace>q \<and> r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)

lemma antiframe_goare_p_t_stronger[hoare_prog]:
  assumes "vwb_lens a"
  assumes "a \<sharp> r" 
  assumes "a \<natural> q"    
  assumes "\<lbrace>p \<and> r\<rbrace>P\<lbrace>q\<rbrace>\<^sub>P"  
  shows "\<lbrace>p \<and> r\<rbrace>a:[P]\<lbrace>q \<and> r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)    
    
lemma frame_hoare_p_t[hoare_prog]:
  assumes "vwb_lens a"
  assumes "a \<natural> r" 
  assumes "a \<sharp> q"    
  assumes "\<lbrace>p\<rbrace>P\<lbrace>q\<rbrace>\<^sub>P"  
  shows "\<lbrace>p \<and> r\<rbrace> a:\<lbrakk>P\<rbrakk> \<lbrace>q \<and> r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)

lemma frame_hoare_p_t_stronger[hoare_prog]:
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
    
    
subsection {*Hoare for while iteration*}   

lemma while_invr_hoare_prog_t [hoare_prog]:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`" 
  assumes induct_step:"\<And>e. \<lbrace>b \<and> I \<and> E =\<^sub>u \<guillemotleft>e\<guillemotright>\<rbrace> body \<lbrace>I \<and>(E,\<guillemotleft>e\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"  
  assumes PHI:"`(\<not> b \<and> I) \<Rightarrow> Post`"  
  shows "\<lbrace>Pre\<rbrace>INVR I WHILE b DO body OD \<lbrace>Post\<rbrace>\<^sub>P"
  unfolding pwhile_inv_prog_def
  by (simp add: prog_rep_eq while_hoare_ndesign_t[unfolded While_inv_ndes_def, OF WF I0  Rep_prog_H1_H3_closed[THEN H1_H3_impl_H2, THEN H1_H2_impl_H1] induct_step[unfolded prog_rep_eq] PHI])

lemma while_invr_vrt_hoare_prog_t [hoare_des]:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`"
  assumes induct_step:"\<And> st. \<lbrace>b \<and> I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>I \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"  
  assumes PHI:"`(\<not> b \<and> I) \<Rightarrow> Post`"  
  shows "\<lbrace>Pre\<rbrace>INVR I VRT \<guillemotleft>R\<guillemotright>  WHILE b DO body OD\<lbrace>Post\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq while_hoare_ndesign_t[unfolded While_inv_ndes_def, OF WF I0  Rep_prog_H1_H3_closed[THEN H1_H3_impl_H2, THEN H1_H2_impl_H1] induct_step[unfolded prog_rep_eq] PHI])

lemma while_invr_vrt_hoare_prog_t' [hoare_des]:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`"     
  assumes induct_step:"\<And>st. \<lbrace>b \<and> I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace> P st \<rbrace>\<^sub>P"  
  assumes I0': "\<And>st. `P st \<Rightarrow>I \<and> (E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>`"    
  shows "\<lbrace>Pre\<rbrace>INVR I VRT \<guillemotleft>R\<guillemotright>  WHILE b DO body OD\<lbrace>\<not>b \<and> I\<rbrace>\<^sub>P"
proof (rule while_invr_vrt_hoare_prog_t[OF WF I0, of _ E], goal_cases)
  case (1 st)
  then show ?case using induct_step I0' unfolding prog_rep_eq by pred_blast
next
  case 2
  then show ?case by pred_simp 
qed
  
lemma while_invr_hoare_r':
  assumes \<open>\<lbrace>p \<and> b\<rbrace>C\<lbrace>p'\<rbrace>\<^sub>u\<close> and \<open>`pre \<Rightarrow> p`\<close>   and \<open>`p' \<Rightarrow> p`\<close>
  shows \<open>\<lbrace>pre\<rbrace>while b invr p do C od\<lbrace>\<not>b \<and> p\<rbrace>\<^sub>u\<close>
  by (metis while_inv_def assms hoare_post_weak hoare_pre_str while_hoare_r)
    
lemmas while_invr_vrt_hoare_prog_t_instantiated = 
       while_invr_vrt_hoare_prog_t'[where E = "&\<Sigma>"]
       
term "(measure o Rep_uexpr) ((&y + 1) - &x)"  
  
section {*VCG*} 
lemmas [hoare_sp_vcg_rules] =  
  assigns_prog_floyd_t seq_hoare_prog_t cond_prog_hoare_prog_t'  
  while_invr_vrt_hoare_prog_t_instantiated skip_prog_hoare_prog_t
  
method_setup insert_assms = \<open>Scan.succeed (fn _ => CONTEXT_METHOD (fn facts => fn (ctxt,st) => let
   val tac = HEADGOAL (Method.insert_tac ctxt facts)
   val ctxt = Method.set_facts [] ctxt
 in Method.CONTEXT ctxt (tac st)
 end))\<close>                      
        
(*method insert_assms =  tactic \<open>@{context} |>  Assumption.all_prems_of |> (@{context} |>  Method.insert_tac) |> FIRSTGOAL\<close>*)
                      
method hoare_sp_vcg_pre = (simp only: seqr_assoc[symmetric])?, rule hoare_post_weak_prog_t  

method hoare_sp_vcg_rule = rule hoare_sp_vcg_rules

named_theorems lens_laws_vcg_simps
lemmas [lens_laws_vcg_simps] =
  lens_indep.lens_put_irr1
  lens_indep.lens_put_irr2
  
method vcg_default_solver = assumption|pred_simp?;(simp add: lens_laws_vcg_simps)?;fail

method vcg_default_goal_post_processing = 
       (pred_simp?,(unfold lens_indep_all_alt)?; (simp add: lens_laws_vcg_simps)?;safe?;clarsimp?)
   
method vcg_pp_solver methods post_processing = assumption|pred_simp?, post_processing?;fail
  
method vcg_step_solver methods solver = 
       (hoare_sp_vcg_rule | solver)
                   
method hoare_sp_vcg_step_solver = vcg_step_solver \<open>vcg_default_solver\<close>
    
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
  
definition DEFERRED :: "bool \<Rightarrow> bool" where "DEFERRED P = P"
lemma DEFERREDD: "DEFERRED P \<Longrightarrow> P" by (auto simp: DEFERRED_def)

method vcg_can_defer =
  (match conclusion 
      in "DEFERRED _" \<Rightarrow> fail  -- \<open>Refuse to defer already deferred goals\<close>
       \<bar>
         "\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>P" \<Rightarrow> fail  -- \<open>Refuse to defer Hoare triples (They are no VCs!)\<close>
       \<bar> 
         "_" \<Rightarrow> succeed)
  
method vcg_defer = (vcg_can_defer, rule DEFERREDD, tactic \<open>FIRSTGOAL defer_tac\<close>)

method  hoare_sp_vcg_step = (hoare_sp_vcg_rule | vcg_defer)
  
method  hoare_sp_vcg_steps = hoare_sp_vcg_pre, hoare_sp_vcg_step+ , (unfold DEFERRED_def)

method  hoare_sp_vcg_steps_pp = hoare_sp_vcg_steps; pred_simp?
  
method hoare_sp_default_vcg_all = (hoare_sp_vcg_pre, (hoare_sp_vcg_step_solver| vcg_defer)+, (unfold DEFERRED_def)?)(*This tactic loops because of vcg_defer*)

method hoare_sp_pp_vcg_all = (hoare_sp_default_vcg_all; vcg_default_goal_post_processing)
  
lemma increment_method: 
  assumes "vwb_lens x" "x \<bowtie> y" "vwb_lens y"
  shows  
    "\<lbrace>&y >\<^sub>u 0\<rbrace>
      x :== 0 ; 
      INVR &y >\<^sub>u 0 \<and> &y \<ge>\<^sub>u &x 
      VRT \<guillemotleft>(measure o Rep_uexpr) ((&y + 1) - &x)\<guillemotright> 
      WHILE &x <\<^sub>u &y DO x:== (&x + 1) OD
    \<lbrace>&y =\<^sub>u &x\<rbrace>\<^sub>P"
  apply (insert assms) (*Make this automatic*)
  apply (hoare_sp_pp_vcg_all)    
  done
    
subsection {* I want to see the problem of nested existential*}
  
lemma ushExE:
  assumes " \<lbrakk>\<^bold>\<exists> v \<bullet> P\<rbrakk>\<^sub>e a"
  assumes "\<And> v .  \<lbrakk>P\<rbrakk>\<^sub>e a \<Longrightarrow> Q " 
  shows Q
  using assms 
  by pred_auto

lemma ushExE':
  assumes "\<lbrakk>\<^bold>\<exists> v \<bullet> Abs_uexpr (\<lambda>st. \<lbrakk>&y\<rbrakk>\<^sub>e st = y\<^sub>0 \<and> 0 < y\<^sub>0)\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u 0\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<rbrakk>\<^sub>e a"
  assumes "\<And>v.  \<lbrakk>Abs_uexpr (\<lambda>st. \<lbrakk>&y\<rbrakk>\<^sub>e st = y\<^sub>0 \<and> 0 < y\<^sub>0)\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u 0\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrakk>\<^sub>e a \<Longrightarrow> Q " 
  shows Q
  using assms 
  by pred_auto
    
lemma even_count:
  assumes "lens_indep_all [i, start, j, endd]"
  assumes "vwb_lens x" "vwb_lens y" "vwb_lens i" "vwb_lens j"  
  shows  
    "\<lbrace>&start =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &endd =\<^sub>u 1\<rbrace>
       i :== &start;
       j :== 0 ; 
       INVR &start =\<^sub>u 0 \<and> &endd =\<^sub>u 1 \<and> &j =\<^sub>u ((&i + 1) - &start) div 2 \<and> &i \<le>\<^sub>u &endd \<and> &i \<ge>\<^sub>u &start
       VRT \<guillemotleft>measure (nat o (Rep_uexpr ((&endd + 1) - &i)))\<guillemotright>
       WHILE &i <\<^sub>u &endd
       DO
         IF &i mod 2 =\<^sub>u 0 
         THEN j :== (&j + 1)
         ELSE SKIP 
         FI;
        i :== (&i + 1)
       OD
    \<lbrace>&j =\<^sub>u 1\<rbrace>\<^sub>P"
  apply (insert assms) (*Make this automatic*) 
  supply   mod_pos_pos_trivial[simp]
  apply (hoare_sp_pp_vcg_all)
  done
    
named_theorems beautify_thms     
lemma thin_vwb_lens[beautify_thms]: "vwb_lens l \<Longrightarrow> P \<Longrightarrow> P" .   
lemma [beautify_thms]: "\<not> ief_lens i \<Longrightarrow> P \<Longrightarrow> P" .  
lemma [beautify_thms]: "i\<bowtie>j \<Longrightarrow> P \<Longrightarrow> P" .  
lemma [beautify_thms]: "i\<noteq>(j::_\<Longrightarrow>_) \<Longrightarrow> P \<Longrightarrow> P" .  
lemma [beautify_thms]: "get\<^bsub>i\<^esub> A = x \<Longrightarrow> P \<Longrightarrow> P" .  
    
lemma even_count_gen:
  assumes "lens_indep_all [i, start, j, endd]"
  assumes "vwb_lens x" "vwb_lens y" "vwb_lens i" "vwb_lens j"  
  shows  
    "\<lbrace>&start =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &endd >\<^sub>u 0 \<rbrace>
       i :== &start;
       j :== 0 ; 
       INVR &start =\<^sub>u 0 \<and>  &j =\<^sub>u ((&i + 1) - &start) div 2 \<and> &i \<le>\<^sub>u &endd \<and> &i \<ge>\<^sub>u &start
       VRT \<guillemotleft>measure (nat o (Rep_uexpr ((&endd + 1) - &i)))\<guillemotright>
       WHILE &i <\<^sub>u &endd
       DO
         IF &i mod 2 =\<^sub>u 0 
         THEN j :== (&j + 1)
         ELSE SKIP 
         FI;
        i :== (&i + 1)
       OD
    \<lbrace>&j =\<^sub>u ((&endd + 1)div 2)\<rbrace>\<^sub>P"  
  apply (insert assms) (*Make this automatic*)
  apply (hoare_sp_pp_vcg_all)
  apply (vcg_elim_determ beautify_thms)
    apply (simp add: zdiv_zadd1_eq)
  done    
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
*)  
term 
"Abs_uexpr (\<lambda> st. \<exists>a\<^sub>0 h\<^sub>0 . (Rep_uexpr (&y) st)  = a\<^sub>0  \<and> 
                           (Rep_uexpr (&h) st)  = h\<^sub>0 \<and> 
                           h\<^sub>0 = a\<^sub>0 \<and> (Rep_uexpr (&l) st) \<le> h\<^sub>0)"
term 
  "\<^bold>\<exists>(l\<^sub>0, h\<^sub>0, a\<^sub>0) \<bullet> #\<^sub>u(&a::(int list, _) uexpr) =\<^sub>u a\<^sub>0 \<and> &h =\<^sub>u h\<^sub>0 \<and> &l =\<^sub>u l\<^sub>0 \<and> l\<^sub>0 \<le>\<^sub>u h\<^sub>0"

lemma " (\<^bold>\<exists>(a\<^sub>0, h\<^sub>0) \<bullet> #\<^sub>u(&a::(int list, _) uexpr) =\<^sub>u h\<^sub>0) =
       Abs_uexpr (\<lambda> st. \<exists>a\<^sub>0 h\<^sub>0 . (Rep_uexpr (#\<^sub>u(&a::(int list, _) uexpr)) st)  = h\<^sub>0)"
apply pred_simp 
  by (metis lit.rep_eq)  
thm "lens_indepI"
lemma lens_indepE:
  assumes "x \<bowtie> y"
  assumes " \<And> v u \<sigma>. put\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> \<sigma> v) u = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> \<sigma> u) v \<Longrightarrow> 
                   get\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> \<sigma> u) = get\<^bsub>y\<^esub> \<sigma> \<Longrightarrow> 
                   get\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> \<sigma> v) = get\<^bsub>x\<^esub> \<sigma> \<Longrightarrow> Q"
  shows Q
  using assms unfolding lens_indep_def
  by auto

lemma 
  assumes "lens_indep_all [l, h, r, w]"
  assumes "a \<bowtie> l"  "a \<bowtie> h" "a \<bowtie> r" "a \<bowtie> w"
  assumes "vwb_lens a" "vwb_lens l" "vwb_lens h" "vwb_lens r" "vwb_lens w"
  shows  
 "\<lbrace>\<^bold>\<exists>(l\<^sub>0, h\<^sub>0, a\<^sub>0, r\<^sub>0, w\<^sub>0) \<bullet> (&a::(int list, _) uexpr) =\<^sub>u \<guillemotleft>a\<^sub>0\<guillemotright> \<and>  #\<^sub>u(\<guillemotleft>a\<^sub>0\<guillemotright>) =\<^sub>u \<guillemotleft>h\<^sub>0\<guillemotright> \<and>  
                          &r =\<^sub>u \<guillemotleft>r\<^sub>0\<guillemotright> \<and> &w =\<^sub>u \<guillemotleft>w\<^sub>0\<guillemotright> \<and> &l =\<^sub>u \<guillemotleft>l\<^sub>0\<guillemotright> \<and> \<guillemotleft>l\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>h\<^sub>0\<guillemotright>\<rbrace> 
      r:== &l; w :==&l;
      INVR \<^bold>\<exists>(l\<^sub>0, h\<^sub>0, a\<^sub>0 , r\<^sub>0, w\<^sub>0) \<bullet> &r =\<^sub>u \<guillemotleft>r\<^sub>0\<guillemotright> \<and> &w =\<^sub>u \<guillemotleft>w\<^sub>0\<guillemotright> \<and> &a =\<^sub>u \<guillemotleft>a\<^sub>0\<guillemotright> \<and> #\<^sub>u(\<guillemotleft>a\<^sub>0\<guillemotright>) =\<^sub>u \<guillemotleft>h\<^sub>0\<guillemotright> \<and> 
                                    \<guillemotleft>l\<^sub>0\<guillemotright>\<le>\<^sub>u\<guillemotleft>w\<^sub>0\<guillemotright> \<and>  \<guillemotleft>w\<^sub>0\<guillemotright>\<le>\<^sub>u\<guillemotleft>r\<^sub>0\<guillemotright> \<and> \<guillemotleft>r\<^sub>0\<guillemotright>\<le>\<^sub>u\<guillemotleft>h\<^sub>0\<guillemotright> \<and>
           \<guillemotleft>a\<^sub>0\<guillemotright> =\<^sub>u  \<guillemotleft>filter (\<lambda> x . 5 < x) (a\<^sub>0)\<guillemotright>
      VRT  \<guillemotleft>measure ((Rep_uexpr (&h - &r)))\<guillemotright>
      WHILE &r<\<^sub>u &h
      DO 
       IF (&a)(&r)\<^sub>a >\<^sub>u (5)
       THEN a :== (trop list_update (&a) (&r) (&a(&w)\<^sub>a)) ;
            w :== (&w + 1)
       ELSE SKIP
       FI ;
       r:== (&r+1)
      OD;
      h :==&w
     \<lbrace>\<^bold>\<exists>(l\<^sub>0, h\<^sub>0, a\<^sub>0 , r\<^sub>0, w\<^sub>0) \<bullet> &r =\<^sub>u \<guillemotleft>r\<^sub>0\<guillemotright> \<and> &w =\<^sub>u \<guillemotleft>w\<^sub>0\<guillemotright> \<and> &a =\<^sub>u \<guillemotleft>a\<^sub>0\<guillemotright> \<and> #\<^sub>u(\<guillemotleft>a\<^sub>0\<guillemotright>) =\<^sub>u \<guillemotleft>h\<^sub>0\<guillemotright> \<and>
                             \<guillemotleft>h\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>l\<^sub>0\<guillemotright> \<and>  
                             \<guillemotleft>a\<^sub>0\<guillemotright> =\<^sub>u  \<guillemotleft>filter (\<lambda> x . 5 < x) (a\<^sub>0)\<guillemotright>\<rbrace>\<^sub>P"
  apply (insert assms) (*Make this automatic*)
  apply (hoare_sp_pp_vcg_all)
oops
lemma 
  assumes "lens_indep_all [l, h, r, w]"
  assumes "a \<bowtie> l"  "a \<bowtie> h" "a \<bowtie> r" "a \<bowtie> w"
  assumes "vwb_lens a" "vwb_lens l" "vwb_lens h" "vwb_lens r" "vwb_lens w"
  shows  
 "\<lbrace> #\<^sub>u(&a) =\<^sub>u &h \<and> &l \<le>\<^sub>u &h\<rbrace> 
      r:== &l; w :==&l;
      INVR #\<^sub>u(&a) =\<^sub>u &h \<and> 
           &l \<le>\<^sub>u &w \<and> &w \<le>\<^sub>u &r \<and> &r\<le>\<^sub>u &h \<and>
           &a =\<^sub>u  bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) (&a)
      VRT  \<guillemotleft>measure ((Rep_uexpr (&h - &r)))\<guillemotright>
      WHILE &r<\<^sub>u &h
      DO 
       IF (&a)(&r)\<^sub>a >\<^sub>u (5)
       THEN a :== (trop list_update (&a) (&r) (&a(&w)\<^sub>a)) ;
            w :== (&w + 1)
       ELSE SKIP
       FI ;
       r:== (&r+1)
      OD;
      h :==&w
     \<lbrace> #\<^sub>u(&a) =\<^sub>u &h \<and> &h \<le>\<^sub>u &l \<and> &a =\<^sub>u  bop filter (\<lambda> x \<bullet> \<guillemotleft>5 < x\<guillemotright>) (&a)\<rbrace>\<^sub>P"
  apply (insert assms) (*Make this automatic*)
  apply (hoare_sp_pp_vcg_all)
  apply (tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+ done  
  oops
    ..
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