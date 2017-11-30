theory utp_hoare_ndes_prog

imports "../../../AlgebraicLaws/IMP_Prog/algebraic_laws_prog"

begin
section {*Hoare logic for programs*}  
named_theorems hoare_prog

subsection {*Hoare triple definition*}

lift_definition hoare :: "'\<alpha> cond \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>P") 
 is  hoare_d .

declare hoare.rep_eq [prog_rep_eq]

lemma hoare_true_assisgns_p_t[hoare_prog]: 
  "\<lbrace>p\<rbrace> \<langle>\<sigma>\<rangle>\<^sub>p \<lbrace>true\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma hoare_true_skip_p_t [hoare_prog]: 
  "\<lbrace>p\<rbrace>skip\<lbrace>true\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma hoare_false_p_t [hoare_prog]: 
  "\<lbrace>false\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

subsection {*Precondition weakening*}

lemma hoare_pre_str_p_t[hoare_prog]:
  assumes "`p\<^sub>1 \<Rightarrow> p\<^sub>2`" and "\<lbrace>p\<^sub>2\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<^sub>1\<rbrace>C\<lbrace>q\<rbrace>\<^sub>P" 
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Post-condition strengthening*}

lemma hoare_post_weak_p_t[hoare_prog]:
  assumes "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>2\<rbrace>\<^sub>P" and "`q\<^sub>2 \<Rightarrow> q\<^sub>1`"
  shows "\<lbrace>p\<rbrace>C\<lbrace>q\<^sub>1\<rbrace>\<^sub>P" 
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Hoare and assertion logic*}

lemma hoare_prog_conj_p_t [hoare_prog]: 
  assumes"\<lbrace>p\<rbrace>C\<lbrace>r\<rbrace>\<^sub>P" and "\<lbrace>p\<rbrace>C\<lbrace>s\<rbrace>\<^sub>P"
  shows "\<lbrace>p\<rbrace>C\<lbrace>r \<and> s\<rbrace>\<^sub>P"
  using assms  
  by (simp add: prog_rep_eq hoare_des)

subsection {*Hoare SKIP*}

lemma skip_p_hoare_p_t [hoare_prog]: 
  "\<lbrace>p\<rbrace>SKIP\<lbrace>p\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

subsection {*Hoare for assignment*}

lemma assigns_p_hoare_p_t [hoare_prog]: 
  assumes"`p \<Rightarrow> \<sigma> \<dagger> q`" 
  shows  "\<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>p\<lbrace>q\<rbrace>\<^sub>P"
  using assms  
  by (simp add: prog_rep_eq hoare_des)

lemma assigns_p_hoare_p'_t [hoare_prog]: 
  "\<lbrace>\<sigma> \<dagger> p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>p\<lbrace>p\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq hoare_des)

lemma assigns_p_floyd_p_t [hoare_prog]:
  \<open>\<lbrace>\<guillemotleft>vwb_lens x\<guillemotright>\<and> p\<rbrace>x :== e\<lbrace>\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<rbrace>\<^sub>P\<close>
  by (simp add: prog_rep_eq hoare_des)

subsection {*Hoare for Sequential Composition*}

lemma seq_hoare_p_t [hoare_prog]: 
  assumes"\<lbrace>p\<rbrace>C\<^sub>1\<lbrace>s\<rbrace>\<^sub>P" and "\<lbrace>s\<rbrace>C\<^sub>2\<lbrace>r\<rbrace>\<^sub>P" 
  shows"\<lbrace>p\<rbrace>C\<^sub>1 ; C\<^sub>2\<lbrace>r\<rbrace>\<^sub>P"
  using assms
  by (simp add: prog_rep_eq hoare_des)  

subsection {*Hoare for Conditional*}

lemma cond_p_hoare_p_t [hoare_prog]: 
  assumes "\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>P" and "\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>q\<rbrace>\<^sub>P" 
  shows "\<lbrace>p\<rbrace>IF b THEN C\<^sub>1 ELSE C\<^sub>2 FI\<lbrace>q\<rbrace>\<^sub>P"
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
   
lemma mu_p_rec_hoare_p_t [hoare_prog]:
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
    
lemma mu_p_rec_hoare_p_t' [hoare_prog]:
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<And> st P. \<lbrace>Pre \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace> P \<lbrace>Post\<rbrace>\<^sub>P \<Longrightarrow> \<lbrace>Pre \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> F P \<lbrace>Post\<rbrace>\<^sub>P" 
  assumes I0: "`Pre' \<Rightarrow> Pre`"  
  shows "\<lbrace>Pre'\<rbrace>\<mu>\<^sub>p F \<lbrace>Post\<rbrace>\<^sub>P"
  by (simp add: hoare_pre_str_p_t[OF I0 mu_p_rec_hoare_p_t[OF WF M induct_step]])

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
  by (smt assms(1) assms(2) assms(3) lens_get_put_quasi_commute lens_put_of_quotient mwb_lens.put_put vwb_lens.put_eq vwb_lens_mwb)
 oops a pply (smt lens.surjective mwb_lens.put_put vwb_lens_mwb vwb_lens_wb wb_lens.get_put)
  done
    
subsection {*Hoare for while iteration*}   

lemma while_invr_hoare_p_t [hoare_prog]:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`" 
  assumes induct_step:"\<And>e. \<lbrace>b \<and> I \<and> E =\<^sub>u \<guillemotleft>e\<guillemotright>\<rbrace> body \<lbrace>I \<and>(E,\<guillemotleft>e\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"  
  assumes PHI:"`(\<not> b \<and> I) \<Rightarrow> Post`"  
  shows "\<lbrace>Pre\<rbrace>INVR I WHILE b DO body OD \<lbrace>Post\<rbrace>\<^sub>P"
  unfolding pwhile_inv_prog_def
  by (simp add: prog_rep_eq while_hoare_ndesign_t[unfolded While_inv_ndes_def, OF WF I0  Rep_prog_H1_H3_closed[THEN H1_H3_impl_H2, THEN H1_H2_impl_H1] induct_step[unfolded prog_rep_eq] PHI])

lemma while_invr_vrt_hoare_p_t [hoare_des]:
  assumes WF: "wf R"
  assumes I0: "`Pre \<Rightarrow> I`"
  assumes induct_step:"\<And> st. \<lbrace>b \<and> I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>I \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>P"  
  assumes PHI:"`(\<not> b \<and> I) \<Rightarrow> Post`"  
  shows "\<lbrace>Pre\<rbrace>INVR I VRT \<guillemotleft>R\<guillemotright>  WHILE b DO body OD\<lbrace>Post\<rbrace>\<^sub>P"
  by (simp add: prog_rep_eq while_hoare_ndesign_t[unfolded While_inv_ndes_def, OF WF I0  Rep_prog_H1_H3_closed[THEN H1_H3_impl_H2, THEN H1_H2_impl_H1] induct_step[unfolded prog_rep_eq] PHI])

lemma while_invr_vrt_hoare_p_t' [hoare_des]:
  assumes WF: "`uop wf R`"
  assumes I0: "`Pre \<Rightarrow> I`"
  assumes induct_step:"\<And> st. \<lbrace>b \<and> I \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace> body \<lbrace>I \<and>(E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>uR\<rbrace>\<^sub>P"  
  assumes PHI:"`(\<not> b \<and> I) \<Rightarrow> Post`"  
  shows "\<lbrace>Pre\<rbrace>INVR I VRT R WHILE b DO body OD\<lbrace>Post\<rbrace>\<^sub>P"
  unfolding pwhile_inv_vrt_prog_def
  apply (simp add: prog_rep_eq)
  unfolding  hoare_d_def While_lfp_ndes_def
  apply (rule ndesign_mu_wf_refine_intro[OF _ mono_Monotone_utp_order[OF if_d_mono, of "\<H>\<^bsub>NDES\<^esub>" b ]])
  using WF apply rel_blast 

  by (simp add: prog_rep_eq while_hoare_ndesign_t[unfolded While_inv_ndes_def, OF WF I0  Rep_prog_H1_H3_closed[THEN H1_H3_impl_H2, THEN H1_H2_impl_H1] induct_step[unfolded prog_rep_eq] PHI])

term "`uop wf R`"    
section {*VCG*} 
lemma increment_method: 
 "\<lbrace>\<guillemotleft>vwb_lens x\<guillemotright> \<and> \<guillemotleft>vwb_lens y\<guillemotright> \<and>&y >\<^sub>u 0\<rbrace>
    x :== 0 ; 
    INVR &y >\<^sub>u 0 \<and> &y \<ge>\<^sub>u &x 
    VRT uop measure (\<lambda>_ \<bullet> (&y + 1) - &x) 
    WHILE &x <\<^sub>u &y DO x:== (&x + 1) OD
  \<lbrace>&y =\<^sub>u &x\<rbrace>\<^sub>P"
  apply (rule hoare_post_weak_p_t)
   apply (rule seq_hoare_p_t)
    apply (rule assigns_p_floyd_p_t)
oops
find_theorems name:"H1_H2_impl_"    

end