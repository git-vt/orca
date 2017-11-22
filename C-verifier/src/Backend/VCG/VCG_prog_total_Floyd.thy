section \<open>VCG for total correctness using Floyd assignment\<close>

theory VCG_prog_total_Floyd                                           
  imports "../../Midend-IVL/Isabelle-UTP-Extended/hoare/HoareLogic/TotalCorrectness/IMP_Prog/utp_hoare_ndes_prog"
begin


named_theorems hoare_rules

lemma assert_hoare_p'[hoare_rules]:
  assumes \<open>`p \<Rightarrow> c`\<close>
  shows \<open>\<lbrace>p\<rbrace>c\<^sub>\<bottom>\<^sub>P\<lbrace>p \<and> c\<rbrace>\<^sub>P\<close>
  using assms unfolding assert_des_def
  by (metis cond_p_hoare_p_t hoare_false_p_t refBy_order skip_p_hoare_p_t 
            utp_pred_laws.inf.orderE utp_pred_laws.inf_commute 
            utp_pred_laws.inf_compl_bot_left1)
    
lemma assume_hoare_p'[hoare_rules]:
  \<open>\<lbrace>p\<rbrace>c\<^sup>\<top>\<^sup>P\<lbrace>p \<and> c\<rbrace>\<^sub>P\<close>
   unfolding prog_rep_eq
   by rel_simp
     
lemma cond_p_hoare_p':
  assumes \<open>\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>P\<close> and \<open>\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>s\<rbrace>\<^sub>P\<close>
  shows \<open>\<lbrace>p\<rbrace>IF b THEN C\<^sub>1 ELSE C\<^sub>2 FI\<lbrace>q \<or> s\<rbrace>\<^sub>P\<close>
  using assms unfolding prog_rep_eq  
  by rel_blast

lemma cond_p_assert_p_hoare_p[hoare_rules]: (* Needs some heuristics *)
  assumes \<open>\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>P\<close>
      and \<open>\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>s\<rbrace>\<^sub>P\<close>
      and \<open>`q \<Rightarrow> A`\<close>
      and \<open>`s \<Rightarrow> A`\<close>
      and \<open>\<lbrace>A\<rbrace>P\<lbrace>A'\<rbrace>\<^sub>P\<close>
    shows \<open>\<lbrace>p\<rbrace>IF b THEN C\<^sub>1 ELSE C\<^sub>2 FI; ((A\<^sub>\<bottom>\<^sub>P);  P)\<lbrace>A'\<rbrace>\<^sub>P\<close>
  apply (insert assms)
  apply (rule hoare_post_weak_p_t) 
   apply (rule cond_p_hoare_p' seq_hoare_p_t|assumption)
    apply (rule cond_p_hoare_p' seq_hoare_p_t|assumption)
     apply assumption
    apply assumption
    apply (rule seq_hoare_p_t)
      apply (rule assert_hoare_p')
  using impl_disjI apply blast
   apply (rule hoare_pre_str_p_t[where p\<^sub>2 = A])
   apply (simp add: disj_comm impl_alt_def)
    apply assumption
  apply pred_simp
  done
    
lemma "\<lbrace>P\<rbrace>ABORT\<lbrace>P\<rbrace>\<^sub>P"     
oops
    
lemma cond_p_assert_p_last_hoare_p[hoare_rules]:
  assumes \<open>\<lbrace>b \<and> p\<rbrace>C\<^sub>1\<lbrace>q\<rbrace>\<^sub>P\<close>
      and \<open>\<lbrace>\<not>b \<and> p\<rbrace>C\<^sub>2\<lbrace>s\<rbrace>\<^sub>P\<close>
      and \<open>`q \<Rightarrow> A`\<close>
      and \<open>`s \<Rightarrow> A`\<close>
    shows \<open>\<lbrace>p\<rbrace>IF b THEN C\<^sub>1 ELSE C\<^sub>2 FI; (A\<^sub>\<bottom>\<^sub>P) \<lbrace>A\<rbrace>\<^sub>P\<close>                  
 apply (insert assms)
  apply (rule hoare_post_weak_p_t)
   apply (rule cond_p_hoare_p' seq_hoare_p_t|assumption)+
    apply (rule skip_p_hoare_p_t)
   apply (simp add: prog_rep_eq)
   apply rel_auto+
  done

lemma while_invr_hoare_d'[hoare_rules]:
  assumes   WF:\<open>wf R\<close> 
      and   I0:\<open>`Pre \<Rightarrow> I`\<close> 
      and step:\<open>\<And>st .\<lbrace>b \<and> I \<and>  E =\<^sub>u \<guillemotleft>st\<guillemotright>\<rbrace>body\<lbrace>I \<and> (E,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>\<^sub>D\<close> 
      and   BH:"body is \<^bold>H"
    shows \<open>\<lbrace>Pre\<rbrace>while b invr I do body od\<lbrace>\<not>b \<and> I\<rbrace>\<^sub>D\<close>  
 proof -
  have M: "mono (\<lambda>X. bif\<^sub>D b then body ;; X else SKIP\<^sub>D eif)"
    by (auto intro: monoI seqr_mono cond_mono) 
  have H: "(\<lambda>X. bif\<^sub>D b then body ;; X else SKIP\<^sub>D eif) \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H" 
    using BH
    apply pred_simp apply rel_simp  apply smt done   
  from mono_Monotone_utp_order [OF M, of "\<H>\<^bsub>DES\<^esub>"] H
          design_theory_continuous.LFP_weak_unfold  
  have M_des: "Mono\<^bsub>uthy_order DES\<^esub>(\<lambda>X. bif\<^sub>D b then body ;; X else SKIP\<^sub>D eif)"
    by auto
  show ?thesis    
  unfolding  hoare_d_def While_inv_des_def While_lfp_des_def
   apply (rule hoare_pre_str_d_t[unfolded hoare_d_def ,of _ "I" ])
  using I0 
   apply pred_simp
    apply (rule rec_total_utp_des_rule[where Pre="\<lceil>I\<rceil>\<^sub>D\<^sub><" and E = "E", OF WF ])  
      apply (simp add: M_des)
     apply (simp add: H)
    apply pred_simp
   apply pred_simp
  apply (rule  cond_refine_des)
    subgoal for st
      apply (rule_tac seq_refine_unrest_des[where s= "I \<and> (E,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>" ])
            apply pred_simp
        apply pred_simp 
        using step[unfolded hoare_d_def, of st] apply pred_simp 
        apply pred_simp
      done
     apply (rule skip_refine_des)      
       apply rel_blast
  done 
qed      
(*lemma while_invr_hoare_r'[hoare_rules]:
  assumes \<open>`pre \<Rightarrow> p`\<close> and \<open>\<lbrace>p \<and> b\<rbrace>C\<lbrace>p'\<rbrace>\<^sub>u\<close> and \<open>`p' \<Rightarrow> p`\<close>
  shows \<open>\<lbrace>pre\<rbrace>while b invr p do C od\<lbrace>\<not>b \<and> p\<rbrace>\<^sub>u\<close>
  by (metis while_inv_def assms hoare_post_weak hoare_pre_str while_hoare_r)

lemma nu_refine_intro[hoare_rules]:
  assumes \<open>(C \<Rightarrow> S) \<sqsubseteq> F(C \<Rightarrow> S)\<close>
  shows \<open>(C \<Rightarrow> S) \<sqsubseteq> \<nu> F\<close>
  using assms
  by (simp add: lfp_lowerbound)

lemma nu_hoare_basic_r[hoare_rules]:
  assumes \<open>\<And>p. \<lbrace>P\<rbrace>p\<lbrace>Q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>P\<rbrace>F p\<lbrace>Q\<rbrace>\<^sub>u\<close>
  shows \<open>\<lbrace>P\<rbrace>\<nu> F\<lbrace>Q\<rbrace>\<^sub>u\<close>
  using assms unfolding hoare_r_def
  by (rule nu_refine_intro) auto
*)
  
lemma mu_deshoare_basic_r[hoare_rules]:
  assumes WF:"wf R"
  assumes M:"Mono\<^bsub>uthy_order DES\<^esub> F"
  assumes H:"F \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"  
  assumes step:\<open>\<And>p st. \<lbrace>P \<and> (E, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>\<rbrace>p\<lbrace>Q\<rbrace>\<^sub>D \<Longrightarrow> \<lbrace>P \<and> E =\<^sub>u \<guillemotleft>st\<guillemotright> \<rbrace>F p\<lbrace>Q\<rbrace>\<^sub>D\<close>
  shows \<open>\<lbrace>P\<rbrace>\<mu>\<^sub>D F\<lbrace>Q\<rbrace>\<^sub>D\<close>
  unfolding hoare_d_def
    thm rec_total_utp_des_rule
    apply (rule rec_total_utp_des_rule[of _ _ _ _ "E", OF WF M H])
      apply pred_simp
     apply pred_simp
    subgoal for st
    using step[of st]  
  by (rule rec_total_utp_des_rule) auto

definition annot_rec ::
  \<open>'a upred \<Rightarrow> 'a upred \<Rightarrow> ((bool, 'a) hexpr \<Rightarrow> (bool, 'a) hexpr) \<Rightarrow> (bool, 'a) hexpr\<close> where
  \<open>annot_rec P Q F \<equiv> \<nu> F\<close>

syntax
  "_nu_annot" :: \<open>pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic\<close> ("\<nu> _ [_\<Rightarrow>_] \<bullet> _" [0, 10] 10)

translations
  "\<nu> X [P\<Rightarrow>Q] \<bullet> p" == "CONST annot_rec P Q (\<lambda> X. p)"

lemma nu_hoare_r(* [hoare_rules] *):
  assumes PRE: \<open>`P' \<Rightarrow> P`\<close>
  assumes IH: \<open>\<And>p. \<lbrace>P\<rbrace>p\<lbrace>Q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>P\<rbrace>F p\<lbrace>Q\<rbrace>\<^sub>u\<close>
  shows \<open>\<lbrace>P'\<rbrace>\<nu> F\<lbrace>Q\<rbrace>\<^sub>u\<close>
  apply (rule hoare_pre_str[OF PRE])
  using IH
  unfolding hoare_r_def
  by (rule nu_refine_intro) (rule order_refl)

lemma nu_hoare_annot_r[hoare_rules]:
  assumes PRE: \<open>`P' \<Rightarrow> P`\<close>
  assumes IH: \<open>\<And>p. \<lbrace>P\<rbrace>p\<lbrace>Q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>P\<rbrace>F p\<lbrace>Q\<rbrace>\<^sub>u\<close>
  shows \<open>\<lbrace>P'\<rbrace>annot_rec P Q F\<lbrace>Q\<rbrace>\<^sub>u\<close>
  using nu_hoare_r assms unfolding annot_rec_def .

lemmas [hoare_rules] =
  cond_hoare_r' \<comment> \<open>Needs to come after annotated cond check\<close>
  assigns_floyd_r
  skip_hoare_r
  seq_hoare_r

named_theorems vcg_simps
lemmas [vcg_simps] =
  lens_indep.lens_put_irr1
  lens_indep.lens_put_irr2
  lens_indep_all_alt

named_theorems hoare_rules_extra and vcg_dests

method exp_vcg_pre = (simp only: seqr_assoc[symmetric])?, rule hoare_post_weak
method solve_dests = safe?; simp?; drule vcg_dests; assumption?; (simp add: vcg_simps)?
method solve_vcg = assumption|pred_simp?, (simp add: vcg_simps)?;(solve_dests; fail)?
method exp_vcg_step = rule hoare_rules_extra|rule hoare_rules|solve_vcg; fail
method exp_vcg = exp_vcg_pre, exp_vcg_step+

end
