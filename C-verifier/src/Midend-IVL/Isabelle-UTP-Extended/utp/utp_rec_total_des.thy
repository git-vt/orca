(*****************************************************************************************)
(* Orca: A Functional Correctness Verifier for Imperative Programs Based on Isabelle/UTP *)
(*                                                                                       *)
(* Copyright (c) 2016-2018 Virginia Tech, USA                                            *)
(* This software may be distributed and modified according to the terms of               *)
(* the GNU Lesser General Public License version 3.0 or any later version.               *)
(* Note that NO WARRANTY is provided.                                                    *)
(* See CONTRIBUTORS, LICENSE and CITATION files for details.                             *)
(*****************************************************************************************)

theory utp_rec_total_des
  imports "../AlgebraicLaws/Algebraic_laws_design"
begin
section {*Total correctness for recursion*}
 
subsection {*AUX lemmas on healthy fixed points*}

lemma nu_design_is_healthy_des[simp]: (*This should be generated automatically in utp_theory*)
  "\<nu>\<^sub>D F is \<H>\<^bsub>DES\<^esub>"
  by (simp add: is_Hcarrier_is_hdesigns)

lemma nu_normal_design_is_healthy_des[simp]: (*This should be generated automatically in utp_theory*)
  "\<nu>\<^sub>N F is \<H>\<^bsub>NDES\<^esub>"
  by (simp add: is_Ncarrier_is_ndesigns)
  
lemma mu_design_is_healthy_des[simp]: (*This should be generated automatically in utp_theory*)
  "\<mu>\<^sub>D F is \<H>\<^bsub>DES\<^esub>"
  by (simp add: is_Hcarrier_is_hdesigns)

lemma mu_normal_design_is_healthy_des[simp]: (*This should be generated automatically in utp_theory*)
  "\<mu>\<^sub>N F is \<H>\<^bsub>NDES\<^esub>"
  by (simp add: is_Ncarrier_is_ndesigns)

lemma  design_nu_wf_refine_intro: 
  assumes   WF: "wf R"
    and      M: "Mono\<^bsub>uthy_order DES\<^esub> F"
    and      H: "F \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    and      Okey1:"$ok\<acute> \<sharp> p"
    and      Okey2:"$ok\<acute> \<sharp> e"
    and  induct_step:
    "\<And>st. ((p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> q) \<sqsubseteq> (F((p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile> q))"
  shows "(p \<turnstile> q) \<sqsubseteq> \<nu>\<^sub>D F"            
proof -   
  {
    fix st
    have "(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> q \<sqsubseteq> \<nu>\<^sub>D F" 
      using WF proof (induction rule: wf_induct_rule)
      case (less st)
      hence 0: "(p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile> q \<sqsubseteq> \<nu>\<^sub>D F"
        by rel_blast
      from M H design_theory_continuous.GFP_lemma2 mono_Monotone_utp_order
      have 1: " (\<nu>\<^sub>D F) \<sqsubseteq> F(\<nu>\<^sub>D F)"
        by blast
      from 0 1 have 2:" (p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile> q \<sqsubseteq> F (\<nu>\<^sub>D F)"
        by simp 
      have 3: "F ((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile> q) \<sqsubseteq> F (\<nu>\<^sub>D F)"
      proof (rule Mono_utp_orderD[OF M "nu_design_is_healthy_des" "design_is_healthy_DES_intro" 0], goal_cases)
        case 1
        then show ?case by (simp add: Okey1 Okey2 unrest)
      qed  
      have 4:"(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> q \<sqsubseteq> \<dots>" 
        by (rule induct_step)
      show ?case
        using order_trans[OF 3 4] Okey1 H M design_theory_continuous.GFP_lemma3 dual_order.trans mono_Monotone_utp_order 
        by blast
    qed
  }
  thus ?thesis
    by pred_simp
qed    

lemma  design_mu_wf_refine_intro: 
  assumes   WF: "wf R"
    and      M: "Mono\<^bsub>uthy_order DES\<^esub> F"
    and      H: "F \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    and      Okey1:"$ok\<acute> \<sharp> p"
    and      Okey2:"$ok\<acute> \<sharp> e"
    and  induct_step:
    "\<And>st. ((p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> q) \<sqsubseteq> (F((p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile> q))"
  shows "(p \<turnstile> q) \<sqsubseteq> \<mu>\<^sub>D  F"            
proof -   
  {
    fix st
    have "(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> q \<sqsubseteq> \<mu>\<^sub>D F" 
      using WF proof (induction rule: wf_induct_rule)
      case (less st)
      hence 0: "(p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile> q \<sqsubseteq> \<mu>\<^sub>D F"
        by rel_blast
      from M H design_theory_continuous.LFP_lemma3 mono_Monotone_utp_order
      have 1: "\<mu>\<^sub>D F \<sqsubseteq>  F (\<mu>\<^sub>D F)"
        by blast
      from 0 1 have 2:"(p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile> q \<sqsubseteq> F (\<mu>\<^sub>D F)"
        by simp
      have 3: "F ((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile> q) \<sqsubseteq> F (\<mu>\<^sub>D F)"
      proof (rule Mono_utp_orderD[OF M "mu_design_is_healthy_des" "design_is_healthy_DES_intro" 0], goal_cases)
        case 1
        then show ?case by (simp add: Okey2 Okey1 unrest)
      qed  
      have 4:"(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile> q \<sqsubseteq> \<dots>" 
        by (rule induct_step)
      show ?case
        using order_trans[OF 3 4] Okey1 H M design_theory_continuous.LFP_lemma2 dual_order.trans mono_Monotone_utp_order 
        by blast
    qed
  }
  thus ?thesis
    by pred_simp
qed    

  
lemma rdesign_nu_wf_refine_intro: 
  assumes   WF: "wf R"
    and      M: "Mono\<^bsub>uthy_order DES\<^esub> F"
    and      H: "F \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    and  induct_step:
    "\<And>st. ((p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r q) \<sqsubseteq> (F ((p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r q))"
  shows "(p \<turnstile>\<^sub>r q) \<sqsubseteq> \<nu>\<^sub>D F"            
proof -          
  {
  fix st
  have "(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r q \<sqsubseteq> \<nu>\<^sub>D F" 
    using WF proof (induction rule: wf_induct_rule)
    case (less st)
    hence 0: "(p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r q \<sqsubseteq> \<nu>\<^sub>D F"
      by rel_blast
    from M H design_theory_continuous.GFP_lemma2 mono_Monotone_utp_order
    have 1: "\<nu>\<^sub>D F \<sqsubseteq>  F (\<nu>\<^sub>D F)"
      by blast
    from 0 1 have 2:"(p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r q \<sqsubseteq> F (\<nu>\<^sub>D F)"
      by simp
    have 3: "F ((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r q) \<sqsubseteq> F (\<nu>\<^sub>D F)"
      by (auto intro: Mono_utp_orderD M 0)
    have 4:"(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r q \<sqsubseteq> \<dots>" 
      by (rule induct_step)
    show ?case
      using order_trans[OF 3 4] H M design_theory_continuous.GFP_lemma3 dual_order.trans mono_Monotone_utp_order 
      by blast
  qed
  }
  thus ?thesis
    by pred_simp
qed    
  
lemma rdesign_mu_wf_refine_intro: 
  assumes   WF: "wf R"
    and      M: "Mono\<^bsub>uthy_order DES\<^esub> F"
    and      H: "F \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    and  induct_step:
    "\<And>st. ((p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r q) \<sqsubseteq> (F ((p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r q))"
  shows "(p \<turnstile>\<^sub>r q) \<sqsubseteq> \<mu>\<^sub>D F"            
proof -          
  {
  fix st
  have "(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r q \<sqsubseteq> \<mu>\<^sub>D F" 
    using WF proof (induction rule: wf_induct_rule)
    case (less st)
    hence 0: "(p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r q \<sqsubseteq> \<mu>\<^sub>D F"
      by rel_blast
    from M H design_theory_continuous.LFP_lemma3 mono_Monotone_utp_order
    have 1: "\<mu>\<^sub>D F \<sqsubseteq>  F (\<mu>\<^sub>D F)"
      by blast
    from 0 1 have 2:"(p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r q \<sqsubseteq> F (\<mu>\<^sub>D F)"
      by simp
    have 3: "F ((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>r q) \<sqsubseteq> F (\<mu>\<^sub>D F)"
      by (auto intro: Mono_utp_orderD M 0)
    have 4:"(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>r q \<sqsubseteq> \<dots>" 
      by (rule induct_step)
    show ?case
      using order_trans[OF 3 4] H M design_theory_continuous.LFP_lemma2 dual_order.trans mono_Monotone_utp_order 
      by blast
  qed
  }
  thus ?thesis
    by pred_simp
qed    
  
   
lemma ndesign_nu_wf_refine_intro: 
  assumes   WF: "wf R"
    and      M: "Mono\<^bsub>uthy_order NDES\<^esub> F"
    and      H: "F \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
    and  induct_step:
    "\<And>st. ((p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n q) \<sqsubseteq> (F ((p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n q))"
  shows "(p \<turnstile>\<^sub>n q) \<sqsubseteq> \<nu>\<^sub>N F"            
proof -          
  {
  fix st
  have "(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n q \<sqsubseteq> \<nu>\<^sub>N F" 
    using WF proof (induction rule: wf_induct_rule)
    case (less st)
    hence 0: "(p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n q \<sqsubseteq> \<nu>\<^sub>N F"
      by rel_blast
    from M H normal_design_theory_continuous.GFP_lemma2 mono_Monotone_utp_order
    have 1: "\<nu>\<^sub>N F \<sqsubseteq>  F (\<nu>\<^sub>N F)"
      by blast
    from 0 1 have 2:"(p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n q \<sqsubseteq> F (\<nu>\<^sub>N F)"
      by simp
    have 3: "F((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n q) \<sqsubseteq> F (\<nu>\<^sub>N F)"
      by (auto intro: Mono_utp_orderD M 0)
    have 4:"(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n q \<sqsubseteq> \<dots>" 
      by (rule induct_step)
    show ?case
      using order_trans[OF 3 4] H M normal_design_theory_continuous.GFP_lemma3 dual_order.trans mono_Monotone_utp_order 
      by blast
  qed
  }
  thus ?thesis
    by pred_simp
qed  
  
lemma ndesign_mu_wf_refine_intro: 
  assumes   WF: "wf R"
    and      M: "Mono\<^bsub>uthy_order NDES\<^esub> F"
    and      H: "F \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
    and  induct_step:
    "\<And>st. ((p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n q) \<sqsubseteq> (F ((p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n q))"
  shows "(p \<turnstile>\<^sub>n q) \<sqsubseteq> \<mu>\<^sub>N F"            
proof -          
  {
  fix st
  have "(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n q \<sqsubseteq> \<mu>\<^sub>N F" 
    using WF proof (induction rule: wf_induct_rule)
    case (less st)
    hence 0: "(p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n q \<sqsubseteq> \<mu>\<^sub>N F"
      by rel_blast
    from M H normal_design_theory_continuous.LFP_lemma3 mono_Monotone_utp_order
    have 1: "\<mu>\<^sub>N F \<sqsubseteq>  F (\<mu>\<^sub>N F)"
      by blast
    from 0 1 have 2:"(p \<and> (e,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n q \<sqsubseteq> F (\<mu>\<^sub>N F)"
      by simp
    have 3: "F((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n q) \<sqsubseteq> F (\<mu>\<^sub>N F)"
      by (auto intro: Mono_utp_orderD M 0)
    have 4:"(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n q \<sqsubseteq> \<dots>" 
      by (rule induct_step)
    show ?case
      using order_trans[OF 3 4] H M normal_design_theory_continuous.LFP_lemma2 dual_order.trans mono_Monotone_utp_order 
      by blast
  qed
  }
  thus ?thesis
    by pred_simp
qed  
end

