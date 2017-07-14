subsection {* Relational Hoare calculus *}

theory utp_hoare_helper
imports utp_hoare_total 
begin
named_theorems utp_hoare_hp

(********************
 ********************)
  subsection"Throw"
(*******************
 *******************)

lemma throw_cpa_left_zero_true_abr [utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R ;; true\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>true\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  by rel_auto 

lemma throw_cpa_left_zero_true_lift_abr [utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R ;; \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  by rel_auto 

lemma throw_cpa_left_zero_false [utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R ;; false\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>false\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  by rel_auto 

lemma throw_cpa_left_zero_false_lift_abr [utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R ;; \<lceil>false\<rceil>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>\<lceil>false\<rceil>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  by rel_auto 

lemma throw_cpa_left_zero_skip_abr [utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R ;;  SKIP\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  apply pred_simp 
  apply rel_simp 
  apply auto 
  apply metis 
done

lemma throw_cpa_left_zero_assigns_abr[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R ;; \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  apply pred_simp 
  apply rel_simp 
  apply auto 
  apply metis 
done

lemma throw_cpa_left_zero_top_abr[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R ;; \<top>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>\<top>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  by rel_simp 
  
lemma not_abrupt_left_zero_throw_abr[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>($x) ;; THROW\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>($x)\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  apply pred_simp 
  apply rel_simp 
  apply auto 
  apply metis+
done

lemma bot_left_zero_throw_abr[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>\<top>\<^sub>A\<^sub>B\<^sub>R ;; THROW\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>\<top>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  by pred_simp 
  
lemma throw_abr_idem[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R ;; THROW\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  apply pred_simp 
  apply rel_simp 
  apply auto 
  apply metis
done

lemma throw_abr_right_zero_skip_abr[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R ;; THROW\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  apply pred_simp 
  apply rel_simp 
  apply auto 
  apply metis
done

subsection"Skip"

text{*In this section we introduce the algebraic laws of programming related to the SKIP
      statement.*}
 
lemma true_left_zero_skip_cpa_abr[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R ;; true\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>true\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  apply pred_simp 
  apply rel_simp 
  apply auto 
  apply metis+
done
 
lemma true_lift_abr_left_zero_skip_abr[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R ;; \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  apply pred_simp 
  apply rel_simp 
  apply auto 
  apply metis+
done

lemma false_left_zero_skip_abr[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R ;; false\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>false\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  by pred_simp 

lemma false_lift_abr_left_zero_skip_abr[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R ;; \<lceil>false\<rceil>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>\<lceil>false\<rceil>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  by pred_simp 


lemma skip_abr_left_unit_assigns_abr[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R ;; \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  apply pred_simp 
  apply rel_simp 
  apply auto 
  apply smt
done

lemma skip_abr_top_abr_left_zero[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R ;; \<top>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>\<top>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  by rel_simp 

lemma skip_abr_ivar_left_zero[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>$x ;; SKIP\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>$x\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  apply pred_simp 
  apply rel_simp 
  apply auto 
  apply metis+
done

lemma skip_abr_top_left_zero[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>\<top>\<^sub>A\<^sub>B\<^sub>R ;; SKIP\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>\<top>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  by pred_simp 

lemma skip_abr_idem[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R ;; SKIP\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  apply pred_simp 
  apply rel_simp 
  apply auto 
  apply smt
done

lemma skip_abr_post_left_unit[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>S \<turnstile> (SKIP\<^sub>A\<^sub>B\<^sub>R;; Q)\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>S \<turnstile> Q\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  apply pred_simp 
  apply rel_simp 
  apply auto 
  apply metis+
done

subsection {*Assignment Laws*}
text{*In this section we introduce the algebraic laws of programming related to the assignment
      statement.*}

lemma design_post_not_abrupt_cond_cancel[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>S \<turnstile> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>R\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and> $abrupt\<acute>) ;; P \<triangleleft> \<not> $abrupt \<triangleright> Q)\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace> S \<turnstile> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>R\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and> $abrupt\<acute>);; Q)\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  apply pred_simp
  apply (smt des_vars.select_convs(1) fst_conv mem_Collect_eq relcomp.intros relcomp.simps snd_conv) 
done

lemma design_post_abrupt_cond_cancel[utp_hoare_hp]: 
  "\<lbrace>p\<rbrace>S \<turnstile> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>R\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and>  $abrupt\<acute>) ;; P \<triangleleft> $abrupt \<triangleright> Q)\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace>S \<turnstile> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<lceil>R\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and>  $abrupt\<acute>);; P)\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  apply pred_simp
  apply (smt des_vars.select_convs(1) fst_conv mem_Collect_eq relcomp.intros relcomp.simps snd_conv) 
done

lemma usubst_abr_cancel[utp_hoare_hp]: 
  "\<lbrace>\<guillemotleft>weak_lens v\<guillemotright>\<rbrace>($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub></$v\<rbrakk>\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>\<guillemotleft>weak_lens v\<guillemotright>\<rbrace>\<lceil>expr\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  by rel_auto 
 
lemma usubst_abr_cancel_str[utp_hoare_hp]: 
  assumes "`p \<Rightarrow> \<guillemotleft>weak_lens v\<guillemotright>`"
  shows "\<lbrace>p\<rbrace>($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub></$v\<rbrakk>\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
         \<lbrace>p\<rbrace>\<lceil>expr\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  using assms
  by rel_auto metis+ 


lemma usubst_abr_lift_cancel[utp_hoare_hp]: 
  "\<lbrace>\<guillemotleft>weak_lens v\<guillemotright>\<rbrace>\<lceil>($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub></$v\<rbrakk>\<rceil>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>\<guillemotleft>weak_lens v\<guillemotright>\<rbrace>\<lceil>expr\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  by rel_auto 

lemma usubst_abr_lift_cancel_str[utp_hoare_hp]: 
  assumes "`p \<Rightarrow> \<guillemotleft>weak_lens v\<guillemotright>`"
  shows "\<lbrace>p\<rbrace>\<lceil>($v)\<lbrakk>\<lceil>expr\<rceil>\<^sub></$v\<rbrakk>\<rceil>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
         \<lbrace>p\<rbrace>\<lceil>expr\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R "
  using assms
  by rel_auto metis+ 

subsection {*Try Catch Laws*}
text{*In this section we introduce the algebraic laws of programming related to the assignment
      statement.*}


lemma try_catch_unfold_hoare: (*because seq is assoc*)
  "\<lbrace>p\<rbrace>try  R ;; P catch  Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace>R ;; try  P catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
   apply pred_simp
   apply rel_simp
   apply auto
   apply smt+
done

lemma try_catch_abr_fold_hoare[utp_hoare_hp]: (*because seq is assoc*)
  "\<lbrace>p\<rbrace>R ;; try  P catch Q end \<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace>try  R ;; P catch  Q end \<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
   apply pred_simp
   apply rel_simp
   apply auto
   apply smt+
done

lemma try_catch_abr_throw_abr_hoare [utp_hoare_hp]:
  "\<lbrace>p\<rbrace> try THROW\<^sub>A\<^sub>B\<^sub>R  catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace> Q \<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
   apply pred_simp
   apply rel_simp
   apply auto
   apply smt+
done

lemma try_catch_abr_skip_abr_hoare [utp_hoare_hp]:
  "\<lbrace>p\<rbrace>try  SKIP\<^sub>A\<^sub>B\<^sub>R catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
   apply pred_simp
   apply rel_simp
   apply auto
   apply smt
done

lemma try_catch_abr_assigns_abr_hoare [utp_hoare_hp]:
  "\<lbrace>p\<rbrace>try   \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace> \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
   apply pred_simp
   apply rel_simp
   apply auto
   apply smt+
done

lemma
  "\<lbrace>p\<rbrace> try THROW\<^sub>A\<^sub>B\<^sub>R ;; SKIP\<^sub>A\<^sub>B\<^sub>R catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>Q \<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
   by (simp only: utp_hoare_hp  uabr_comp)

lemma 
  "\<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R ;; try \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace>Q \<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by (simp only: utp_hoare_hp  uabr_comp)


lemma
  "\<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R ;; try Simpl\<^sub>A\<^sub>B\<^sub>R P catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R =  \<lbrace>p\<rbrace>Q \<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by (simp only: utp_hoare_hp  uabr_comp)


lemma 
  "\<lbrace>p\<rbrace> try THROW\<^sub>A\<^sub>B\<^sub>R;; Simpl\<^sub>A\<^sub>B\<^sub>R P catch Simpl\<^sub>A\<^sub>B\<^sub>R Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace>Simpl\<^sub>A\<^sub>B\<^sub>R Q \<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
   by (simp only: utp_hoare_hp  uabr_comp)

   
lemma 
  "\<lbrace>p\<rbrace>try  SKIP\<^sub>A\<^sub>B\<^sub>R catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by (simp only: utp_hoare_hp  uabr_comp)

lemma [utp_hoare_hp]:
  "\<lbrace>p\<rbrace>try  THROW\<^sub>A\<^sub>B\<^sub>R catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace> Q\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by (simp only: utp_hoare_hp  uabr_comp)


end