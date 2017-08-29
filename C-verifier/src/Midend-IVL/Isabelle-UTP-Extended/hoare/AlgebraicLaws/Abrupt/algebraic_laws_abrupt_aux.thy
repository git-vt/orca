section \<open>Auxiliary algebraic laws for abrupt designs\<close>

theory algebraic_laws_abrupt_aux
  imports "../../../theories/Abrupt/utp_abrupt_designs"
begin

named_theorems uabr_simpl and uabr_cond and uabr_comp and uabr_lens

subsection \<open>THM setup\<close>

declare design_condr[urel_cond]

subsection \<open>abrupt alphabet behavior\<close>

lemma assigns_abr_alpha:
  "(abrupt :== (\<not> &abrupt)) = (\<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and>  $abrupt\<acute> =\<^sub>u (\<not>$abrupt) \<and> $ok =\<^sub>u $ok\<acute>)"
  "(ok :== (\<not> &ok)) = (\<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and>  $abrupt\<acute> =\<^sub>u $abrupt \<and> $ok =\<^sub>u (\<not>$ok\<acute>))"
  by rel_auto+

lemma vwb_of_abrupt[simp]:
  "vwb_lens ok" "vwb_lens abrupt"
  by simp_all

lemma unrest_pre_out\<alpha>_abr[unrest]: "out\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><"
  by (transfer, auto simp add: out\<alpha>_def lens_prod_def)

lemma unrest_post_in\<alpha>_abr[unrest]: "in\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>>"
  by (transfer, auto simp add: in\<alpha>_def lens_prod_def)

lemma unrest_ok_abrupt_rel_uexpr_lift_cpa[unrest]:
  "$ok \<sharp> \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R" "$ok\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  "$abrupt \<sharp> \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R" "$abrupt\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  by (pred_auto)+

lemma unrest_ok_abrupt_rel_usubst_lift_cpa[unrest]:
  "$ok\<acute> \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R" "$ok \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R"
  "$abrupt\<acute> \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R" "$abrupt \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto+

lemma unrest_in_out_rel_ok_abrupt_res_abr [unrest]:
  "$ok \<sharp> (P \<restriction>\<^sub>\<alpha> ok)" "$ok\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> ok)"
  "$abrupt \<sharp> (P \<restriction>\<^sub>\<alpha> abrupt)" "$abrupt\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> abrupt)"
  by (simp_all add: rel_var_res_def unrest)

lemma uabr_alphabet_unrest[unrest]:(*FIXEME:These laws should be generated automatically by alphabet backend since all the fields of alphabet are independant*)
  "$ok\<acute> \<sharp> $abrupt\<acute>" "$ok \<sharp> $abrupt"
  "$ok\<acute> \<sharp> $abrupt"  "$ok \<sharp> $abrupt\<acute>"
  "$abrupt\<acute> \<sharp> $ok\<acute>" "$abrupt \<sharp> $ok "
  "$abrupt \<sharp> $ok\<acute>"  "$abrupt\<acute> \<sharp> $ok"
  by pred_simp+

lemma cpa_ord [usubst]:
  "$ok \<prec>\<^sub>v $ok\<acute>" "$abrupt \<prec>\<^sub>v $abrupt\<acute>" "$ok \<prec>\<^sub>v $abrupt\<acute>"
  "$ok \<prec>\<^sub>v $abrupt" "$ok\<acute> \<prec>\<^sub>v $abrupt\<acute>" "$ok\<acute> \<prec>\<^sub>v $abrupt"
  by (simp_all add: var_name_ord_def)

lemma rel_usubst_lift_cpa_in_out_abrupt_ok[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> $abrupt = $abrupt" "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> (\<not>$abrupt) = (\<not>$abrupt)"
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> ($ok) = ($ok)" "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> (\<not>$ok) = (\<not>$ok)"
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> ($abrupt\<acute>) = (($abrupt\<acute>))" "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> (\<not>$abrupt\<acute>) = (\<not>$abrupt\<acute>)"
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> ($ok\<acute>) = ($ok\<acute>)"  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> (\<not>$ok\<acute>) = (\<not>$ok\<acute>)"
  by (simp_all add: usubst unrest)

lemma abrupt_ok_simpl[uabr_comp]:
  "($abrupt;; Simpl\<^sub>A\<^sub>B\<^sub>R P) = $abrupt" "(\<not>$ok;; Simpl\<^sub>A\<^sub>B\<^sub>R P) = (\<not>$ok)"
  "($abrupt;; (P \<turnstile> Q)) = $abrupt" "(\<not>$ok;; (P \<turnstile> Q)) = (\<not>$ok)"
  "(\<not>$abrupt;; Simpl\<^sub>A\<^sub>B\<^sub>R P) = (\<not>$abrupt)" "(\<not>$ok;; Simpl\<^sub>A\<^sub>B\<^sub>R P) = (\<not>$ok)"
  "(\<not>$abrupt;; (P \<turnstile> Q)) = (\<not>$abrupt)" "(\<not>$ok;; (P \<turnstile> Q)) = (\<not>$ok)"
  "($abrupt\<acute>;; Simpl\<^sub>A\<^sub>B\<^sub>R P) = $abrupt\<acute>"
  "(\<not>$abrupt\<acute>;; Simpl\<^sub>A\<^sub>B\<^sub>R P) = (\<not>$abrupt\<acute>)"
  by rel_auto+

lemma simpl_abr_in_ok:
  "Simpl\<^sub>A\<^sub>B\<^sub>R ($ok) = ((\<not>$abrupt \<and> ($ok \<Rightarrow>$ok\<acute>)) \<or> (II))"
  by rel_auto

lemma  simpl_abr_our_ok:
  "Simpl\<^sub>A\<^sub>B\<^sub>R ($ok\<acute>) =
   ((\<not>$abrupt \<and> ($ok \<Rightarrow>$ok\<acute>)) \<or> (II))"
  by rel_auto

lemma simpl_abr_in_abrupt:
  "Simpl\<^sub>A\<^sub>B\<^sub>R ($abrupt) =
   ((\<not>$abrupt \<and> ($ok \<Rightarrow>($ok\<acute> \<and> $abrupt))) \<or> ($abrupt \<and> II))"
  by rel_auto

lemma simpl_abr_alr_def:
  "Simpl\<^sub>A\<^sub>B\<^sub>R (P) =
   ((\<not>$abrupt \<and> ($ok \<Rightarrow>($ok\<acute> \<and> P))) \<or> ($abrupt \<and> II))"
  by rel_auto

subsection \<open>Healthiness condition behavior\<close>

lemma rel_usubst_cpa_c3_abr[usubst]:
  assumes "$ok \<sharp> \<sigma>" "$ok\<acute> \<sharp> \<sigma> "
  shows "\<sigma> \<dagger> C3_abr(P) = (\<sigma> \<dagger> P \<triangleleft> \<sigma> \<dagger> (\<not>$abrupt) \<triangleright> (\<sigma> \<dagger> II))"
  using assms unfolding C3_abr_def
  by (simp add: usubst)

lemma Simpl_abr_idem[simp]: "Simpl\<^sub>A\<^sub>B\<^sub>R(Simpl\<^sub>A\<^sub>B\<^sub>R(P)) = Simpl\<^sub>A\<^sub>B\<^sub>R(P)"
  by (rel_auto)

lemma simpl_abr_Idempotent: "Idempotent Simpl\<^sub>A\<^sub>B\<^sub>R"
  by (simp add: Idempotent_def)

lemma Simpl_abr_mono: "P \<sqsubseteq> Q \<Longrightarrow> Simpl\<^sub>A\<^sub>B\<^sub>R(P) \<sqsubseteq> Simpl\<^sub>A\<^sub>B\<^sub>R(Q)"
  by (rel_auto)

lemma simpl_abr_Monotonic: "Monotonic Simpl\<^sub>A\<^sub>B\<^sub>R"
  by (simp add: Monotonic_def Simpl_abr_mono)

lemma simpl_abr_def:
  "Simpl\<^sub>A\<^sub>B\<^sub>R(P) = ((\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> P) \<triangleleft> \<not>$abrupt \<triangleright>  II)"
  unfolding C3_abr_def ..


lemma simpl_abr_condr[uabr_simpl]:
  "Simpl\<^sub>A\<^sub>B\<^sub>R(P \<triangleleft> b \<triangleright> Q) = (Simpl\<^sub>A\<^sub>B\<^sub>R(P) \<triangleleft> b \<triangleright> Simpl\<^sub>A\<^sub>B\<^sub>R(Q))"
  unfolding simpl_abr_def
  by (simp add: urel_cond)

lemma simpl_abr_skip_abr[uabr_simpl]:
  "Simpl\<^sub>A\<^sub>B\<^sub>R(SKIP\<^sub>A\<^sub>B\<^sub>R) = (SKIP\<^sub>A\<^sub>B\<^sub>R)"
  by (simp add: urel_cond urel_defs)

lemma simpl_abr_throw_abr:
  "Simpl\<^sub>A\<^sub>B\<^sub>R(THROW\<^sub>A\<^sub>B\<^sub>R) = ((\<not>$abrupt) \<and> ($ok \<Rightarrow>($ok\<acute> \<and> $abrupt\<acute> \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R)) \<or> ($abrupt \<and> II))"
  by rel_auto

lemma simpl_abr_assign_abr[uabr_simpl]:
  "Simpl\<^sub>A\<^sub>B\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R) = (\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R)"
  by (simp add: urel_cond urel_defs)

lemma simpl_abr_throw_abr_comp_abrupt[uabr_simpl]:
  "Simpl\<^sub>A\<^sub>B\<^sub>R (THROW\<^sub>A\<^sub>B\<^sub>R;; ((abrupt :== (\<not> &abrupt);; Simpl\<^sub>A\<^sub>B\<^sub>R Q) \<triangleleft> $abrupt \<triangleright> II)) = Simpl\<^sub>A\<^sub>B\<^sub>R Q"
   apply pred_simp
   apply rel_simp
   apply auto
done

lemma simpl_abr_throw_abr_comp_abrupt_cond_throw_abr[uabr_simpl]:
  "Simpl\<^sub>A\<^sub>B\<^sub>R (THROW\<^sub>A\<^sub>B\<^sub>R;; ((abrupt :== (\<not> &abrupt);; THROW\<^sub>A\<^sub>B\<^sub>R) \<triangleleft> $abrupt \<triangleright> II)) = Simpl\<^sub>A\<^sub>B\<^sub>R THROW\<^sub>A\<^sub>B\<^sub>R"
   apply pred_simp
   apply rel_simp
   apply auto
done

lemma simpl_abr_throw_abr_comp_abrupt_cond_skip_abr[uabr_simpl]:
  "Simpl\<^sub>A\<^sub>B\<^sub>R (THROW\<^sub>A\<^sub>B\<^sub>R;; ((abrupt :== (\<not> &abrupt);; SKIP\<^sub>A\<^sub>B\<^sub>R) \<triangleleft> $abrupt \<triangleright> II)) = SKIP\<^sub>A\<^sub>B\<^sub>R"
   apply pred_simp
   apply rel_simp
   apply auto
done

lemma simpl_abr_throw_abr_comp_abrupt_cond_assigns_abr[uabr_simpl]:
  "Simpl\<^sub>A\<^sub>B\<^sub>R (THROW\<^sub>A\<^sub>B\<^sub>R;; ((abrupt :== (\<not> &abrupt);; \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R) \<triangleleft> $abrupt \<triangleright> II)) = \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R"
   apply pred_simp
   apply rel_simp
   apply auto
done

lemma C3_abr_throw_abr_comp_abrupt[uabr_simpl]:
  "C3_abr (THROW\<^sub>A\<^sub>B\<^sub>R;; ((abrupt :== (\<not> &abrupt);; Simpl\<^sub>A\<^sub>B\<^sub>R Q) \<triangleleft> $abrupt \<triangleright> II)) =
    Simpl\<^sub>A\<^sub>B\<^sub>R Q"
  apply pred_simp
  apply rel_simp
  apply safe
  apply auto
done

lemma C3_abr_throw_abr_comp_abrupt_cond_skip_abr[uabr_simpl]:
  "C3_abr (THROW\<^sub>A\<^sub>B\<^sub>R;; ((abrupt :== (\<not> &abrupt);; SKIP\<^sub>A\<^sub>B\<^sub>R) \<triangleleft> $abrupt \<triangleright> II)) =
    SKIP\<^sub>A\<^sub>B\<^sub>R"
  apply pred_simp
  apply rel_simp
  apply safe
  apply auto
done

lemma C3_abr_throw_abr_comp_abrupt_cond_throw_abr[uabr_simpl]:
  "C3_abr (THROW\<^sub>A\<^sub>B\<^sub>R;; ((abrupt :== (\<not> &abrupt);; THROW\<^sub>A\<^sub>B\<^sub>R) \<triangleleft> $abrupt \<triangleright> II)) =
    C3_abr THROW\<^sub>A\<^sub>B\<^sub>R"
  apply pred_simp
  apply rel_simp
  apply safe
  apply auto
done

lemma C3_abr_throw_abr_comp_abrupt_cond_assigns_abr[uabr_simpl]:
  "C3_abr (THROW\<^sub>A\<^sub>B\<^sub>R;; ((abrupt :== (\<not> &abrupt);; \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R) \<triangleleft> $abrupt \<triangleright> II)) =
    \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R"
  apply pred_simp
  apply rel_simp
  apply safe
  apply auto
done

(*lemma [uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R;; ((abrupt :== (\<not> &abrupt);; THROW\<^sub>A\<^sub>B\<^sub>R) \<triangleleft> $abrupt \<triangleright> II)) =
   (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> ($abrupt\<acute> \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R)) "
  apply pred_simp
  apply rel_simp
  apply safe
  apply auto
done

lemma throw_abr_comp_abrupt_cond_skip_abr[uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R;; ((abrupt :== (\<not> &abrupt);; SKIP\<^sub>A\<^sub>B\<^sub>R) \<triangleleft> $abrupt \<triangleright> II)) =
   (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<not>$abrupt\<acute> \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R)) "
  apply pred_simp
  apply rel_simp
  apply safe
  apply auto
done

lemma [uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R;; ((abrupt :== (\<not> &abrupt);; \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R) \<triangleleft> $abrupt \<triangleright> II)) =
   (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<not>$abrupt\<acute> \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R)) "
  apply pred_simp
  apply rel_simp
  apply safe
  apply auto
done*)

lemma [uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R;; ((abrupt :== (\<not> &abrupt);; \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R) \<triangleleft> $abrupt \<triangleright> II)) = (true) "
  apply pred_simp
  apply rel_simp
  apply auto
done

lemma simpl_abr_form:
  "Simpl\<^sub>A\<^sub>B\<^sub>R(P) = (((\<not>$abrupt) \<and> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (P)))  \<or> ($abrupt \<and> II))"
  by rel_auto

lemma abrupt_simpl_abr[uabr_simpl]:
  "($abrupt \<and> Simpl\<^sub>A\<^sub>B\<^sub>R(P)) = ($abrupt \<and>II)"
   by rel_auto

lemma nabrupt_simpl_abr[uabr_simpl]:
  "(\<not>$abrupt \<and> Simpl\<^sub>A\<^sub>B\<^sub>R(P)) = (\<not>$abrupt \<and> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (P)))"
  by (rel_auto)

definition design_abr_sup :: "('\<alpha>,'\<beta>) rel_cpa set \<Rightarrow> ('\<alpha>,'\<beta>) rel_cpa" ("\<Sqinter>\<^sub>A\<^sub>B\<^sub>R_" [900] 900) where
"\<Sqinter>\<^sub>A\<^sub>B\<^sub>R A = (if (A = {}) then \<top>\<^sub>A\<^sub>B\<^sub>R else \<Sqinter> A)"

lemma simpl_abr_Continuous: "Continuous Simpl\<^sub>A\<^sub>B\<^sub>R"
  apply rel_auto
done

lemma simpl_abr_R3_conj:
  "Simpl\<^sub>A\<^sub>B\<^sub>R(P \<and> Q) = (Simpl\<^sub>A\<^sub>B\<^sub>R(P) \<and> Simpl\<^sub>A\<^sub>B\<^sub>R(Q))"
  by (rel_auto)

lemma simpl_abr_disj:
  "Simpl\<^sub>A\<^sub>B\<^sub>R(P \<or> Q) = (Simpl\<^sub>A\<^sub>B\<^sub>R(P) \<or> Simpl\<^sub>A\<^sub>B\<^sub>R(Q))"
  by (rel_auto)

lemma Simpl_abr_USUP:
  assumes "A \<noteq> {}"
  shows "Simpl\<^sub>A\<^sub>B\<^sub>R(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> Simpl\<^sub>A\<^sub>B\<^sub>R(P(i)))"
  using assms by (rel_auto)

lemma design_abr_sup_non_empty [simp]:
  "A \<noteq> {} \<Longrightarrow> \<Sqinter>\<^sub>A\<^sub>B\<^sub>R A = \<Sqinter> A"
  by (simp add: design_abr_sup_def)

subsection \<open>Signature behavior\<close>

lemma design_top_abr:
  "(P \<turnstile> Q) \<sqsubseteq> \<top>\<^sub>A\<^sub>B\<^sub>R"
  by (rel_auto)

lemma design_abr_sup_empty [simp]:
  "\<Sqinter>\<^sub>A\<^sub>B\<^sub>R {} = \<top>\<^sub>A\<^sub>B\<^sub>R"
  by (simp add: design_abr_sup_def)

abbreviation design_inf :: "('\<alpha>, '\<beta>) rel_des set \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" ("\<Squnion>\<^sub>A\<^sub>B\<^sub>R_" [900] 900) where
  "\<Squnion>\<^sub>A\<^sub>B\<^sub>R A \<equiv> \<Squnion> A"

lemma design_bottom_abr:
  "\<bottom>\<^sub>A\<^sub>B\<^sub>R \<sqsubseteq> (P \<turnstile> Q)"
  by simp

lemma Simpl_abr_bottom_abr:
  "\<bottom>\<^sub>A\<^sub>B\<^sub>R \<sqsubseteq> Simpl\<^sub>A\<^sub>B\<^sub>R (P)"
  by simp

lemma Simpl_abr_UINF:
  assumes "A \<noteq> {}"
  shows "Simpl\<^sub>A\<^sub>B\<^sub>R(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> Simpl\<^sub>A\<^sub>B\<^sub>R(P(i)))"
  using assms by (rel_auto)

lemma skip_cpa_def:
  "II = (\<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R \<and> $abrupt =\<^sub>u $abrupt\<acute> \<and> $ok =\<^sub>u $ok\<acute>)"
  by rel_auto

lemma skip_lift_cpa_def:
  "\<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R = ($\<Sigma>\<^sub>A\<^sub>B\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma seqr_abrupt_true [usubst]: "(P;; Q) \<^sub>a\<^sub>t = (P \<^sub>a\<^sub>t;; Q)"
  by (rel_auto)

lemma seqr_abrupt_false [usubst]: "(P;; Q) \<^sub>a\<^sub>f = (P \<^sub>a\<^sub>f;; Q)"
  by (rel_auto)

lemma rel_usubst_lift_cpa_uexpr_lift_cpa[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R = \<lceil>\<sigma> \<dagger> P\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto

lemma usubst_lift_cpa_assigns_lift_cpa [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>\<langle>\<rho>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R = \<lceil>\<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  by (simp add: usubst)

lemma usubst_lift_cpa_pre_uexpr_lift_cpa[usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< = \<lceil>\<sigma> \<dagger> b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub><"
  by (simp add: usubst)

lemma rel_usubst_lift_cpa_design[usubst]:
  "(\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> (Q \<turnstile> P)) = (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> Q) \<turnstile> (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>A\<^sub>B\<^sub>R \<dagger> P)"
  by (simp add: usubst unrest)

lemma usubst_cpa_true[usubst]: "\<sigma> \<dagger> \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R = \<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto

lemma usubst_cpa_false[usubst]: "\<sigma> \<dagger> \<lceil>false\<rceil>\<^sub>A\<^sub>B\<^sub>R = \<lceil>false\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto

lemma rel_usubst_cpa_skip_cpa[usubst]:
  "(\<sigma> \<dagger> II) = ((\<sigma> \<dagger> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R) \<and> \<sigma> \<dagger> $abrupt =\<^sub>u \<sigma> \<dagger> $abrupt\<acute> \<and> \<sigma> \<dagger> $ok =\<^sub>u \<sigma> \<dagger> $ok\<acute>)"
  by (simp add: usubst unrest skip_cpa_def)

lemma usubst_lift_cpa_skip_lift_cpa[usubst]:
  "(\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R) = \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  unfolding skip_r_def
  by (simp add: usubst_lift_cpa_assigns_lift_cpa)

lemma usubst_cpa_skip_cpa [usubst]:
  assumes "$ok \<sharp> \<sigma>" "$ok\<acute> \<sharp> \<sigma> "
  shows
  "(\<sigma> \<dagger> SKIP\<^sub>A\<^sub>B\<^sub>R) = (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<sigma> \<dagger> ((\<not>$abrupt\<acute>) \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R)) \<triangleleft> \<sigma> \<dagger> (\<not>$abrupt) \<triangleright> (\<sigma> \<dagger> (II)))"
  using assms unfolding skip_abr_def
  using [[simp_trace]]
  by (simp add: usubst)

lemma usubst_cpa_throw_cpa [usubst]:
  assumes "$ok \<sharp> \<sigma>" "$ok\<acute> \<sharp> \<sigma> "
  shows
  "(\<sigma> \<dagger> THROW\<^sub>A\<^sub>B\<^sub>R) = (\<sigma> \<dagger> (\<not>$abrupt) \<turnstile> (\<sigma> \<dagger> ($abrupt\<acute> \<and> \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R)))"
  using assms unfolding throw_abr_def
  by (simp add: usubst)

lemma usubst_cpa_assigns_cpa [usubst]:
  assumes "$ok \<sharp> \<sigma>" "$ok\<acute> \<sharp> \<sigma> "
  shows
  "\<sigma> \<dagger> \<langle>\<rho>\<rangle>\<^sub>A\<^sub>B\<^sub>R = (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (\<sigma> \<dagger> ((\<not>$abrupt\<acute>) \<and> \<lceil>\<langle>\<rho>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R)) \<triangleleft> \<sigma> \<dagger> (\<not>$abrupt) \<triangleright>  (\<sigma> \<dagger> (II)))"
  using assms unfolding assigns_abr_def
  by (simp add: usubst)

lemma simpl_comp_left_distr:
  "(C3_abr (P);; R) = ((P;; R) \<triangleleft> \<not>$abrupt \<triangleright> (II;; R))"
  apply pred_simp
  apply rel_simp
  apply fastforce
done

lemma c3_abr_comp_semir:
  "(C3_abr(P);; C3_abr(R)) = C3_abr (P;; C3_abr(R))"
  by rel_auto

lemma c3_abr_comp_simpl[uabr_comp]:
  "(C3_abr(P);; C3_abr(R)) = ((P;; C3_abr(R)) \<triangleleft> \<not>$abrupt \<triangleright> (II))"
  by rel_auto

lemma simpl_abr_comp_semir:
  "(Simpl\<^sub>A\<^sub>B\<^sub>R(P);; Simpl\<^sub>A\<^sub>B\<^sub>R(R)) = Simpl\<^sub>A\<^sub>B\<^sub>R ((\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> P);; Simpl\<^sub>A\<^sub>B\<^sub>R(R))"
  by rel_auto

theorem design_top_abr_left_zero[uabr_comp]:
  "(\<top>\<^sub>A\<^sub>B\<^sub>R;; (P \<turnstile> Q)) = \<top>\<^sub>A\<^sub>B\<^sub>R"
  by (rel_auto)

theorem Simpl_abr_top_abr_left_zero[uabr_comp]:
  "(\<top>\<^sub>A\<^sub>B\<^sub>R;; Simpl\<^sub>A\<^sub>B\<^sub>R (P)) = \<top>\<^sub>A\<^sub>B\<^sub>R"
  by (rel_auto)

lemma assigns_lift_cpa_comp_rel_cpa[uabr_comp]:
  assumes "$ok \<sharp> P" "$abrupt \<sharp> P"
  shows  "(\<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>A\<^sub>B\<^sub>R;; P) = (\<lceil>\<sigma>\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> P)"
  apply (insert assms)
  apply pred_simp
  apply rel_blast
done

lemma lift_des_skip_dr_unit_abr[uabr_comp]:
  "(\<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R;; \<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R) = \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  "(\<lceil>II\<rceil>\<^sub>A\<^sub>B\<^sub>R;; \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R) = \<lceil>P\<rceil>\<^sub>A\<^sub>B\<^sub>R"
  by (rel_auto)+

lemma skip_cpa_left_comp_simpl[uabr_comp]:
  "(SKIP\<^sub>A\<^sub>B\<^sub>R;; Simpl\<^sub>A\<^sub>B\<^sub>R(R)) = (Simpl\<^sub>A\<^sub>B\<^sub>R(R))"
  by rel_auto

lemma skip_cpa_right_comp_simpl[uabr_comp]:
  "(Simpl\<^sub>A\<^sub>B\<^sub>R(R);; SKIP\<^sub>A\<^sub>B\<^sub>R) = (Simpl\<^sub>A\<^sub>B\<^sub>R(R))"
  by rel_auto

lemma throw_cpa_left_comp_simpl[uabr_comp]:
  "(THROW\<^sub>A\<^sub>B\<^sub>R;; Simpl\<^sub>A\<^sub>B\<^sub>R(R)) = (THROW\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma assign_abr_alt_def:
  "\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R = Simpl\<^sub>A\<^sub>B\<^sub>R (\<not>$abrupt\<acute> \<and> \<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> II\<rceil>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto

lemma assign_abr_left_comp_c3[uabr_comp]:
  "\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; C3_abr (P \<turnstile> Q) = C3_abr (\<lceil>a\<rceil>\<^sub>s\<^sub>A\<^sub>B\<^sub>R \<dagger> (P \<turnstile> Q))"
  by rel_auto

lemma assigns_abr_comp[uabr_comp]:
  "(\<langle>f\<rangle>\<^sub>A\<^sub>B\<^sub>R;; \<langle>g\<rangle>\<^sub>A\<^sub>B\<^sub>R) = \<langle>g \<circ> f\<rangle>\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto

lemma usubst_cpa_des_cond_abr[usubst]:
  "\<lbrakk> $ok \<sharp> \<sigma>; $ok\<acute> \<sharp> \<sigma> \<rbrakk> \<Longrightarrow>
    \<sigma> \<dagger> (R \<turnstile> bif b then P else Q eif) =
    (\<sigma> \<dagger> R \<turnstile> (\<sigma> \<dagger> P \<triangleleft> \<sigma> \<dagger> \<lceil>b\<rceil>\<^sub>A\<^sub>B\<^sub>R\<^sub>< \<triangleright> \<sigma> \<dagger> Q))"
  by (simp add: usubst)

lemma comp_cond_abr_left_distr[uabr_comp]:
  "((bif b then Simpl\<^sub>A\<^sub>B\<^sub>R P else Simpl\<^sub>A\<^sub>B\<^sub>R Q eif);; Simpl\<^sub>A\<^sub>B\<^sub>R R) =
    (bif b then (Simpl\<^sub>A\<^sub>B\<^sub>R P;; Simpl\<^sub>A\<^sub>B\<^sub>R R) else (Simpl\<^sub>A\<^sub>B\<^sub>R Q;; Simpl\<^sub>A\<^sub>B\<^sub>R R) eif)"
  apply (simp add: usubst uabr_comp)
  apply pred_simp
  apply rel_simp
  apply auto
done

lemma if_mono:
  "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (bif b then P\<^sub>1 else Q\<^sub>1 eif) \<sqsubseteq> (bif b then P\<^sub>2 else Q\<^sub>2 eif)"
  by rel_auto

subsection \<open>While abrupt usubst\<close>

subsection \<open>block abrupt usubst\<close>

subsection \<open>Catch abrupt usubst\<close>

end
