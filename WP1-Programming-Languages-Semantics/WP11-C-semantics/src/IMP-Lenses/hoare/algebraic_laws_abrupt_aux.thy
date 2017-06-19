
section "Auxiliary algebraic laws for abrupt designs"
theory algebraic_laws_abrupt_aux
imports "../theories/utp_abrupt_designs"

begin

subsection {*Abrupt semantics behavior*}

lemma Simpl_abr_idem[simp]: "Simpl\<^sub>A\<^sub>B\<^sub>R(Simpl\<^sub>A\<^sub>B\<^sub>R(P)) = Simpl\<^sub>A\<^sub>B\<^sub>R(P)"
  by (rel_auto)

lemma Simpl_abr_Idempotent: "Idempotent Simpl\<^sub>A\<^sub>B\<^sub>R"
  by (simp add: Idempotent_def Simpl_abr_idem)

lemma Simpl_abr_mono: "P \<sqsubseteq> Q \<Longrightarrow> Simpl\<^sub>A\<^sub>B\<^sub>R(P) \<sqsubseteq> Simpl\<^sub>A\<^sub>B\<^sub>R(Q)"
  by (rel_auto)

lemma Simpl_abr_Monotonic: "Monotonic Simpl\<^sub>A\<^sub>B\<^sub>R"
  by (simp add: Monotonic_def Simpl_abr_mono)

lemma Simpl_abr_condr: "Simpl\<^sub>A\<^sub>B\<^sub>R(P \<triangleleft> b \<triangleright> Q) = (Simpl\<^sub>A\<^sub>B\<^sub>R(P) \<triangleleft> b \<triangleright> Simpl\<^sub>A\<^sub>B\<^sub>R(Q))"
  by (rel_auto)

lemma Simpl_abr_if_abr: 
  "Simpl\<^sub>A\<^sub>B\<^sub>R(bif b then P else Q eif) = 
   (bif b then Simpl\<^sub>A\<^sub>B\<^sub>R(P) else Simpl\<^sub>A\<^sub>B\<^sub>R(Q) eif)"
  by (rel_auto)

lemma Simpl_abr_skip_abr[simp]: "Simpl\<^sub>A\<^sub>B\<^sub>R(SKIP\<^sub>A\<^sub>B\<^sub>R) = (SKIP\<^sub>A\<^sub>B\<^sub>R)"
  by (rel_auto)
                    
lemma Simpl_abr_throw_abr[simp]: "Simpl\<^sub>A\<^sub>B\<^sub>R(THROW\<^sub>A\<^sub>B\<^sub>R) = (THROW\<^sub>A\<^sub>B\<^sub>R)"
  by (rel_auto)

lemma Simpl_abr_assign_abr[simp]: "Simpl\<^sub>A\<^sub>B\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R) = (\<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R)"
  by (rel_auto)

lemma Simpl_abr_form: "Simpl\<^sub>A\<^sub>B\<^sub>R(P) = ((\<not> (\<not>$abrupt \<and> ($abrupt_aux =\<^sub>u \<guillemotleft>None\<guillemotright>)) \<and> II) \<or> 
                              (\<not>$abrupt \<and> $abrupt_aux =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (P))))"
  by (rel_auto) 

lemma abrupt_Simpl_abr:
  "(\<not> (\<not>$abrupt \<and> ($abrupt_aux =\<^sub>u \<guillemotleft>None\<guillemotright>)) \<and> Simpl\<^sub>A\<^sub>B\<^sub>R(P)) = 
   (II \<and> \<not> (\<not>$abrupt\<acute> \<and> ($abrupt_aux\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright>)))"
  by (rel_auto)

lemma nabrupt_Simpl_abr:
  "(\<not>$abrupt \<and> $abrupt_aux =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> Simpl\<^sub>A\<^sub>B\<^sub>R(P)) = 
   (\<not>$abrupt \<and> $abrupt_aux =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> (\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (P)))"
  by (rel_auto)

lemma Simpl_abr_semir_form:
  "(Simpl\<^sub>A\<^sub>B\<^sub>R(P) ;; Simpl\<^sub>A\<^sub>B\<^sub>R(Q)) = Simpl\<^sub>A\<^sub>B\<^sub>R((\<lceil>true\<rceil>\<^sub>A\<^sub>B\<^sub>R \<turnstile> (P)) ;; Simpl\<^sub>A\<^sub>B\<^sub>R(Q))"
  by (rel_simp) blast 

lemma Simpl_abr_semir_closure:
  assumes "P is Simpl\<^sub>A\<^sub>B\<^sub>R" "Q is Simpl\<^sub>A\<^sub>B\<^sub>R"
  shows "(P ;; Q) is Simpl\<^sub>A\<^sub>B\<^sub>R"
  using assms
  by (metis  Healthy_def Simpl_abr_semir_form Simpl_abr_idem)

definition design_abr_sup :: "('a,'\<alpha>,'\<beta>) rel_cpa set \<Rightarrow> ('a,'\<alpha>,'\<beta>) rel_cpa" ("\<Sqinter>\<^sub>A\<^sub>B\<^sub>R_" [900] 900) where
"\<Sqinter>\<^sub>A\<^sub>B\<^sub>R A = (if (A = {}) then \<top>\<^sub>A\<^sub>B\<^sub>R else \<Sqinter> A)"

lemma Simpl_abr_Continuous: "Continuous Simpl\<^sub>A\<^sub>B\<^sub>R"
  unfolding Continuous_def SUP_def apply rel_simp
  unfolding  SUP_def  
  apply transfer apply auto 
done

lemma Simpl_abr_R3_conj: "Simpl\<^sub>A\<^sub>B\<^sub>R(P \<and> Q) = (Simpl\<^sub>A\<^sub>B\<^sub>R(P) \<and> Simpl\<^sub>A\<^sub>B\<^sub>R(Q))"
  by (rel_auto)

lemma Simpl_abr_disj: "Simpl\<^sub>A\<^sub>B\<^sub>R(P \<or> Q) = (Simpl\<^sub>A\<^sub>B\<^sub>R(P) \<or> Simpl\<^sub>A\<^sub>B\<^sub>R(Q))"
  by (rel_auto)

lemma Simpl_abr_USUP:
  assumes "A \<noteq> {}"
  shows "Simpl\<^sub>A\<^sub>B\<^sub>R(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> Simpl\<^sub>A\<^sub>B\<^sub>R(P(i)))"
  using assms by (rel_auto)


lemma design_abr_sup_non_empty [simp]:  
  "A \<noteq> {} \<Longrightarrow> \<Sqinter>\<^sub>A\<^sub>B\<^sub>R A = \<Sqinter> A"
  by (simp add: design_abr_sup_def)

subsection {*Abrupt top behavior*}

theorem design_top_abr_left_zero[simp]: 
  "(\<top>\<^sub>A\<^sub>B\<^sub>R ;; (P \<turnstile> Q)) = \<top>\<^sub>A\<^sub>B\<^sub>R"
  by (rel_auto)

theorem Simpl_abr_top_abr_left_zero[simp]: 
  "(\<top>\<^sub>A\<^sub>B\<^sub>R ;; Simpl\<^sub>A\<^sub>B\<^sub>R (P)) = \<top>\<^sub>A\<^sub>B\<^sub>R"
  by (rel_auto)

lemma design_top_abr:
  "(P \<turnstile> Q) \<sqsubseteq> \<top>\<^sub>A\<^sub>B\<^sub>R"
  by (rel_auto)

lemma Simpl_abr_top_abr:
  "Simpl\<^sub>A\<^sub>B\<^sub>R (P) \<sqsubseteq> \<top>\<^sub>A\<^sub>B\<^sub>R"
  by (rel_auto)

lemma design_abr_sup_empty [simp]: 
  "\<Sqinter>\<^sub>A\<^sub>B\<^sub>R {} = \<top>\<^sub>A\<^sub>B\<^sub>R"
  by (simp add: design_abr_sup_def)

subsection {*Abrupt Bot behavior*}

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

subsection {*Abrupt If behavior*}

lemma if_mono:
  "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (bif b then P\<^sub>1 else Q\<^sub>1 eif) \<sqsubseteq> (bif b then P\<^sub>2 else Q\<^sub>2 eif)"
  by rel_auto

end