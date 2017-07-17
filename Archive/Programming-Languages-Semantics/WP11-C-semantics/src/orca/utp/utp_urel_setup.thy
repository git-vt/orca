section {* UTP variables *}

theory utp_urel_setup
  imports utp_lift utp_tactics
begin
(*tactics are in utp_tactics*)
consts
  useq   :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr ";;" 51)
  uskip  :: "'a" ("II")

definition in\<alpha> :: "('\<alpha>, '\<alpha> \<times> '\<beta>) uvar" where
"in\<alpha> = \<lparr> lens_get = fst, lens_put = \<lambda> (A, A') v. (v, A') \<rparr>"

definition out\<alpha> :: "('\<beta>, '\<alpha> \<times> '\<beta>) uvar" where
"out\<alpha> = \<lparr> lens_get = snd, lens_put = \<lambda> (A, A') v. (A, v) \<rparr>"

declare in\<alpha>_def [urel_defs]
declare out\<alpha>_def [urel_defs]

lemma var_in_alpha [simp]: "x ;\<^sub>L in\<alpha> = ivar x"
  by (simp add: fst_lens_def in\<alpha>_def in_var_def)

lemma var_out_alpha [simp]: "x ;\<^sub>L out\<alpha> = ovar x"
  by (simp add: out\<alpha>_def out_var_def snd_lens_def)

lemma out_alpha_in_indep [simp]:
  "out\<alpha> \<bowtie> in_var x" "in_var x \<bowtie> out\<alpha>"
  by (simp_all add: in_var_def out\<alpha>_def lens_indep_def fst_lens_def lens_comp_def)

lemma in_alpha_out_indep [simp]:
  "in\<alpha> \<bowtie> out_var x" "out_var x \<bowtie> in\<alpha>"
  by (simp_all add: in_var_def in\<alpha>_def lens_indep_def fst_lens_def lens_comp_def)

text {* The alphabet of a relation consists of the input and output portions *}

lemma alpha_in_out:
  "\<Sigma> \<approx>\<^sub>L in\<alpha> +\<^sub>L out\<alpha>"
  by (metis fst_lens_def fst_snd_id_lens in\<alpha>_def lens_equiv_refl out\<alpha>_def snd_lens_def)

abbreviation usubst_rel_lift :: "'\<alpha> usubst \<Rightarrow> ('\<alpha> \<times> '\<beta>) usubst" ("\<lceil>_\<rceil>\<^sub>s") where
"\<lceil>\<sigma>\<rceil>\<^sub>s \<equiv> \<sigma> \<oplus>\<^sub>s in\<alpha>"

abbreviation usubst_rel_drop :: "('\<alpha> \<times> '\<alpha>) usubst \<Rightarrow> '\<alpha> usubst" ("\<lfloor>_\<rfloor>\<^sub>s") where
"\<lfloor>\<sigma>\<rfloor>\<^sub>s \<equiv> \<sigma> \<restriction>\<^sub>s in\<alpha>"


end
