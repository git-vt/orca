 
section {*Algebraic laws of programming*}

text{*In this section we introduce the semantic rules related to the different
      statements of IMP. In the literature this also known as the algebraic laws of programming.
      In our framework we will use these rules in order to optimize a given program written in our 
      language, and this before any deductive proof verification activity or formal testing.*}

theory Algebraic_Laws_aux
imports "../../../theories/utp_designs"
begin

subsection {*complementing usubst*}
lemma bool_seqr_laws [usubst]:
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s true) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>true/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s false) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>false/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s true) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>true/$x\<acute>\<rbrakk>)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s false) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>false/$x\<acute>\<rbrakk>)"
    by (simp_all add: bool_seqr_laws)

subsection {*complementing unrest*}
lemma undep_imp_unrest[unrest]: (*FIXEME:This law should be used by alphabet-backend to generate automatically unrest between different fields*)
  assumes "x \<bowtie> y "
  shows "$x \<sharp> $y" 
  using assms unfolding lens_indep_def
  by pred_auto

subsection {*complementing laws for preds *}

lemma upred_not_not[simp]:
"\<not> \<not> P = P"
  by rel_auto

subsection {*laws for urel *}

lemma unrest_iuvar_not[unrest]: "out\<alpha> \<sharp> (\<not>$x)"
  by rel_auto

lemma unrest_ouvar_not[unrest]: "in\<alpha> \<sharp> (\<not>$x\<acute>)"
  by rel_auto

lemma assigns_r_usubst_skip_r[usubst]:
  "(\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> II) =  \<langle>\<sigma>\<rangle>\<^sub>a" 
  by rel_auto

lemma cond_not_cond_L6_right[urel_cond]: 
  "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> \<not> b \<triangleright> R)) = (P \<triangleleft> b \<triangleright> Q)" 
  by rel_auto

lemma cond_not_cond_L6_right_variant[urel_cond]: 
  "(P \<triangleleft> \<not> b \<triangleright> (Q \<triangleleft>  b \<triangleright> R)) = (P \<triangleleft> \<not> b \<triangleright> Q)" 
  by rel_auto

lemma cond_not_cond_L6_left[urel_cond]: 
  "((P \<triangleleft> b \<triangleright> Q) \<triangleleft> \<not> b \<triangleright> R) = (Q \<triangleleft>\<not> b \<triangleright> R)" 
  by rel_auto

lemma cond_not_cond_L6_left_variant[urel_cond]: 
  "((P \<triangleleft> \<not> b \<triangleright> Q) \<triangleleft> b \<triangleright> R) = (Q \<triangleleft> b \<triangleright> R)" 
  by rel_auto

lemma cond_L6_left[urel_cond]: 
  "((P \<triangleleft>  b \<triangleright> Q) \<triangleleft> b \<triangleright> R) = (P \<triangleleft> b \<triangleright> R)" 
  by rel_auto

subsection {*laws for des*}
 
lemma usubst_d_true[usubst]: "\<sigma> \<dagger> \<lceil>true\<rceil>\<^sub>D = \<lceil>true\<rceil>\<^sub>D" 
  by rel_auto

lemma usubst_d_false[usubst]: "\<sigma> \<dagger> \<lceil>false\<rceil>\<^sub>D = \<lceil>false\<rceil>\<^sub>D" 
  by rel_auto

lemma usubst_des_skip_des [usubst]:
  assumes "$ok \<sharp> \<sigma>" "$ok\<acute> \<sharp> \<sigma>"
  shows "(\<sigma> \<dagger> II\<^sub>D) = (\<lceil>true\<rceil>\<^sub>D \<turnstile> (\<sigma> \<dagger> \<lceil>II\<rceil>\<^sub>D))"
  using assms unfolding skip_d_def rdesign_def
  by (simp add: assms usubst) 

lemma cond_L6_right_des[urel_cond]: 
  "(R \<triangleleft> b \<triangleright> (S \<turnstile> (P \<triangleleft> b \<triangleright> Q))) = (R \<triangleleft> b \<triangleright> (S \<turnstile> Q))" 
  by rel_auto

lemma cond_L6_left_des[urel_cond]: 
  "((S \<turnstile> (P \<triangleleft> b \<triangleright> Q)) \<triangleleft> b \<triangleright> R) =  (S \<turnstile> P \<triangleleft>b \<triangleright> R)" 
  by rel_auto

lemma cond_not_cond_L6_right_des[urel_cond]: 
  "( R \<triangleleft> \<not> b \<triangleright> (S \<turnstile> (P \<triangleleft> b \<triangleright> Q)) ) =  (R \<triangleleft> \<not> b \<triangleright> (S \<turnstile> P))" 
  by rel_auto

lemma cond_not_cond_L6_right_des_variant[urel_cond]:
  "R \<triangleleft> b \<triangleright> (S \<turnstile> (P \<triangleleft> \<not> b \<triangleright> Q)) = R \<triangleleft> b \<triangleright> (S \<turnstile> P)"
  by rel_auto

lemma cond_not_cond_L6_left_des[urel_cond]: 
  "((S \<turnstile> (P \<triangleleft> b \<triangleright> Q)) \<triangleleft> \<not> b \<triangleright> R) =  ((S \<turnstile> Q) \<triangleleft> \<not> b \<triangleright> R)" 
  by rel_auto

lemma cond_not_cond_L6_left_des_variant[urel_cond]: 
  "((S \<turnstile> (P \<triangleleft> \<not> b \<triangleright> Q)) \<triangleleft> b \<triangleright> R) =  ((S \<turnstile> Q) \<triangleleft> b \<triangleright> R)" 
  by rel_auto



end