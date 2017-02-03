chapter {*Hoare Logic*}

theory Hoare
imports Algebraic_Laws

begin
section {*Examples*}
text {*In this section we introduce small examples showing how can use the tools from the lens 
       theory to represent a Hoare triple*}

named_theorems hoare

lemma Hoare_test1:
  assumes 1:"weak_lens Y"
  shows"(bop implies ((bop (op =) (VAR X) \<guillemotleft>1::int\<guillemotright>)) 
                     ((Y :== (VAR X))\<dagger> bop (op =) (VAR Y) \<guillemotleft>1::int\<guillemotright>)) = 
         \<guillemotleft>True\<guillemotright>"
  using 1 unfolding subst_upd_var_def
  by transfer  auto

lemma Hoare_test2:
  assumes 1:"weak_lens Y" and     2:"X \<bowtie> Y"
  shows"( (bop implies ((bop (op =) (VAR X) \<guillemotleft>1::int\<guillemotright>)) 
                     ((Y :== (VAR X))\<dagger> bop (op =) (VAR Y) \<guillemotleft>2::int\<guillemotright>)) 
          ) = \<guillemotleft>True\<guillemotright>"
  using 1 2 unfolding subst_upd_var_def lens_indep_def
  apply transfer 
  apply auto oops

lemma Hoare_test3:
  assumes 1:"vwb_lens Y" and  2:"vwb_lens X" and 3:"vwb_lens R"
  and     4:"X \<bowtie> Y" and     5:"X \<bowtie> R" and     6:"Y\<bowtie> R"
  shows "bop implies (bop conj (bop (op =) (VAR X) \<guillemotleft>1::int\<guillemotright>) (bop (op =) (VAR Y) \<guillemotleft>2::int\<guillemotright>))
                     ((R:== (VAR X) ; X :== (VAR Y); Y:== (VAR R))\<dagger>(bop conj (bop (op =) (VAR X) \<guillemotleft>2::int\<guillemotright>) (bop (op =) (VAR Y) \<guillemotleft>1::int\<guillemotright>))) = 
         \<guillemotleft>True\<guillemotright>"
  using assms unfolding subst_upd_var_def id_def lens_indep_def 
  by transfer auto 

lemma Hoare_test4:
  assumes 1:"weak_lens Y" and  2:"weak_lens X" and 3:"weak_lens R"
  and     4:"X \<bowtie> Y" and  5:"X \<bowtie> R" and  6:"Y\<bowtie> R"
  shows "bop implies (bop conj (bop (op =) (VAR X) \<guillemotleft>x\<guillemotright>) (bop (op =) (VAR Y) \<guillemotleft>y\<guillemotright>))
                     ((R:== (VAR X) ; X :== (VAR Y); Y:== (VAR R))\<dagger>(bop conj (bop (op =) (VAR X) \<guillemotleft>y\<guillemotright>) (bop (op =) (VAR Y) \<guillemotleft>x\<guillemotright>))) = 
         \<guillemotleft>True\<guillemotright>"
  using assms unfolding subst_upd_var_def id_def lens_indep_def 
  by transfer auto

section {*Hoare triple definition*}
text {*A Hoare triple is represented by a pre-condition @{text P} a post-condition @{text Q}
       and a program @{text C}. It says whenever the pre-condition holds then the post-condition
       must hold.*}
definition hoare :: "(bool ,  '\<alpha>) expr \<Rightarrow> '\<alpha> states \<Rightarrow> (bool ,  '\<alpha>) expr \<Rightarrow>  bool" ("\<lbrace>(1_)\<rbrace>/ (_)/\<lbrace>(1_)\<rbrace>") where
"\<lbrace>P\<rbrace>C\<lbrace>Q\<rbrace> = ((bop implies P (C \<dagger> Q)) = \<guillemotleft>True\<guillemotright>)"

(*definition hoare_valid :: "(bool ,  '\<alpha>) expr \<Rightarrow> '\<alpha> states \<Rightarrow> (bool ,  '\<alpha>) expr \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile>{P}C{Q} = ((bop implies P (C \<dagger> Q)) = \<guillemotleft>True\<guillemotright>)"*)

lemma Hoare_True [hoare]: "\<lbrace>P\<rbrace>C\<lbrace>\<guillemotleft>True\<guillemotright>\<rbrace>"
  unfolding hoare_def 
  by transfer auto

lemma Hoare_False [hoare]: "\<lbrace>\<guillemotleft>False\<guillemotright>\<rbrace>C\<lbrace>Q\<rbrace>"
  unfolding hoare_def 
  by transfer auto

section {*Hoare for SKIP*}

lemma Hoare_SKIP [hoare]: "\<lbrace>P\<rbrace>SKIP\<lbrace>P\<rbrace>"
  unfolding hoare_def
  by transfer auto

section {*Hoare for assignment*}

lemma Hoare_ASN:
 "\<lbrace>[X \<mapsto>\<^sub>s exp] \<dagger> P\<rbrace>X:== exp\<lbrace>P\<rbrace>" 
   unfolding subst_upd_var_def hoare_def 
  by transfer auto


lemma  Hoare_ASN_bop_test:
  assumes 1:"weak_lens Y"  
  shows "\<lbrace>bop (op =) (VAR X) \<guillemotleft>1\<guillemotright>\<rbrace>
          Y:== (VAR X)
         \<lbrace>bop (op =) (VAR Y) (\<guillemotleft>1\<guillemotright>)\<rbrace>"
  using 1 unfolding subst_upd_var_def hoare_def 
  by transfer auto 
  
lemma Hoare_ASN_uop:
  assumes 1:"weak_lens X"  
  shows "\<lbrace>uop P exp\<rbrace>
          X:== exp
         \<lbrace>uop P (VAR X)\<rbrace>" 
  using 1 unfolding subst_upd_var_def hoare_def   
  by transfer auto


lemma Hoare_ASN_bop1:
  assumes 1:"weak_lens X"  and 2:"X \<sharp> exp2"
  shows "\<lbrace>bop P exp1 exp2\<rbrace>
          X:== exp1
         \<lbrace>bop P (VAR X) exp2\<rbrace>" 
  using 1 2 unfolding subst_upd_var_def hoare_def unrest_def 
  by transfer auto

lemma Hoare_ASN_bop2:
  assumes 1:"weak_lens X"  and 2:"X \<sharp> exp1"
  shows "\<lbrace>bop P exp1 exp2\<rbrace>
          X:== exp2
         \<lbrace>bop P exp1 (VAR X)\<rbrace>" 
  using 1 2 unfolding subst_upd_var_def hoare_def unrest_def 
  by transfer auto

lemma Hoare_ASN_bop3:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>bop P exp1 \<guillemotleft>exp2\<guillemotright>\<rbrace>
          X:== exp1
         \<lbrace>bop P (VAR X) \<guillemotleft>exp2\<guillemotright>\<rbrace>" 
  using 1 unfolding subst_upd_var_def hoare_def  
  by transfer auto

lemma Hoare_ASN_bop4:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>bop P \<guillemotleft>exp1\<guillemotright> exp2\<rbrace>
          X:== exp2
         \<lbrace>bop P \<guillemotleft>exp1\<guillemotright> (VAR X)\<rbrace>" 
  using 1 unfolding subst_upd_var_def hoare_def  
  by transfer auto

lemma Hoare_ASN_trop1:
  assumes 1:"weak_lens X"  and 2:"X \<sharp> exp2" and 3:"X \<sharp> exp3"
  shows "\<lbrace>trop P exp1 exp2 exp3\<rbrace>
          X:== exp1
         \<lbrace>trop P (VAR X) exp2 exp3\<rbrace>" 
  using 1 2 3 unfolding subst_upd_var_def hoare_def unrest_def 
  by transfer auto

lemma Hoare_ASN_trop2:
  assumes 1:"weak_lens X"  and 2:"X \<sharp> exp1" and 3:"X \<sharp> exp3"
  shows "\<lbrace>trop P exp1 exp2 exp3\<rbrace>
          X:== exp2
         \<lbrace>trop P exp1 (VAR X) exp3\<rbrace>" 
  using 1 2 3 unfolding subst_upd_var_def hoare_def unrest_def 
  by transfer auto

lemma Hoare_ASN_trop3:
  assumes 1:"weak_lens X" and 2:"X \<sharp> exp1" and 3:"X \<sharp> exp2"
  shows "\<lbrace>trop P exp1 exp2 exp3\<rbrace> 
          X:== exp3
         \<lbrace>trop P exp1 exp2 (VAR X)\<rbrace>" 
  using 1 2 3 unfolding subst_upd_var_def hoare_def unrest_def 
  by transfer auto

lemma Hoare_ASN_trop4:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>trop P exp1 \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright>\<rbrace>
          X:== exp1
         \<lbrace>trop P (VAR X) \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright>\<rbrace>" 
  using 1  unfolding subst_upd_var_def hoare_def  
  by transfer auto

lemma Hoare_ASN_trop5:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>trop P \<guillemotleft>exp1\<guillemotright> exp2 \<guillemotleft>exp3\<guillemotright>\<rbrace>
          X:== exp2 
         \<lbrace>trop P \<guillemotleft>exp1\<guillemotright> (VAR X) \<guillemotleft>exp3\<guillemotright>\<rbrace>" 
  using 1  unfolding subst_upd_var_def hoare_def  
  by transfer auto

lemma Hoare_ASN_trop6:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>trop P \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> exp3\<rbrace>
          X:== exp3
         \<lbrace>trop P \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> (VAR X)\<rbrace>" 
  using 1  unfolding subst_upd_var_def hoare_def  
  by transfer auto

lemma Hoare_ASN_qtop1:
  assumes 1:"weak_lens X"  and 2:"X \<sharp> exp2" and 3:"X \<sharp> exp3"  and 4:"X \<sharp> exp4"
  shows "\<lbrace>qtop P exp1 exp2 exp3 exp4\<rbrace>
          X:== exp1
         \<lbrace>qtop P (VAR X) exp2 exp3 exp4\<rbrace>" 
  using 1 2 3 4unfolding subst_upd_var_def hoare_def unrest_def 
  by transfer auto

lemma Hoare_ASN_qtop2:
  assumes 1:"weak_lens X" and 2:"X \<sharp> exp1" and 3:"X \<sharp> exp3" and 4:"X \<sharp> exp4"
  shows "\<lbrace>qtop P exp1 exp2 exp3 exp4\<rbrace>
          X:== exp2
         \<lbrace>qtop P exp1 (VAR X) exp3 exp4\<rbrace>" 
  using 1 2 3 4 unfolding subst_upd_var_def hoare_def unrest_def 
  by transfer auto

lemma Hoare_ASN_qtop3:
  assumes 1:"weak_lens X" and 2:"X \<sharp> exp1" and 3:"X \<sharp> exp2" and 4:"X \<sharp> exp4"
  shows "\<lbrace>qtop P exp1 exp2 exp3 exp4\<rbrace>
          X:== exp3
         \<lbrace>qtop P exp1 exp2 (VAR X) exp4\<rbrace>" 
  using 1 2 3 4 unfolding subst_upd_var_def hoare_def unrest_def 
  by transfer auto

lemma Hoare_ASN_qtop4:
  assumes 1:"weak_lens X" and 2:"X \<sharp> exp1" and 3:"X \<sharp> exp2" and 4:"X \<sharp> exp3"
  shows "\<lbrace>qtop P exp1 exp2 exp3 exp4\<rbrace>
          X:== exp4
         \<lbrace>qtop P exp1 exp2 exp3 (VAR X)\<rbrace>" 
  using 1 2 3 4 unfolding subst_upd_var_def hoare_def unrest_def 
  by transfer auto

lemma Hoare_ASN_qtop5:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>qtop P exp1 \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>\<rbrace>
          X:== exp1
         \<lbrace>qtop P (VAR X) \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>\<rbrace> " 
  using 1 unfolding subst_upd_var_def hoare_def  
  by transfer auto

lemma Hoare_ASN_qtop6:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>qtop P \<guillemotleft>exp1\<guillemotright> exp2 \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>\<rbrace>
          X:== exp2
         \<lbrace>qtop P \<guillemotleft>exp1\<guillemotright> (VAR X) \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>\<rbrace>" 
  using 1  unfolding subst_upd_var_def hoare_def  
  by transfer auto

lemma Hoare_ASN_qtop7:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>qtop P \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> exp3 \<guillemotleft>exp4\<guillemotright>\<rbrace>
          X:== exp3
         \<lbrace>qtop P \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> (VAR X) \<guillemotleft>exp4\<guillemotright>\<rbrace>" 
  using 1  unfolding subst_upd_var_def hoare_def  
  by transfer auto

section {*Hoare for Sequential Composition*}

lemma Hoare_SEQ_uop:
  assumes 1:"\<lbrace>P\<rbrace>C1\<lbrace>Q\<rbrace>"  
  and     2:"\<lbrace>Q\<rbrace>C2\<lbrace>R\<rbrace>"
  shows "\<lbrace>P\<rbrace>C1;C2\<lbrace>R\<rbrace>" 
  using 1 2 unfolding hoare_def   
  by transfer (metis comp_apply)

section {*Hoare for Conditional*}

lemma Hoare_COND_uop:
  assumes 1:"\<lbrace>bop conj P b\<rbrace>C1\<lbrace>Q\<rbrace>"  
  and     2:"\<lbrace>bop conj P (uop Not b)\<rbrace>C2\<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace>IF b THEN C1 ELSE C2\<lbrace>Q\<rbrace>" 
  using 1 2 unfolding hoare_def 
  by transfer (metis (full_types, hide_lams))   

section {*Hoare for Consequence*}

lemma Hoare_CONSEQ:
  assumes 1:"(bop implies P' P) = \<guillemotleft>True\<guillemotright>"  
  and     2:"(bop implies Q Q') = \<guillemotleft>True\<guillemotright>"
  shows "\<lbrace>P\<rbrace>C\<lbrace>Q\<rbrace> \<longrightarrow> \<lbrace>P'\<rbrace>C\<lbrace>Q'\<rbrace>" 
  using 1 2  unfolding hoare_def
  by transfer meson 

section {*Hoare for While-loop*}

lemma Hoare_COND_uop:
  assumes 1:"\<lbrace>bop conj P b\<rbrace>C\<lbrace>P\<rbrace>"  
  shows "\<lbrace>P\<rbrace>WHILE b DO C OD\<lbrace>bop conj P (uop Not b)\<rbrace>" 
  using 1 unfolding hoare_def RelInv_def Rel_def W_def
oops  



 

end