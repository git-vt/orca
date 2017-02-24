section{*Hoare Logic*}

theory Hoare
imports Algebraic_Laws

begin

subsection {*Examples*}

text {*In this section we introduce small examples showing how can use the tools from the lens 
       theory to represent a Hoare triple*}

named_theorems hoare_partial and vcg

lemma Hoare_test1:
  assumes 1:"weak_lens Y"
  shows"\<lceil>(VAR X) =\<^sub>e \<guillemotleft>1::int\<guillemotright> \<longrightarrow>\<^sub>e (Y :== (VAR X)) \<dagger> (VAR Y) =\<^sub>e \<guillemotleft>1::int\<guillemotright>\<rceil>"
  using 1 unfolding subst_upd_var_def
  by transfer auto

lemma Hoare_test2:
  assumes 1:"weak_lens Y" and 2:"X \<bowtie> Y"
  shows"\<lceil>(VAR X) =\<^sub>e \<guillemotleft>1::int\<guillemotright> \<longrightarrow>\<^sub>e (Y :== (VAR X))\<dagger> (VAR Y) =\<^sub>e \<guillemotleft>2::int\<guillemotright>\<rceil> "
  using 1 2 unfolding subst_upd_var_def lens_indep_def
  apply transfer 
  apply auto oops

lemma Hoare_test3:
  assumes 1:"vwb_lens Y" and  2:"vwb_lens X" and 3:"vwb_lens R"
  and     4:"X \<bowtie> Y"     and  5:"X \<bowtie> R"     and 6:"Y\<bowtie> R"
  shows "\<lceil>(VAR X) =\<^sub>e \<guillemotleft>1::int\<guillemotright> \<and>\<^sub>e (VAR Y) =\<^sub>e \<guillemotleft>2::int\<guillemotright> \<longrightarrow>\<^sub>e
          (R:== (VAR X) ; X :== (VAR Y); Y:== (VAR R))\<dagger>((VAR X) =\<^sub>e \<guillemotleft>2::int\<guillemotright> \<and>\<^sub>e (VAR Y) =\<^sub>e \<guillemotleft>1::int\<guillemotright>)\<rceil>"
  using assms unfolding subst_upd_var_def id_def lens_indep_def 
  by transfer auto 

lemma Hoare_test4:
  assumes 1:"weak_lens Y" and 2:"weak_lens X" and 3:"weak_lens R"
  and     4:"X \<bowtie> Y" and 5:"X \<bowtie> R" and 6:"Y\<bowtie> R"
  shows "\<lceil>(VAR X) =\<^sub>e \<guillemotleft>x\<guillemotright> \<and>\<^sub>e (VAR Y) =\<^sub>e \<guillemotleft>y\<guillemotright>  \<longrightarrow>\<^sub>e
         (R:== (VAR X) ; X :== (VAR Y); Y:== (VAR R))\<dagger>((VAR X) =\<^sub>e\<guillemotleft>y\<guillemotright> \<and>\<^sub>e (VAR Y) =\<^sub>e \<guillemotleft>x\<guillemotright>)\<rceil>"
  using assms unfolding subst_upd_var_def id_def lens_indep_def
  by transfer auto

subsection {*Hoare triple definition*}
text {*A Hoare triple is represented by a pre-condition @{text P} a post-condition @{text Q}
       and a program @{text C}. It says whenever the pre-condition @{text P} holds then the post-condition
       @{text Q} must hold after the execution of the program @{text C}.*}

abbreviation hoare :: "(bool ,  '\<alpha>) expr \<Rightarrow> '\<alpha> states \<Rightarrow> (bool ,  '\<alpha>) expr \<Rightarrow>  bool" ("\<lbrace>(1_)\<rbrace>/ (_)/\<lbrace>(1_)\<rbrace>") where
"\<lbrace>P\<rbrace>C\<lbrace>Q\<rbrace> \<equiv> \<lceil>P \<longrightarrow>\<^sub>e (C \<dagger> Q)\<rceil>"

lift_definition hoare_valid :: "(bool ,  '\<alpha>) expr \<Rightarrow> '\<alpha> states \<Rightarrow> (bool ,  '\<alpha>) expr \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) is
"\<lambda>P C Q. (\<forall> \<sigma> \<sigma>'. P \<sigma> \<and> C \<sigma> = \<sigma>' \<longrightarrow> Q \<sigma>')" .

text \<open>For proof automation, using an Eisbach method to compose transfer and simp/auto rules. Proving
more complex Hoare triples will involve recursive theorem matching using ML-level tactics.\<close>
method hoare_solver = transfer, (simp_all|auto)

lemma Hoare_eq:"\<Turnstile> {P}C{Q} = \<lbrace>P\<rbrace>C\<lbrace>Q\<rbrace>"
  by hoare_solver

lemma Hoare_True [hoare_partial,vcg]: "\<lbrace>P\<rbrace>C\<lbrace>TRUE\<rbrace>"
  by hoare_solver

lemma Hoare_False [hoare_partial,vcg]: "\<lbrace>FALSE\<rbrace>C\<lbrace>Q\<rbrace>"
  by hoare_solver

subsection {*Hoare for Consequence*}

lemma Hoare_CONSEQ[hoare_partial]:
  assumes 1:"\<lceil>P' \<longrightarrow>\<^sub>e P\<rceil>"  
  and     2:"\<lceil>Q \<longrightarrow>\<^sub>e Q'\<rceil>"
  shows "\<lbrace>P\<rbrace>C\<lbrace>Q\<rbrace> \<longrightarrow> \<lbrace>P'\<rbrace>C\<lbrace>Q'\<rbrace>" 
  using 1 2 by hoare_solver

subsection {*Precondition strengthening*}

lemma Hoare_Pre_Str[hoare_partial]:
  assumes 1:"\<lceil>P \<longrightarrow>\<^sub>e P'\<rceil>"
  and     2:"\<lbrace>P'\<rbrace>C\<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace>C\<lbrace>Q\<rbrace>" 
  using 1 2 by hoare_solver

subsection {*Postcondition weakening*}

lemma Hoare_Post_weak[hoare_partial]:
  assumes 1:"\<lbrace>P\<rbrace>C\<lbrace>Q'\<rbrace>"  
  and     2:"\<lceil>Q'\<longrightarrow>\<^sub>e Q\<rceil>"
  shows "\<lbrace>P\<rbrace>C\<lbrace>Q\<rbrace>" 
  using 1 2 
  by hoare_solver

subsection {*Hoare and assertion logic*}

lemma Hoare_conjI[hoare_partial,vcg]:
  assumes 1:"\<lbrace>P1\<rbrace>C\<lbrace>Q1\<rbrace>"  
  and     2:"\<lbrace>P2\<rbrace>C\<lbrace>Q2\<rbrace>"
  shows "\<lbrace>P1 \<and>\<^sub>e P2\<rbrace>C\<lbrace>Q1 \<and>\<^sub>e Q2\<rbrace>" 
  using 1 2 by hoare_solver

lemma Hoare_disjI[hoare_partial,vcg]:
  assumes 1:"\<lbrace>P1\<rbrace>C\<lbrace>Q1\<rbrace>"  
  and     2:"\<lbrace>P2\<rbrace>C\<lbrace>Q2\<rbrace>"
  shows "\<lbrace>P1 \<or>\<^sub>e P2\<rbrace>C\<lbrace>Q1 \<or>\<^sub>e Q2\<rbrace>"
  using 1 2 by hoare_solver
 
subsection {*Hoare for SKIP*}

lemma Hoare_SKIP[hoare_partial,vcg]: "\<lbrace>P\<rbrace>SKIP\<lbrace>P\<rbrace>"
   by hoare_solver

subsection {*Hoare for assignment*}

lemma Hoare_ASN[hoare_partial,vcg]: "\<lbrace>[X \<mapsto>\<^sub>s exp] \<dagger> P\<rbrace>X:== exp\<lbrace>P\<rbrace>" (*I a, not sure if this make sens...*)
  unfolding subst_upd_var_def 
  by hoare_solver

lemma Floyd_ASN[hoare_partial]: 
  assumes 1:"weak_lens X" and 2:"weak_lens v" and 3:"X \<bowtie> v" and 4:"v \<sharp> P" and 5:"v \<sharp> exp" 
  shows "\<lbrace>P\<rbrace>X:== exp\<lbrace>\<exists>\<^sub>e v . ((VAR X) =\<^sub>e([X \<mapsto>\<^sub>s (VAR v)]\<dagger> exp)) \<and>\<^sub>e ([X \<mapsto>\<^sub>s (VAR v)]\<dagger> P)\<rbrace>" 
  using assms unfolding subst_upd_var_def  lens_indep_def
  apply simp apply hoare_solver oops

lemma Hoare_ASN1[hoare_partial,vcg]:
  assumes 1:"weak_lens X" and 2:"X\<sharp> E"
  shows "\<lbrace>TRUE\<rbrace> X:== E \<lbrace>(VAR X) =\<^sub>e E\<rbrace>"
  using 2 1 unfolding subst_upd_var_def unrest_def
  by hoare_solver

lemma  Hoare_ASN_bop_test[hoare_partial]:
  assumes 1:"weak_lens Y"  
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>1\<guillemotright>\<rbrace>
          Y:== (VAR X)
         \<lbrace>(VAR Y) =\<^sub>e \<guillemotleft>1\<guillemotright>\<rbrace>"
  using 1 unfolding subst_upd_var_def 
  by hoare_solver 
 
lemma Hoare_ASN_uop1[hoare_partial,vcg]:
  assumes 1:"weak_lens X"  
  shows "\<lbrace>uop P exp\<rbrace>
          X:== exp
         \<lbrace>uop P (VAR X)\<rbrace>" 
  using 1 unfolding subst_upd_var_def    
  by hoare_solver 

lemma Hoare_ASN_uop2[hoare_partial,vcg]:
  assumes 1:"weak_lens X" and 2:"X \<sharp> exp"
  shows "\<lbrace>uop P exp\<rbrace>
          X:== x
         \<lbrace>uop P exp\<rbrace>"
  using 1 2 unfolding subst_upd_var_def unrest_def
  by hoare_solver 

lemma Hoare_ASN_uop3[hoare_partial,vcg]:
  assumes 1:"weak_lens X"
  shows "\<lbrace>uop P \<guillemotleft>exp\<guillemotright>\<rbrace>
          X:== x
         \<lbrace>uop P \<guillemotleft>exp\<guillemotright>\<rbrace>"
  using 1 unfolding subst_upd_var_def unrest_def
  by hoare_solver

lemma Hoare_ASN_uop4[hoare_partial,vcg]:
  assumes 1:"weak_lens X" and 2: "X \<sharp> P"
  shows "\<lbrace>P\<rbrace>X:== exp\<lbrace>P\<rbrace>"
  using 1 2 unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_Const_test:
  assumes 1:"weak_lens X" and 2:"X \<bowtie> Y"
  shows "\<lbrace>(VAR Y) =\<^sub>e \<guillemotleft>2\<guillemotright>\<rbrace>X:== \<guillemotleft>2::int\<guillemotright>\<lbrace>(VAR Y) =\<^sub>e(VAR X)\<rbrace>" 
  using 1 2 unfolding subst_upd_var_def lens_indep_def
  by hoare_solver

lemma Hoare_ASN_bop1[hoare_partial,vcg]:
  assumes 1:"weak_lens X" and 2:"X \<sharp> exp2"
  shows "\<lbrace>bop P exp1 exp2\<rbrace>
          X:== exp1
         \<lbrace>bop P (VAR X) exp2\<rbrace>" 
  using 1 2 unfolding subst_upd_var_def unrest_def 
  by hoare_solver

lemma Hoare_ASN_bop2[hoare_partial,vcg]:
  assumes 1:"weak_lens X" and 2:"X \<sharp> exp1"
  shows "\<lbrace>bop P exp1 exp2\<rbrace>
          X:== exp2
         \<lbrace>bop P exp1 (VAR X)\<rbrace>" 
  using 1 2 unfolding subst_upd_var_def unrest_def 
  by hoare_solver

lemma Hoare_ASN_bop3[hoare_partial,vcg]:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>bop P exp1 \<guillemotleft>exp2\<guillemotright>\<rbrace>
          X:== exp1
         \<lbrace>bop P (VAR X) \<guillemotleft>exp2\<guillemotright>\<rbrace>" 
  using 1 unfolding subst_upd_var_def   
  by hoare_solver

lemma Hoare_ASN_bop4[hoare_partial,vcg]:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>bop P \<guillemotleft>exp1\<guillemotright> exp2\<rbrace>
          X:== exp2
         \<lbrace>bop P \<guillemotleft>exp1\<guillemotright> (VAR X)\<rbrace>" 
  using 1 unfolding subst_upd_var_def   
  by hoare_solver

lemma Hoare_ASN_bop5[hoare_partial,vcg]:
  assumes 1:"weak_lens X" and 2:"X \<bowtie> Y"
  shows "\<lbrace>bop P (VAR Y) exp2\<rbrace>
          X:== exp2
         \<lbrace>bop P (VAR Y) (VAR X)\<rbrace>" 
  using 1 2 unfolding subst_upd_var_def lens_indep_def
  by hoare_solver

lemma Hoare_ASN_trop1[hoare_partial,vcg]:
  assumes 1:"weak_lens X"  and 2:"X \<sharp> exp2" and 3:"X \<sharp> exp3"
  shows "\<lbrace>trop P exp1 exp2 exp3\<rbrace>
          X:== exp1
         \<lbrace>trop P (VAR X) exp2 exp3\<rbrace>" 
  using 1 2 3 unfolding subst_upd_var_def unrest_def 
  by hoare_solver

lemma Hoare_ASN_trop2[hoare_partial,vcg]:
  assumes 1:"weak_lens X"  and 2:"X \<sharp> exp1" and 3:"X \<sharp> exp3"
  shows "\<lbrace>trop P exp1 exp2 exp3\<rbrace>
          X:== exp2
         \<lbrace>trop P exp1 (VAR X) exp3\<rbrace>" 
  using 1 2 3 unfolding subst_upd_var_def unrest_def 
  by hoare_solver

lemma Hoare_ASN_trop3[hoare_partial,vcg]:
  assumes 1:"weak_lens X" and 2:"X \<sharp> exp1" and 3:"X \<sharp> exp2"
  shows "\<lbrace>trop P exp1 exp2 exp3\<rbrace> 
          X:== exp3
         \<lbrace>trop P exp1 exp2 (VAR X)\<rbrace>" 
  using 1 2 3 unfolding subst_upd_var_def unrest_def 
  by hoare_solver

lemma Hoare_ASN_trop4[hoare_partial,vcg]:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>trop P exp1 \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright>\<rbrace>
          X:== exp1
         \<lbrace>trop P (VAR X) \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright>\<rbrace>" 
  using 1 unfolding subst_upd_var_def   
  by hoare_solver

lemma Hoare_ASN_trop5[hoare_partial,vcg]:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>trop P \<guillemotleft>exp1\<guillemotright> exp2 \<guillemotleft>exp3\<guillemotright>\<rbrace>
          X:== exp2 
         \<lbrace>trop P \<guillemotleft>exp1\<guillemotright> (VAR X) \<guillemotleft>exp3\<guillemotright>\<rbrace>" 
  using 1 unfolding subst_upd_var_def   
  by hoare_solver

lemma Hoare_ASN_trop6[hoare_partial,vcg]:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>trop P \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> exp3\<rbrace>
          X:== exp3
         \<lbrace>trop P \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> (VAR X)\<rbrace>" 
  using 1 unfolding subst_upd_var_def   
  by hoare_solver

lemma Hoare_ASN_qtop1[hoare_partial,vcg]:
  assumes 1:"weak_lens X"  and 2:"X \<sharp> exp2" and 3:"X \<sharp> exp3"  and 4:"X \<sharp> exp4"
  shows "\<lbrace>qtop P exp1 exp2 exp3 exp4\<rbrace>
          X:== exp1
         \<lbrace>qtop P (VAR X) exp2 exp3 exp4\<rbrace>" 
  using 1 2 3 4 unfolding subst_upd_var_def unrest_def 
  by hoare_solver

lemma Hoare_ASN_qtop2[hoare_partial,vcg]:
  assumes 1:"weak_lens X" and 2:"X \<sharp> exp1" and 3:"X \<sharp> exp3" and 4:"X \<sharp> exp4"
  shows "\<lbrace>qtop P exp1 exp2 exp3 exp4\<rbrace>
          X:== exp2
         \<lbrace>qtop P exp1 (VAR X) exp3 exp4\<rbrace>" 
  using 1 2 3 4 unfolding subst_upd_var_def unrest_def 
  by hoare_solver

lemma Hoare_ASN_qtop3[hoare_partial,vcg]:
  assumes 1:"weak_lens X" and 2:"X \<sharp> exp1" and 3:"X \<sharp> exp2" and 4:"X \<sharp> exp4"
  shows "\<lbrace>qtop P exp1 exp2 exp3 exp4\<rbrace>
          X:== exp3
         \<lbrace>qtop P exp1 exp2 (VAR X) exp4\<rbrace>" 
  using 1 2 3 4 unfolding subst_upd_var_def unrest_def 
  by hoare_solver

lemma Hoare_ASN_qtop4[hoare_partial,vcg]:
  assumes 1:"weak_lens X" and 2:"X \<sharp> exp1" and 3:"X \<sharp> exp2" and 4:"X \<sharp> exp3"
  shows "\<lbrace>qtop P exp1 exp2 exp3 exp4\<rbrace>
          X:== exp4
         \<lbrace>qtop P exp1 exp2 exp3 (VAR X)\<rbrace>" 
  using 1 2 3 4 unfolding subst_upd_var_def unrest_def 
  by hoare_solver

lemma Hoare_ASN_qtop5[hoare_partial,vcg]:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>qtop P exp1 \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>\<rbrace>
          X:== exp1
         \<lbrace>qtop P (VAR X) \<guillemotleft>exp2\<guillemotright> \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>\<rbrace> " 
  using 1 unfolding subst_upd_var_def   
  by hoare_solver

lemma Hoare_ASN_qtop6[hoare_partial,vcg]:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>qtop P \<guillemotleft>exp1\<guillemotright> exp2 \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>\<rbrace>
          X:== exp2
         \<lbrace>qtop P \<guillemotleft>exp1\<guillemotright> (VAR X) \<guillemotleft>exp3\<guillemotright> \<guillemotleft>exp4\<guillemotright>\<rbrace>" 
  using 1 unfolding subst_upd_var_def   
  by hoare_solver

lemma Hoare_ASN_qtop7[hoare_partial,vcg]:
  assumes 1:"weak_lens X" 
  shows "\<lbrace>qtop P \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> exp3 \<guillemotleft>exp4\<guillemotright>\<rbrace>
          X:== exp3
         \<lbrace>qtop P \<guillemotleft>exp1\<guillemotright> \<guillemotleft>exp2\<guillemotright> (VAR X) \<guillemotleft>exp4\<guillemotright>\<rbrace>" 
  using 1 unfolding subst_upd_var_def  
  by hoare_solver

subsection \<open>Hoare for Assignment with Equality\<close>

lemma Hoare_ASN_EQ1[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp"
  shows "\<lbrace>P\<rbrace>
          X :== exp
         \<lbrace>(VAR X) =\<^sub>e exp\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ2[hoare_partial,vcg]:
  assumes "weak_lens X"
  shows "\<lbrace>P\<rbrace>
          X :== \<guillemotleft>exp\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

subsubsection \<open>Assignment of Unary Operations\<close>

lemma Hoare_ASN_EQ_uop1[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp"
  shows "\<lbrace>P\<rbrace>
          X :== uop Q exp
         \<lbrace>(VAR X) =\<^sub>e uop Q exp\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_uop1x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "exp\<^sub>2 = uop Q exp\<^sub>1"
  shows "\<lbrace>P\<rbrace>
          X :== uop Q exp\<^sub>1
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_uop2[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1"
  shows "\<lbrace>exp\<^sub>2 =\<^sub>e exp\<^sub>1\<rbrace>
          X :== uop Q exp\<^sub>2
         \<lbrace>(VAR X) =\<^sub>e uop Q exp\<^sub>1\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_uop2x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "exp\<^sub>3 = uop Q exp\<^sub>1"
  shows "\<lbrace>exp\<^sub>2 =\<^sub>e exp\<^sub>1\<rbrace>
          X :== uop Q exp\<^sub>2
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_uop3[hoare_partial,vcg]:
  assumes "weak_lens X"
  shows "\<lbrace>P\<rbrace>
          X :== uop Q \<guillemotleft>exp\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e uop Q \<guillemotleft>exp\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_uop3x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "\<lceil>\<guillemotleft>exp\<^sub>2\<guillemotright> =\<^sub>e uop Q \<guillemotleft>exp\<^sub>1\<guillemotright>\<rceil>"
  shows "\<lbrace>P\<rbrace>
          X :== uop Q \<guillemotleft>exp\<^sub>1\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_uop4[hoare_partial,vcg]:
  assumes "weak_lens X"
  shows "\<lbrace>exp\<^sub>1 =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== uop Q exp\<^sub>1
         \<lbrace>(VAR X) =\<^sub>e uop Q \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_uop4x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "\<lceil>\<guillemotleft>exp\<^sub>3\<guillemotright> =\<^sub>e uop Q \<guillemotleft>exp\<^sub>2\<guillemotright>\<rceil>"
  shows "\<lbrace>exp\<^sub>1 =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== uop Q exp\<^sub>1
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_uop5[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" (* Weird that the unrest is required *)
  shows "\<lbrace>exp\<^sub>1 =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== uop Q \<guillemotleft>exp\<^sub>2\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e uop Q exp\<^sub>1\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_uop5x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "exp\<^sub>3 = uop Q exp\<^sub>1"
  shows "\<lbrace>exp\<^sub>1 =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== uop Q \<guillemotleft>exp\<^sub>2\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_uop6[hoare_partial,vcg]:
  assumes "weak_lens X"
  shows "\<lbrace>\<guillemotleft>exp\<^sub>1\<guillemotright> =\<^sub>e exp\<^sub>2\<rbrace>
          X :== uop Q exp\<^sub>2
         \<lbrace>(VAR X) =\<^sub>e uop Q \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_uop6x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "exp\<^sub>3 = uop Q \<guillemotleft>exp\<^sub>1\<guillemotright>"
  shows "\<lbrace>\<guillemotleft>exp\<^sub>1\<guillemotright> =\<^sub>e exp\<^sub>2\<rbrace>
          X :== uop Q exp\<^sub>2
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

subsubsection \<open>Assignment of Binary Operations\<close>

lemma Hoare_ASN_EQ_bop1[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== bop Q (VAR X) exp\<^sub>2
         \<lbrace>(VAR X) =\<^sub>e bop Q exp\<^sub>1 exp\<^sub>2\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop1x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "exp\<^sub>3 = bop Q exp\<^sub>1 exp\<^sub>2"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== bop Q (VAR X) exp\<^sub>2
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop2[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>2"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== bop Q (VAR X) exp\<^sub>2
         \<lbrace>(VAR X) =\<^sub>e bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop2x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>2"
      and "exp\<^sub>3 = bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== bop Q (VAR X) exp\<^sub>2
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop3[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== bop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e bop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop3x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "exp\<^sub>3 = bop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== bop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop4[hoare_partial,vcg]:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== bop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop4x[hoare_partial,vcg]:
  assumes "weak_lens X"
  and "\<lceil>\<guillemotleft>exp\<^sub>3\<guillemotright> =\<^sub>e bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright>\<rceil>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== bop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop4y[hoare_partial,vcg]:
  assumes "weak_lens X"
  and "exp\<^sub>3 = bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== bop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop5[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== bop Q exp\<^sub>1 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e bop Q exp\<^sub>1 exp\<^sub>2\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop5x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "exp\<^sub>3 = bop Q exp\<^sub>1 exp\<^sub>2"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== bop Q exp\<^sub>1 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop6[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== bop Q exp\<^sub>1 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e bop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop6x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "exp\<^sub>3 = bop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== bop Q exp\<^sub>1 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop7[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>2"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop7x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>2"
      and "exp\<^sub>3 = bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop8[hoare_partial,vcg]:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop8x[hoare_partial,vcg]:
  assumes "weak_lens X"
  and "\<lceil>\<guillemotleft>exp\<^sub>3\<guillemotright> =\<^sub>e bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright>\<rceil>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_bop8y[hoare_partial,vcg]:
  assumes "weak_lens X"
  and "exp\<^sub>3 = bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== bop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

subsubsection \<open>Assignment of Ternary Operations\<close>

lemma Hoare_ASN_EQ_trop1[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== trop Q (VAR X) exp\<^sub>2 exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e trop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop1x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>4 = trop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== trop Q (VAR X) exp\<^sub>2 exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop2[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== trop Q (VAR X) exp\<^sub>2 exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop2x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>4 = trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== trop Q (VAR X) exp\<^sub>2 exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop3[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== trop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop3x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>4 = trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== trop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop4[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== trop Q (VAR X) exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e trop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop4x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "exp\<^sub>4 = trop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== trop Q (VAR X) exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop5[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== trop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop5x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>4 = trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== trop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop6[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== trop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop6x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "exp\<^sub>4 = trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== trop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop7[hoare_partial,vcg]:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== trop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop7x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "\<lceil>\<guillemotleft>exp\<^sub>4\<guillemotright> =\<^sub>e trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>\<rceil>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== trop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop7y[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "exp\<^sub>4 = trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== trop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop8[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== trop Q exp\<^sub>1 (VAR X) exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e trop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop8x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>4 = trop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== trop Q exp\<^sub>1 (VAR X) exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop9[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X) exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop9x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>4 = trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X) exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop10[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== trop Q exp\<^sub>1 (VAR X) exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop10x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>4 = trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== trop Q exp\<^sub>1 (VAR X) exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop11[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== trop Q exp\<^sub>1 (VAR X) \<guillemotleft>exp\<^sub>3\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e trop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop11x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "exp\<^sub>4 = trop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== trop Q exp\<^sub>1 (VAR X) \<guillemotleft>exp\<^sub>3\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop12[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X) exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop12x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>4 = trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X) exp\<^sub>3
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop13[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== trop Q exp\<^sub>1 (VAR X) \<guillemotleft>exp\<^sub>3\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop13x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "exp\<^sub>4 = trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== trop Q exp\<^sub>1 (VAR X) \<guillemotleft>exp\<^sub>3\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop14[hoare_partial,vcg]:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X) \<guillemotleft>exp\<^sub>3\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop14x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "\<lceil>\<guillemotleft>exp\<^sub>4\<guillemotright> =\<^sub>e trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>\<rceil>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X) \<guillemotleft>exp\<^sub>3\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop14y[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "exp\<^sub>4 = trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X) \<guillemotleft>exp\<^sub>3\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop15[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== trop Q exp\<^sub>1 exp\<^sub>2 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e trop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop15x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>4 = trop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== trop Q exp\<^sub>1 exp\<^sub>2 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop16[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop16x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>4 = trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop17[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop17x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>4 = trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop18[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>
          X :== trop Q exp\<^sub>1 exp\<^sub>2 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e trop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop18x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "exp\<^sub>4 = trop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>
          X :== trop Q exp\<^sub>1 exp\<^sub>2 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop19[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop19x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>4 = trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop20[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>
          X :== trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop20x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "exp\<^sub>4 = trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>
          X :== trop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop21[hoare_partial,vcg]:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>
          X :== trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop21x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "\<lceil>\<guillemotleft>exp\<^sub>4\<guillemotright> =\<^sub>e trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>\<rceil>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>
          X :== trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_trop21y[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "exp\<^sub>4 = trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>
          X :== trop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

subsubsection \<open>Assignment of Quaternary Operations\<close>
text \<open>There are, unfortunately, too many combinations of const/non-const lemmas for quaternary
operations to reasonably list here, but a decent number of possibilities have been included.\<close>

lemma Hoare_ASN_EQ_qtop1[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== qtop Q (VAR X) exp\<^sub>2 exp\<^sub>3 exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop1x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== qtop Q (VAR X) exp\<^sub>2 exp\<^sub>3 exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop2[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== qtop Q (VAR X) exp\<^sub>2 exp\<^sub>3 exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3 exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop2x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3 exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== qtop Q (VAR X) exp\<^sub>2 exp\<^sub>3 exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop3[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>3" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== qtop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3 exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3 exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop3x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>3"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3 exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== qtop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3 exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop4[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== qtop Q (VAR X) exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright> exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright> exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop4x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== qtop Q (VAR X) exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright> exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop5[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== qtop Q (VAR X) exp\<^sub>2 exp\<^sub>3 \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop5x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 \<guillemotleft>exp\<^sub>4\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>1\<rbrace>
          X :== qtop Q (VAR X) exp\<^sub>2 exp\<^sub>3 \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop6[hoare_partial,vcg]:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== qtop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop6x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "\<lceil>\<guillemotleft>exp\<^sub>5\<guillemotright> =\<^sub>e qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>\<rceil>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== qtop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>5\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop6y[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "exp\<^sub>5 = qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>1\<guillemotright>\<rbrace>
          X :== qtop Q (VAR X) \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop7[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== qtop Q exp\<^sub>1 (VAR X) exp\<^sub>3 exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop7x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== qtop Q exp\<^sub>1 (VAR X) exp\<^sub>3 exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop8[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X) exp\<^sub>3 exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3 exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop8x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3 exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X) exp\<^sub>3 exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop9[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>3" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== qtop Q exp\<^sub>1 (VAR X) exp\<^sub>3 exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3 exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop9x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>3"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3 exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== qtop Q exp\<^sub>1 (VAR X) exp\<^sub>3 exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop10[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== qtop Q exp\<^sub>1 (VAR X) \<guillemotleft>exp\<^sub>3\<guillemotright> exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright> exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop10x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== qtop Q exp\<^sub>1 (VAR X) \<guillemotleft>exp\<^sub>3\<guillemotright> exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop11[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== qtop Q exp\<^sub>1 (VAR X) exp\<^sub>3 \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop11x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 \<guillemotleft>exp\<^sub>4\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>2\<rbrace>
          X :== qtop Q exp\<^sub>1 (VAR X) exp\<^sub>3 \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop12[hoare_partial,vcg]:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X) \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop12x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "\<lceil>\<guillemotleft>exp\<^sub>5\<guillemotright> =\<^sub>e qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>\<rceil>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X) \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>5\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop12y[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "exp\<^sub>5 = qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>2\<guillemotright>\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> (VAR X) \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop13[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== qtop Q exp\<^sub>1 exp\<^sub>2 (VAR X) exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop13x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== qtop Q exp\<^sub>1 exp\<^sub>2 (VAR X) exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop14[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 (VAR X) exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3 exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop14x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3 exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 (VAR X) exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop15[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>3" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== qtop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> (VAR X) exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3 exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop15x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>3"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3 exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== qtop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> (VAR X) exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop16[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>
          X :== qtop Q exp\<^sub>1 exp\<^sub>2 (VAR X) exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright> exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop16x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>
          X :== qtop Q exp\<^sub>1 exp\<^sub>2 (VAR X) exp\<^sub>4
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop17[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== qtop Q exp\<^sub>1 exp\<^sub>2 (VAR X) \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop17x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 \<guillemotleft>exp\<^sub>4\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>3\<rbrace>
          X :== qtop Q exp\<^sub>1 exp\<^sub>2 (VAR X) \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop18[hoare_partial,vcg]:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> (VAR X) \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop18x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "\<lceil>\<guillemotleft>exp\<^sub>5\<guillemotright> =\<^sub>e qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>\<rceil>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> (VAR X) \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>5\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop18y[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "exp\<^sub>5 = qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>3\<guillemotright>\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> (VAR X) \<guillemotleft>exp\<^sub>4\<guillemotright>
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop19[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>
          X :== qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop19x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>
          X :== qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop20[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3 exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop20x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3 exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> exp\<^sub>2 exp\<^sub>3 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop21[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>3" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>
          X :== qtop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3 exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop21x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>3"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3 exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>
          X :== qtop Q exp\<^sub>1 \<guillemotleft>exp\<^sub>2\<guillemotright> exp\<^sub>3 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop22[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>
          X :== qtop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright> exp\<^sub>4\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop22x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>4"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright> exp\<^sub>4"
  shows "\<lbrace>(VAR X) =\<^sub>e exp\<^sub>4\<rbrace>
          X :== qtop Q exp\<^sub>1 exp\<^sub>2 \<guillemotleft>exp\<^sub>3\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop23[hoare_partial,vcg]:
  assumes "weak_lens X" and "X \<sharp> exp\<^sub>1" and "X \<sharp> exp\<^sub>2" and "X \<sharp> exp\<^sub>3"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>
          X :== qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop23x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "X \<sharp> exp\<^sub>1"
      and "X \<sharp> exp\<^sub>2"
      and "X \<sharp> exp\<^sub>3"
      and "exp\<^sub>5 = qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 \<guillemotleft>exp\<^sub>4\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>
          X :== qtop Q exp\<^sub>1 exp\<^sub>2 exp\<^sub>3 (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop24[hoare_partial,vcg]:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop24x[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "\<lceil>\<guillemotleft>exp\<^sub>5\<guillemotright> =\<^sub>e qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>\<rceil>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>5\<guillemotright>\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

lemma Hoare_ASN_EQ_qtop24y[hoare_partial,vcg]:
  assumes "weak_lens X"
      and "exp\<^sub>5 = qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> \<guillemotleft>exp\<^sub>4\<guillemotright>"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>exp\<^sub>4\<guillemotright>\<rbrace>
          X :== qtop Q \<guillemotleft>exp\<^sub>1\<guillemotright> \<guillemotleft>exp\<^sub>2\<guillemotright> \<guillemotleft>exp\<^sub>3\<guillemotright> (VAR X)
         \<lbrace>(VAR X) =\<^sub>e exp\<^sub>5\<rbrace>"
  using assms unfolding subst_upd_var_def
  by hoare_solver

(* We will use match_tac to enhance performance for the ASN_EQ lemmas, apparently, and eventually
want to move beyond just using (VAR X) =\<^sub>e [whatever] as the precondition. *)

subsection {*Hoare for Sequential Composition*}

lemma Hoare_SEQ[hoare_partial,vcg]:
  assumes 1:"\<lbrace>P\<rbrace>C1\<lbrace>Q\<rbrace>"  
  and     2:"\<lbrace>Q\<rbrace>C2\<lbrace>R\<rbrace>"
  shows "\<lbrace>P\<rbrace>C1;C2\<lbrace>R\<rbrace>" 
  using 1 2 
  by hoare_solver

subsection {*Hoare for Conditional*}

lemma Hoare_COND[hoare_partial,vcg]:
  assumes 1:"\<lbrace>P \<and>\<^sub>e b\<rbrace>C1\<lbrace>Q\<rbrace>"  
  and     2:"\<lbrace> P \<and>\<^sub>e (\<not>\<^sub>e b)\<rbrace>C2\<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace>IF b THEN C1 ELSE C2\<lbrace>Q\<rbrace>" 
  using 1 2 
  by hoare_solver  

subsection {*Hoare for While-loop*}

lemma Hoare_WHILE[hoare_partial,vcg]:
  assumes 1:"\<lbrace>P \<and>\<^sub>e b\<rbrace>C\<lbrace>P\<rbrace>"  
  shows "\<lbrace>P\<rbrace>WHILE b DO C OD\<lbrace>P \<and>\<^sub>e (\<not>\<^sub>eb)\<rbrace>" 
  using 1
  apply transfer
sorry  

subsection \<open>Weakest Precondition\<close>
lift_definition wp :: "'\<alpha> states \<Rightarrow> (bool, '\<alpha>) expr \<Rightarrow> (bool, '\<alpha>) expr" is
  "\<lambda>c Q \<sigma>. \<forall>\<sigma>'. c \<sigma> = \<sigma>' \<longrightarrow> Q \<sigma>'" .

named_theorems wps

lemma wp_SKIP[wps]: "wp SKIP Q = Q"
  by hoare_solver

lemma wp_Ass[wps]: "wp (X :== exp) Q = [X \<mapsto>\<^sub>s exp] \<dagger> Q"
  by hoare_solver

lemma wp_Seq[wps]: "wp (c\<^sub>1; c\<^sub>2) Q = wp c\<^sub>1 (wp c\<^sub>2 Q)"
  by hoare_solver

lemma wp_If[wps]: "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q = (\<lambda>\<sigma>. if b \<sigma> then wp c\<^sub>1 Q \<sigma> else wp c\<^sub>2 Q \<sigma>)"
  by hoare_solver

lemma wp_While_If: "wp (WHILE b DO c OD) Q \<sigma> = wp (IF b THEN c;WHILE b DO c OD ELSE SKIP) Q \<sigma>"
  apply hoare_solver
  oops

lemma wp_While_True[wps]:
  assumes "b \<sigma>"
  shows "wp (WHILE b DO c OD) Q \<sigma> = wp (c; WHILE b DO c OD) Q \<sigma>"
  using assms wp_While_If
  apply hoare_solver
  oops

lemma wp_While_False[wps]:
  assumes "\<not> b \<sigma>"
  shows "wp (WHILE b DO c OD) Q \<sigma> = Q \<sigma>"
  using assms wp_While_If
  apply hoare_solver
  oops

lemma wp_is_pre[wps]: "\<lbrace>wp c Q\<rbrace> c \<lbrace>Q\<rbrace>"
  by hoare_solver

end