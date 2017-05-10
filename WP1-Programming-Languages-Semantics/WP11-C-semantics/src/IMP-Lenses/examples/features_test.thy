section \<open>Verification Condition Testing\<close>

theory features_test
  imports "../hoare/utp_hoare"
begin

subsection {*Even count*}

text{*In the following examples:
      \begin{itemize}  
         \<^item> The formal notation @{term "\<lbrace>Pre\<rbrace>prog\<lbrace>Post\<rbrace>\<^sub>u"} represent a hoare triple for partial 
            correctness.
         \<^item> All variables are represented by lenses and have the type @{typ "'v \<Longrightarrow> 's"}:
           where  @{typ "'v"} is the view type of the lens and @{typ "'s"} is the type of the state.
         \<^item> Lens properties such as @{term "weak_lens"}, @{term "mwb_lens"}, @{term "wb_lens"},
           @{term "vwb_lens"}, @{term "ief_lens"}, @{term "bij_lens"}
           are used to semantically express what does not change in the state space. For example
           applying the property @{term "bij_lens"} of variable @{term "x"} gives the term
           @{term "bij_lens x"}. Informally this means that any change on x will appear on all
           other variables in the state space.The property @{term "ief_lens"} is just the opposite
           of @{term "bij_lens"}.
          \<^item> The formal notation @{term "x \<sharp>\<sharp> P"} is a syntactic sugar for 
            @{term "unrest_relation x P"}:
           informally it is used to semantically express that the variable x does not occur
           in the program P.
          \<^item> The formal notation @{term "x :== v"} is a syntactic sugar for @{term "assigns_r [x \<mapsto>\<^sub>s v]"}:
           informally it represent an assignment of a value v to a variable x. 
         \<^item> The formal notation @{term "&x"} is a syntactic sugar for @{term "\<langle>id\<rangle>\<^sub>s x"}: 
           informally it represent the content of a variable x.
         \<^item> The formal notation @{term "\<guillemotleft>l\<guillemotright>"} is a syntactic sugar for @{term "lit l"}: 
            informally it represent a lifting of an HOL literal l to utp expression.
         \<^item> The formal notation @{term "x \<bowtie> y"} is a syntactic sugar for @{term "lens_indep x y"}: 
           informally it is a semantic representation that uses two variables 
           to characterise independence between two state space regions  .
     \end{itemize}
     *}
lemma even_count:
   assumes "weak_lens i" and "weak_lens a" and "weak_lens j" and "weak_lens n" and
           "i \<bowtie> a" and "i \<bowtie> j" and "i \<bowtie> n" and "a \<bowtie> j" and "a \<bowtie> n" and "j \<bowtie> n"
   shows
   "\<lbrace>&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u 1\<rbrace>
       i:== &a;; j :== 0;;
       (&a =\<^sub>u 0 \<and> &n =\<^sub>u 1 \<and> &j =\<^sub>u 0 \<and> &i =\<^sub>u &a)\<^sup>\<top>;;
     while &i <\<^sub>u &n
       invr &a =\<^sub>u 0 \<and> &n =\<^sub>u 1 \<and> &j =\<^sub>u (((&i + 1) - &a) div 2) \<and> &i \<le>\<^sub>u &n \<and> &i \<ge>\<^sub>u &a
       do (j :== &j + 1 \<triangleleft> &i mod 2 =\<^sub>u 0 \<triangleright>\<^sub>r II);; i :== &i + 1 od
     \<lbrace>&j =\<^sub>u 1\<rbrace>\<^sub>u"
   apply (insert assms)
   apply (rule seq_hoare_r)
    prefer 2
    apply (rule seq_hoare_r [of _ _ true])
     apply (rule assigns_hoare_r')
    apply (rule seq_hoare_r)
     apply (rule assume_hoare_r)
     apply (rule skip_hoare_r)
    prefer 2
    apply (rule while_invr_hoare_r)
      apply (rule seq_hoare_r)
       prefer 2
       apply (rule assigns_hoare_r')
      apply (rule cond_hoare_r)
       apply (rule assigns_hoare_r)
       prefer 6
       apply (rule assigns_hoare_r)
       unfolding lens_indep_def
       apply rel_auto
      apply rel_auto
      using mod_pos_pos_trivial apply auto
     apply rel_auto
    apply rel_auto
   apply rel_auto
   apply rel_auto
  done

subsection {*block feature*}

text {*block_test1 is a scenario. The scenario represent a program where i is name of the variable
       in the scope of the initial state s. In the scenario, and using the command block,
       we create a new variable with the same name inside the block ie., inside the new scope. 
       Now i is a local var for the scope t.
       In that case we can use a restore function on the state s to set the variable to its
       previous value ie.,its value in the scope s, and this before we exit the block.*}

lemma   blocks_test1:
  assumes "weak_lens i"
  shows "\<lbrace>true\<rbrace>
          i :== \<guillemotleft>2::int\<guillemotright>;; 
          block (i :== \<guillemotleft>5\<guillemotright>) (II) (\<lambda> (s, s') (t, t').  i:== \<guillemotleft>\<lbrakk>\<langle>id\<rangle>\<^sub>s i\<rbrakk>\<^sub>e s\<guillemotright>) (\<lambda> (s, s') (t, t').  II) 
         \<lbrace>&i =\<^sub>u \<guillemotleft>2::int\<guillemotright>\<rbrace>\<^sub>u"
  using assms by rel_auto


text {*block_test2 is similar to  block_test1 but the var i is a global var.
       In that case we can use restore function and the state t to set the variable to its
       latest value, ie.,its value in in the scope t,probably modified inside the scope of the block.*}

lemma   blocks_test2:
  assumes "weak_lens i"
  shows "\<lbrace>true\<rbrace>
          i :== \<guillemotleft>2::int\<guillemotright>;; 
          block (i :== \<guillemotleft>5\<guillemotright>) (II) (\<lambda> (s, s') (t, t').  i:== \<guillemotleft>\<lbrakk>\<langle>id\<rangle>\<^sub>s i\<rbrakk>\<^sub>e t\<guillemotright>) (\<lambda> (s, s') (t, t').  II) 
         \<lbrace>&i =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>\<^sub>u"
  using assms by rel_auto

subsection {*Infinite loops*}
text{*The next two lemmas are the witness needed to justify the theory of designs.*}

lemma 1:"while\<^sub>\<bottom> true do II od = true"
  unfolding while_bot_def
  apply rel_simp unfolding gfp_def apply transfer apply auto done

lemma "in\<alpha> \<sharp> ( x :== \<guillemotleft>c\<guillemotright>) \<Longrightarrow> while\<^sub>\<bottom> true  do II od;; x :== \<guillemotleft>c\<guillemotright> = x :== \<guillemotleft>c\<guillemotright>"
  apply (subst 1) apply (simp only: assigns_r.abs_eq )  
  apply (simp only: seqr_def) apply simp
 apply rel_simp  apply transfer apply auto done

end
