section \<open>Verification Condition Testing\<close>

theory control_flow_partial_examples
  imports "../hoare/utp_hoare"
begin
section "Examples"

text{*In this section we provide a set of examples on the verification
      of programs that uses  control flow statements
      with Hoare logic for partial correctness. 
      The combination of 
      relational algebra, ie. UTP, and lens algebra allows for a semantic based
      framework for the specification of programming languages and their features. It also
      allows a powerful proof tactics for the framework such as @{method rel_auto},
      @{method pred_auto}, etc.*}

text{*
   In the following examples:
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
           to characterise independence between two state space regions.
         \<^item> The tactics @{method rel_auto}, @{method pred_auto}, @{method rel_simp},
           @{method pred_simp}, @{method rel_blast}, @{method pred_blast} are used
           to discharge proofs related to UTP-relations and UTP-predicates.
     \end{itemize}
     *}

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
