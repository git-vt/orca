section \<open>Verification Condition Testing\<close>

theory control_flow_total_examples
  imports "../hoare/utp_hoare_total"
begin 
text{*In this section we provide a set of examples on the verification
      of programs that uses control flow statements
      with Hoare logic for total correctness. 
      The combination of relational algebra, ie. UTP, and lens algebra allows for a semantic based
      framework for the specification of programming languages and their features. It also
      allows a powerful proof tactics for the framework such as @{method rel_auto},
      @{method pred_auto}, etc.*}

text{*
   In the following examples:
      \begin{itemize}  
         \<^item> The formal notation @{term "\<lbrace>Pre\<rbrace>prog\<lbrace>Post\<rbrace>\<^sub>A\<^sub>B\<^sub>R"} represent a hoare triple for total 
            correctness.
         \<^item> All variables are represented by lenses and have the type @{typ "'v \<Longrightarrow> 's"}:
           where @{typ "'v"} is the view type of the lens and @{typ "'s"} is the type of the state.
         \<^item> Lens properties such as @{term "weak_lens"}, @{term "mwb_lens"}, @{term "wb_lens"},
           @{term "vwb_lens"}, @{term "ief_lens"}, @{term "bij_lens"}
           are used to semantically express what does not change in the state space. For example
           applying the property @{term "id_lens"}. Informally this means that any change on x will
           appear on all  other variables in the state space.The property @{term "ief_lens"} is 
           just the opposite of @{term "id_lens"}.
         \<^item> The formal notation @{term "x \<sharp>\<sharp> P"} is a syntactic sugar for @{term "unrest_relation x P"}:
           informally it is used to semantically express that the variable x does not occur
           in the program P.
         \<^item> The formal notation @{term "x \<Midarrow> v"} is a syntactic sugar for @{term "assigns_c [x \<mapsto>\<^sub>s v]"}:
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

subsection {*catch feature*}

text{*The control flow statement @{term "try P catch Q end"} is used to capture state exceptions.
      Combined with the @{term "THROW"} it can be used to capture semantics of @{term return}
      @{term break} and @{term continue}. Informally @{term "try P catch Q end"} will execute
       a program @{term P}. If @{term P} triggers an exception, this exception is handled by 
       @{term Q}.*}

text{*Informally @{term "THROW"} statement will transform
      the state from normal, ie. stable state, to an abrupt state. Under the assumption
      that the initial state of a program is stable, any control flow
      statement after @{term "THROW"} is executed will be purged. So, @{term "THROW"}
      is a left zero under the assumption that the initial state is stable.*}

lemma try_throw_zero:
  "(try THROW\<^sub>A\<^sub>B\<^sub>R catch SKIP\<^sub>A\<^sub>B\<^sub>R end) = SKIP\<^sub>A\<^sub>B\<^sub>R"
  by rel_blast 

lemma try_throw_zero_hoare:
      "\<lbrace>\<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace> 
         i \<Midarrow> \<guillemotleft>2::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>0::int\<guillemotright>;;
         try THROW\<^sub>A\<^sub>B\<^sub>R;; i \<Midarrow> \<guillemotleft>7::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>8::int\<guillemotright> catch SKIP\<^sub>A\<^sub>B\<^sub>R end
       \<lbrace>&j =\<^sub>u \<guillemotleft>0::int\<guillemotright>\<and> &i =\<^sub>u \<guillemotleft>2::int\<guillemotright>\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
     apply (simp only: uabr_comp usubst uabr_simpl simpl_abr_form)
     apply rel_simp
done 


lemma try_not_throw_ignor_catch_hoare:
      "\<lbrace>\<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace> 
         try i \<Midarrow> \<guillemotleft>2::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>0::int\<guillemotright> catch i \<Midarrow> \<guillemotleft>7::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>8::int\<guillemotright> end
       \<lbrace>&j =\<^sub>u \<guillemotleft>0::int\<guillemotright>\<and> &i =\<^sub>u \<guillemotleft>2::int\<guillemotright>\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
    apply (simp only: uabr_comp usubst uabr_simpl) 
    apply rel_simp
done

lemma try_throw_zero':
  "(try SKIP\<^sub>A\<^sub>B\<^sub>R ;; \<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;;THROW\<^sub>A\<^sub>B\<^sub>R catch \<langle>b\<rangle>\<^sub>A\<^sub>B\<^sub>R end) = (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R ;; \<langle>b\<rangle>\<^sub>A\<^sub>B\<^sub>R)"
  by rel_auto blast +  

lemma try_throw_zero'_hoare:
      "\<lbrace>\<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace> 
         try SKIP\<^sub>A\<^sub>B\<^sub>R ;; i \<Midarrow> \<guillemotleft>2::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>0::int\<guillemotright>;; THROW\<^sub>A\<^sub>B\<^sub>R 
         catch i \<Midarrow> \<guillemotleft>7::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>8::int\<guillemotright>  end
       \<lbrace>&i =\<^sub>u \<guillemotleft>7::int\<guillemotright> \<and> &j =\<^sub>u \<guillemotleft>8::int\<guillemotright> \<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  apply (simp only: uabr_comp usubst uabr_simpl C3_abr_def) 
  apply rel_simp
done

lemma "(try THROW\<^sub>A\<^sub>B\<^sub>R ;; \<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R catch SKIP\<^sub>A\<^sub>B\<^sub>R end) = SKIP\<^sub>A\<^sub>B\<^sub>R"
  apply (simp only: uabr_comp usubst uabr_simpl) 
  apply rel_simp
done

lemma "(try (SKIP\<^sub>A\<^sub>B\<^sub>R ;; \<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R) catch SKIP\<^sub>A\<^sub>B\<^sub>R end) =  \<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R"
  apply (simp only: uabr_comp usubst uabr_simpl) 
  apply rel_simp
done

lemma "(try \<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; \<langle>b\<rangle>\<^sub>A\<^sub>B\<^sub>R catch SKIP\<^sub>A\<^sub>B\<^sub>R end) = (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R ;; try  \<langle>b\<rangle>\<^sub>A\<^sub>B\<^sub>R catch SKIP\<^sub>A\<^sub>B\<^sub>R end)"
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis (no_types))+
done


lemma "(try \<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; Simpl\<^sub>A\<^sub>B\<^sub>R P catch SKIP\<^sub>A\<^sub>B\<^sub>R end) = (\<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R ;; try  Simpl\<^sub>A\<^sub>B\<^sub>R P catch SKIP\<^sub>A\<^sub>B\<^sub>R end)"
  apply pred_simp
  apply rel_simp
  apply auto
  apply (metis (no_types))+
done

lemma "(try SKIP\<^sub>A\<^sub>B\<^sub>R ;; \<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R;; THROW\<^sub>A\<^sub>B\<^sub>R catch SKIP\<^sub>A\<^sub>B\<^sub>R end) = \<langle>a\<rangle>\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto blast +

subsection {*block feature*}

text {*block_test1 is a scenario. The scenario represent a program where i is name of the variable
       in the scope of the initial state s. In the scenario, and using the command block,
       we create a new variable with the same name inside the block ie., inside the new scope. 
       Now i is a local var for the scope t.
       In that case we can use a restore function on the state s to set the variable to its
       previous value ie.,its value in the scope s, and this before we exit the block.*}

text \<open>The normal restore/return functions were verbose, so it's good to have an abbreviation to use
      to reduce duplicated code. Unfortunately, this does cause some parsing ambiguity, but Isabelle
      resolves that fairly well. It may reduce performance slightly, though.\<close>
abbreviation cp_des where
  "cp_des v s \<equiv> \<guillemotleft>\<lbrakk>v\<rbrakk>\<^sub>e ((cp_abr.more \<circ> des_vars.more) s)\<guillemotright>"

lemma   block_c_test1:
  shows "\<lbrace>\<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace> 
          i \<Midarrow> \<guillemotleft>2::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>0::int\<guillemotright>;;
          bob
            INIT j \<Midarrow> 5;; i \<Midarrow> 5
            BODY II
            RESTORE (\<lambda> (s, _) _. i \<Midarrow> cp_des &i s;;
                                j \<Midarrow> cp_des &j s)
            RETURN (\<lambda> _ _. II)
          eob
         \<lbrace>&j =\<^sub>u 0 \<and> &i =\<^sub>u 2\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by rel_simp

text {*block_test2 is similar to  block_test1 but the var i is a global var.
       In that case we can use restore function and the state t to set the variable to its
       latest value, ie.,its value in the scope t,probably modified inside the scope of the block.*}

lemma   block_c_test2:
  shows "\<lbrace>\<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace>
          i \<Midarrow> \<guillemotleft>2::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>0::int\<guillemotright>;;
          bob
            INIT j \<Midarrow> 5;; i \<Midarrow> 5
            BODY II
            RESTORE \<lambda> _ (t, _). i \<Midarrow> cp_des &i t;;
                                j \<Midarrow> cp_des &j t
            RETURN \<lambda> _ _. II
          eob
         \<lbrace>&j =\<^sub>u 5\<and> &i =\<^sub>u 5\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  unfolding lens_indep_def 
  by rel_simp

lemma  block_c_nested_test1:
  shows "\<lbrace>\<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace>
          i \<Midarrow> \<guillemotleft>2::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>0::int\<guillemotright>;;
          bob
            INIT j \<Midarrow> 5;; i \<Midarrow> 5
            BODY
              bob
                INIT j \<Midarrow> 5;; i \<Midarrow> 5
                BODY II
                RESTORE \<lambda> (s, _) _. i \<Midarrow> cp_des &i s;;
                                    j \<Midarrow> cp_des &j s
                RETURN \<lambda> _ _. II
              eob
            RESTORE \<lambda> _ _. II
            RETURN \<lambda> _ _. II
          eob
         \<lbrace>&j =\<^sub>u 5 \<and> &i =\<^sub>u 5\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  unfolding lens_indep_def 
  by rel_simp

lemma  block_c_nested_test2:
  shows "\<lbrace>\<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace>
          i \<Midarrow> \<guillemotleft>2::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>0::int\<guillemotright>;;
          bob
            INIT j \<Midarrow> 5;; i \<Midarrow> 5
            BODY
              bob
                INIT j \<Midarrow> 5;; i \<Midarrow> 5
                BODY II
                RESTORE \<lambda> (s, _) _. i \<Midarrow> cp_des &i s;;
                                    j \<Midarrow> cp_des &j s
                RETURN \<lambda> _ _. II
              eob
            RESTORE \<lambda> (s, _) _. i \<Midarrow> cp_des &i s;;
                                j \<Midarrow> cp_des &j s
            RETURN \<lambda> _ _. II
          eob
         \<lbrace>&j =\<^sub>u 0 \<and> &i =\<^sub>u 2\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
    by rel_simp

section {*Separation Algebra by Calcagno*}
subsection {*axioms*}
named_theorems separation_algebra

declare Lens_Laws.lens_indep_sym[separation_algebra] (*x \<sharp>\<sharp> y \<Longrightarrow> y \<sharp>\<sharp> x *)
declare unit_ief_lens[separation_algebra] (*x + 0 = x*)
declare lens_indep.lens_put_comm[separation_algebra] (*x \<sharp>\<sharp> y \<Longrightarrow>x + y = y + x *)
declare lens_indep.lens_put_irr1[separation_algebra]
declare lens_indep.lens_put_irr2[separation_algebra]

lemma [separation_algebra]:"x \<bowtie> 0\<^sub>L" (*x \<sharp>\<sharp> 0*)
  unfolding lens_indep_def  
  by rel_auto

lemma [separation_algebra]:
  "\<lbrakk>X \<bowtie> Y; Y \<bowtie> Z; X \<bowtie> Z\<rbrakk>\<Longrightarrow> 
   lens_put Z (lens_put X (lens_put Y \<sigma> v) u) i = lens_put X (lens_put Y (lens_put Z \<sigma> i) v) u"
  unfolding lens_indep_def  
  by rel_auto
 
end
