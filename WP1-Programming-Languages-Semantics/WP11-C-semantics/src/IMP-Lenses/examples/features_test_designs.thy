section \<open>Verification Condition Testing\<close>

theory features_test_designs
  imports "../hoare/utp_hoare_total"
begin
text{*In the following examples:
      \begin{itemize}  
         \<^item> The formal notation @{term "\<lbrace>Pre\<rbrace>prog\<lbrace>Post\<rbrace>\<^sub>D"} represent a Hoare triple for total 
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
          \<^item> The formal notation @{term "x \<Midarrow> v"} is a syntactic sugar for @{term "assigns_c [x \<mapsto>\<^sub>s v]"}:
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
subsection {*Even count*}

lemma even_count_total:
   "\<lbrace>&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> 
     \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens a\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>weak_lens n\<guillemotright> \<and> 
     \<guillemotleft>i \<bowtie> a\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>  \<and> \<guillemotleft>i \<bowtie> n\<guillemotright> \<and> \<guillemotleft>a \<bowtie> j\<guillemotright> \<and> \<guillemotleft>a \<bowtie> n\<guillemotright> \<and> \<guillemotleft>j \<bowtie> n\<guillemotright>\<rbrace>
      i \<Midarrow> &a ;; 
      j \<Midarrow> \<guillemotleft>0::int\<guillemotright> ;; 
     (&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> &j =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &i =\<^sub>u &a \<and> 
      \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens a\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>weak_lens n\<guillemotright> \<and> 
      \<guillemotleft>i \<bowtie> a\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>  \<and> \<guillemotleft>i \<bowtie> n\<guillemotright> \<and> \<guillemotleft>a \<bowtie> j\<guillemotright> \<and> \<guillemotleft>a \<bowtie> n\<guillemotright> \<and> \<guillemotleft>j \<bowtie> n\<guillemotright>)\<^sup>\<top>\<^sup>C;; 
     while  &i <\<^sub>u &n 
       invr  &a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> 
             \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens a\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>weak_lens n\<guillemotright> \<and> 
             \<guillemotleft>i \<bowtie> a\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>  \<and> \<guillemotleft>i \<bowtie> n\<guillemotright> \<and> \<guillemotleft>a \<bowtie> j\<guillemotright> \<and> \<guillemotleft>a \<bowtie> n\<guillemotright> \<and> \<guillemotleft>j \<bowtie> n\<guillemotright>\<and> 
             &j =\<^sub>u (((&i + 1) - &a) div 2) \<and> &i \<le>\<^sub>u &n \<and>  &i \<ge>\<^sub>u &a
       do (bif &i mod \<guillemotleft>2\<guillemotright> =\<^sub>u  \<guillemotleft>0::int\<guillemotright> 
           then  j \<Midarrow> &j + \<guillemotleft>1\<guillemotright> 
           else SKIP
           eif) ;;  
           i \<Midarrow> &i + \<guillemotleft>1\<guillemotright> 
       od
     \<lbrace>&j =\<^sub>u \<guillemotleft>1::int\<guillemotright>\<rbrace>\<^sub>D"
 apply (rule seq_hoare_r_t)
  prefer 2
  apply (rule seq_hoare_r_t [of _ _ true])
   apply (rule assigns_hoare_r'_t)
  apply (rule seq_hoare_r_t)
   apply (rule assume_hoare_r_t)
   apply (rule skip_hoare_r_t)
  prefer 2
  apply (rule while_invr_hoare_r_t)
    apply (rule seq_hoare_r_t)
     prefer 2
     apply (rule assigns_hoare_r'_t)
    apply (rule cond_hoare_r_t)
     apply (rule assigns_hoare_r_t)
     prefer 6
     apply (rule assigns_hoare_r_t)
     unfolding lens_indep_def
     apply rel_auto
    apply rel_auto
    using mod_pos_pos_trivial apply auto
   apply rel_auto
  apply rel_auto
 apply rel_auto
 apply rel_auto
done

subsection {*catch feature*}


lemma try_throw_zero:
  "Simpl (try THROW catch SKIP end) = SKIP"
  by rel_auto

lemma try_throw_zero_hoare:
      "\<lbrace>\<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace> 
         i \<Midarrow> \<guillemotleft>2::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>0::int\<guillemotright>;;
         try THROW;; i \<Midarrow> \<guillemotleft>7::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>8::int\<guillemotright> catch SKIP end
       \<lbrace>&j =\<^sub>u \<guillemotleft>0::int\<guillemotright>\<and> &i =\<^sub>u \<guillemotleft>2::int\<guillemotright>\<rbrace>\<^sub>D"
  by rel_auto

lemma try_not_throw_ignor_catch:
  "Simpl (try \<langle>a\<rangle>\<^sub>C catch \<langle>b\<rangle>\<^sub>C end) = \<langle>a\<rangle>\<^sub>C"
  by rel_auto

lemma try_not_throw_ignor_catch_hoare:
      "\<lbrace>\<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace> 
         try i \<Midarrow> \<guillemotleft>2::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>0::int\<guillemotright> catch i \<Midarrow> \<guillemotleft>7::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>8::int\<guillemotright> end
       \<lbrace>&j =\<^sub>u \<guillemotleft>0::int\<guillemotright>\<and> &i =\<^sub>u \<guillemotleft>2::int\<guillemotright>\<rbrace>\<^sub>D"
  by rel_auto

lemma try_throw_zero':
  "Simpl (try (SKIP ;; \<langle>a\<rangle>\<^sub>C;;THROW) catch \<langle>b\<rangle>\<^sub>C end) = (\<langle>a\<rangle>\<^sub>C ;; \<langle>b\<rangle>\<^sub>C)"
  by rel_auto blast + 

lemma try_throw_zero'_hoare:
      "\<lbrace>\<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace> 
         try SKIP ;; i \<Midarrow> \<guillemotleft>2::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>0::int\<guillemotright>;; THROW 
         catch i \<Midarrow> \<guillemotleft>7::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>8::int\<guillemotright>  end
       \<lbrace>&i =\<^sub>u \<guillemotleft>7::int\<guillemotright> \<and> &j =\<^sub>u \<guillemotleft>8::int\<guillemotright> \<rbrace>\<^sub>D"
  by rel_auto

lemma "Simpl (try THROW ;; \<langle>a\<rangle>\<^sub>C catch SKIP end) = SKIP "
  by rel_auto blast + 

lemma "Simpl (try (SKIP ;; \<langle>a\<rangle>\<^sub>C) catch SKIP end) =  \<langle>a\<rangle>\<^sub>C"
  by rel_auto blast + 

lemma "Simpl (try (SKIP ;; \<langle>a\<rangle>\<^sub>C;;THROW) catch SKIP end) = \<langle>a\<rangle>\<^sub>C"
  by rel_auto blast + 

subsection {*block feature*}

text {*block_test1 is a scenario. The scenario represent a program where i is name of the variable
       in the scope of the initial state s. In the scenario, and using the command block,
       we create a new variable with the same name inside the block ie., inside the new scope. 
       Now i is a local var for the scope t.
       In that case we can use a restore function on the state s to set the variable to its
       previous value ie.,its value in the scope s, and this before we exit the block.*}

lemma   block_c_test1:
  shows "\<lbrace> \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace> 
          i \<Midarrow> \<guillemotleft>2::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>0::int\<guillemotright> ;; 
          bob 
            INIT (j \<Midarrow> \<guillemotleft>5\<guillemotright>;; i\<Midarrow> \<guillemotleft>5\<guillemotright>) 
            BODY (II)
            RESTORE (\<lambda> (s, s') (t, t').  i\<Midarrow> \<guillemotleft>\<lbrakk>\<langle>id\<rangle>\<^sub>s i\<rbrakk>\<^sub>e ((cp_vars.more o des_vars.more) s)\<guillemotright> ;; 
                                         j\<Midarrow> \<guillemotleft>\<lbrakk>\<langle>id\<rangle>\<^sub>s j\<rbrakk>\<^sub>e ((cp_vars.more o des_vars.more) s)\<guillemotright>) 
            RETURN  (\<lambda> (s, s') (t, t').  II)
          eob
         \<lbrace>&j =\<^sub>u \<guillemotleft>0::int\<guillemotright>\<and> &i =\<^sub>u \<guillemotleft>2::int\<guillemotright>\<rbrace>\<^sub>D"
  using assms  by rel_simp

text {*block_test2 is similar to  block_test1 but the var i is a global var.
       In that case we can use restore function and the state t to set the variable to its
       latest value, ie.,its value in in the scope t,probably modified inside the scope of the block.*}

lemma   block_c_test2:
  shows "\<lbrace> \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace> 
          i \<Midarrow> \<guillemotleft>2::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>0::int\<guillemotright> ;; 
          bob 
            INIT (j \<Midarrow> 5;; i \<Midarrow> 5) 
            BODY (II)
            RESTORE (\<lambda> (s, s') (t, t').  i\<Midarrow> \<guillemotleft>\<lbrakk>&i\<rbrakk>\<^sub>e ((cp_vars.more o des_vars.more) t)\<guillemotright> ;; 
                                      j \<Midarrow> \<guillemotleft>\<lbrakk>&j\<rbrakk>\<^sub>e ((cp_vars.more o des_vars.more) t)\<guillemotright>) 
            RETURN  (\<lambda> (s, s') (t, t').  II)
          eob
         \<lbrace>&j =\<^sub>u 5\<and> &i =\<^sub>u 5\<rbrace>\<^sub>D"
  using assms  unfolding lens_indep_def by rel_simp

lemma  block_c_nested_test1:
  shows "\<lbrace> \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace> 
          i \<Midarrow> \<guillemotleft>2::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>0::int\<guillemotright> ;;
          bob
            INIT (j \<Midarrow> \<guillemotleft>5::int\<guillemotright>;; i\<Midarrow> \<guillemotleft>5::int\<guillemotright>)  
            BODY
              bob 
                INIT (j \<Midarrow> \<guillemotleft>5::int\<guillemotright>;; i\<Midarrow> \<guillemotleft>5::int\<guillemotright>) 
                BODY (II)
                RESTORE (\<lambda> (s, s') (t, t').  i\<Midarrow> \<guillemotleft>\<lbrakk>&i\<rbrakk>\<^sub>e ((cp_vars.more o des_vars.more) s)\<guillemotright> ;; 
                                             j\<Midarrow> \<guillemotleft>\<lbrakk>&j\<rbrakk>\<^sub>e ((cp_vars.more o des_vars.more) s)\<guillemotright>) 
                RETURN  (\<lambda> (s, s') (t, t').  SKIP)
              eob
            RESTORE (\<lambda> (s, s') (t, t'). SKIP)
            RETURN  (\<lambda> (s, s') (t, t').  SKIP)
          eob
         \<lbrace>&j =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<and> &i =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>\<^sub>D"
  using assms  unfolding lens_indep_def by rel_simp

lemma  block_c_nested_test2:
  shows "\<lbrace> \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace> 
          i \<Midarrow> \<guillemotleft>2::int\<guillemotright>;; j \<Midarrow> \<guillemotleft>0::int\<guillemotright> ;;
          bob
            INIT (j \<Midarrow> \<guillemotleft>5::int\<guillemotright>;; i\<Midarrow> \<guillemotleft>5::int\<guillemotright>)  
            BODY
              bob 
                INIT (j \<Midarrow> \<guillemotleft>5::int\<guillemotright>;; i\<Midarrow> \<guillemotleft>5::int\<guillemotright>) 
                BODY (II)
                RESTORE (\<lambda> (s, s') (t, t').  i\<Midarrow> \<guillemotleft>\<lbrakk>&j\<rbrakk>\<^sub>e ((cp_vars.more o des_vars.more) s)\<guillemotright> ;; 
                                             j\<Midarrow> \<guillemotleft>\<lbrakk>&j\<rbrakk>\<^sub>e ((cp_vars.more o des_vars.more) s)\<guillemotright>) 
                RETURN  (\<lambda> (s, s') (t, t').  SKIP)
              eob
            RESTORE (\<lambda> (s, s') (t, t'). i\<Midarrow> \<guillemotleft>\<lbrakk>&i\<rbrakk>\<^sub>e ((cp_vars.more o des_vars.more) s)\<guillemotright> ;; 
                                        j\<Midarrow> \<guillemotleft>\<lbrakk>&j\<rbrakk>\<^sub>e ((cp_vars.more o des_vars.more) s)\<guillemotright>)
            RETURN  (\<lambda> (s, s') (t, t').  SKIP)
          eob
         \<lbrace>&j =\<^sub>u \<guillemotleft>0::int\<guillemotright>\<and> &i =\<^sub>u \<guillemotleft>2::int\<guillemotright>\<rbrace>\<^sub>D"
  using assms  by rel_simp
term "fault"
term "SKIP"
term "fault :== v"
term "fault :== v;; (assign_r (f k) \<guillemotleft>val\<guillemotright>) "
term "lens_comp "
term "fault :== v;; (assign_r (add1  ;\<^sub>L field) val) ;; x\<Midarrow> val1"
find_theorems name:".fault"
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
