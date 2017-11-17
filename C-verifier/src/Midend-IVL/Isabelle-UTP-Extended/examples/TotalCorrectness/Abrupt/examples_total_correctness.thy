theory examples_total_correctness
  imports "../../../hoare/HoareLogic/TotalCorrectness/Abrupt/utp_hoare_total"
begin

section Examples

text \<open>In this section we provide a set of examples for the use of Hoare logic 
      for total correctness based on a theory of UTP and lenses. The combination of 
      relational algebra, ie. UTP, and lens algebra allows for a semantic based
      framework for the specification of programming languages and their features. It also
      allows a powerful proof tactics for the framework such as @{method rel_auto},
      @{method pred_auto}, etc.\<close>

text \<open>In the following examples:
      \begin{itemize}  
         \<^item> The formal notation @{term "\<lbrace>Pre\<rbrace>prog\<lbrace>Post\<rbrace>\<^sub>A\<^sub>B\<^sub>R"} represent a hoare triple for total 
            correctness.
         \<^item> All variables are represented by lenses and have the type @{typ "'v \<Longrightarrow> 's"}:
           where  @{typ "'v"} is the view type of the lens and @{typ "'s"} is the type of the state.
         \<^item> Lens properties such as @{term "weak_lens"}, @{term "mwb_lens"}, @{term "wb_lens"},
           @{term "vwb_lens"}, @{term "ief_lens"}, @{term "bij_lens"}
           are used to semantically express what does not change in the state space. For example
           applying the property @{term "id_lens"}. 
            Informally this means that any change on x will appear on all
           other variables in the state space.The property @{term "ief_lens"} is just the opposite
           of @{term "id_lens"}.
         \<^item> The formal notation @{term "x \<sharp>\<sharp> P"} is a syntactic sugar for 
            @{term "unrest_relation x P"}:
           informally it is used to semantically express that the variable x does not occur
           in the program P.
         \<^item> The formal notation @{term "x \<Midarrow> v"} is a lifting of @{term "x :== v"} to the theory 
            of designs: informally it represent an assignment of a value v to a variable x. 
         \<^item> The formal notation @{term "&x"} is a syntactic sugar for @{term "\<langle>id\<rangle>\<^sub>s x"}: 
           informally it represent the content of a variable x.
         \<^item> The formal notation @{term "\<guillemotleft>l\<guillemotright>"} is a syntactic sugar for @{term "lit l"}: 
            informally it represent a lifting of an HOL literal l to a utp expression.
         \<^item> The formal notation @{term "x \<bowtie> y"} is a syntactic sugar for @{term "lens_indep x y"}: 
           informally it is a semantic representation that uses two variables 
           to characterise independence between two state space regions.
         \<^item> The tactics @{method rel_auto}, @{method pred_auto}, @{method rel_simp},
           @{method pred_simp}, @{method rel_blast}, @{method pred_blast} are used
           to discharge proofs related to UTP-relations and UTP-predicates.
     \end{itemize}\<close>

subsection \<open>Swap variables program\<close>

lemma swap_test_manual:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
  and "x \<bowtie> y" and "x \<bowtie> z" and "y \<bowtie> z"
  shows 
  "\<lbrace>&x =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>b\<guillemotright>\<rbrace>
    z :=\<^sub>D &x;;
    x \<Midarrow> &y;;
    y \<Midarrow> &z
   \<lbrace>&x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>a\<guillemotright>\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  apply (insert assms)
  apply (rule seq_hoare_r_t)
   defer
   apply (rule seq_hoare_r_t)
    apply (rule assigns_abr_hoare_r'_t)
   apply (rule assigns_abr_hoare_r'_t)
  apply rel_simp
  apply (simp add: lens_indep_sym)
  done

lemma swap_test:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
  and "x \<bowtie> y" and "x \<bowtie> z" and "y \<bowtie> z"
  shows 
 "\<lbrace>&x =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>b\<guillemotright>\<rbrace>
   z \<Midarrow> &x;;
   x \<Midarrow> &y;;
   y \<Midarrow> &z
  \<lbrace>&x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>a\<guillemotright>\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  using assms
  apply (simp only: uabr_comp uabr_simpl lens_indep_def)
  apply rel_simp
  done

subsection {*Even count program*}
term "j \<Midarrow> ((&j) + 1)"
lemma even_count_total:
  "\<lbrace>&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u 1 \<and>
    \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens a\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>weak_lens n\<guillemotright> \<and>
    \<guillemotleft>i \<bowtie> a\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>  \<and> \<guillemotleft>i \<bowtie> n\<guillemotright> \<and> \<guillemotleft>a \<bowtie> j\<guillemotright> \<and> \<guillemotleft>a \<bowtie> n\<guillemotright> \<and> \<guillemotleft>j \<bowtie> n\<guillemotright>\<rbrace>
     i \<Midarrow> &a;;
     j \<Midarrow> 0;;
    (&a =\<^sub>u 0 \<and> &n =\<^sub>u 1 \<and> &j =\<^sub>u 0 \<and> &i =\<^sub>u &a \<and>
     \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens a\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>weak_lens n\<guillemotright> \<and>
     \<guillemotleft>i \<bowtie> a\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>  \<and> \<guillemotleft>i \<bowtie> n\<guillemotright> \<and> \<guillemotleft>a \<bowtie> j\<guillemotright> \<and> \<guillemotleft>a \<bowtie> n\<guillemotright> \<and> \<guillemotleft>j \<bowtie> n\<guillemotright>)\<^sup>\<top>\<^sup>C;;
    while &i <\<^sub>u &n
    invr &a =\<^sub>u 0 \<and> &n =\<^sub>u 1 \<and>
         \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens a\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>weak_lens n\<guillemotright> \<and>
         \<guillemotleft>i \<bowtie> a\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>  \<and> \<guillemotleft>i \<bowtie> n\<guillemotright> \<and> \<guillemotleft>a \<bowtie> j\<guillemotright> \<and> \<guillemotleft>a \<bowtie> n\<guillemotright> \<and> \<guillemotleft>j \<bowtie> n\<guillemotright> \<and>
         &j =\<^sub>u (((&i + 1) - &a) div 2) \<and> &i \<le>\<^sub>u &n \<and>  &i \<ge>\<^sub>u &a
    do
      bif &i mod 2 =\<^sub>u 0
        then j \<Midarrow> ((&j) + 1)
      else
        SKIP\<^sub>A\<^sub>B\<^sub>R
      eif;;
      i \<Midarrow> (&i + 1)
    od
  \<lbrace>&j =\<^sub>u 1\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  apply (rule seq_hoare_r_t)
   prefer 2
   apply (rule seq_hoare_r_t [of _ _ true])
    apply (rule assigns_abr_hoare_r'_t)
   apply (rule seq_hoare_r_t)
    apply (rule assume_hoare_r_t)
     apply (rule skip_abr_hoare_r_t)
    prefer 2
    apply (rule while_invr_hoare_r_t)
      apply (rule seq_hoare_r_t)
       prefer 2
       apply (rule assigns_abr_hoare_r'_t)
      apply (rule cond_abr_hoare_r_t)
       apply (rule assigns_abr_hoare_r_t)
       prefer 6
       apply (rule assigns_abr_hoare_r_t)
       unfolding lens_indep_def
       apply rel_auto
      apply rel_auto
     using mod_pos_pos_trivial apply auto
     apply rel_auto
    apply rel_auto
   apply rel_auto
  apply rel_auto
  done

lemma 
 "\<lbrace>true\<rbrace>
   while true invr true do SKIP\<^sub>A\<^sub>B\<^sub>R od
  \<lbrace>Q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  apply (rule while_invr_hoare_r_t)
  apply rel_auto
  apply auto
  done
    

lemma "while true invr true do SKIP\<^sub>A\<^sub>B\<^sub>R od = false"
   apply (simp add: While_inv_def While_def alpha)
   apply (rule antisym)
  apply (simp_all)
  apply (rule lfp_lowerbound)
  apply (simp)
  done

lemma 
 "\<lbrace>true\<rbrace>
   false
  \<lbrace>Q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by rel_auto

lemma "while b do C od = lfp (\<lambda>X .bif b then (C ;; X) else SKIP\<^sub>A\<^sub>B\<^sub>R eif)"    
  unfolding While_def
  by (rule refl)
term "gfp (\<lambda>x. f)"
end