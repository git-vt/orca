
theory examples_partial_correctness
imports "../hoare/VCG"
begin
section "Examples"

text{* In this section we provide a set of examples for the use of Hoare logic 
      for partial correctness using a theory of UTP and lenses. The combination of 
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


subsection {*Swap variables program*}

lemma swap_test_manual:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
  and "x \<bowtie> y" and "x \<bowtie> z" and "y \<bowtie> z"
  shows "\<lbrace>&x =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>b\<guillemotright>\<rbrace>
  z :== &x;;
  x :== &y;;
  y :== &z
  \<lbrace>&x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>a\<guillemotright>\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule seq_hoare_r)
   defer
   apply (rule seq_hoare_r)
    apply (rule assigns_hoare_r')
   apply (rule assigns_hoare_r')
  apply rel_simp
  apply (simp add: lens_indep_sym)
  done

lemma swap_test:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
  and "x \<bowtie> y" and "x \<bowtie> z" and "y \<bowtie> z"
  shows "\<lbrace>&x =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>b\<guillemotright>\<rbrace>
  z :== &x;;
  x :== &y;;
  y :== &z
  \<lbrace>&x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>a\<guillemotright>\<rbrace>\<^sub>u"
  using assms
  by rel_auto (simp add: lens_indep_sym)


lemma swap_test_method:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
  and "x \<bowtie> y" and "x \<bowtie> z" and "y \<bowtie> z"
  shows "\<lbrace>&x =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>b\<guillemotright>\<rbrace>
  z :== &x;;
  x :== &y;;
  y :== &z
  \<lbrace>&x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>a\<guillemotright>\<rbrace>\<^sub>u"
  using assms
  by vcg

lemma swap_test_method_step:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
  and "x \<bowtie> y" and "x \<bowtie> z" and "y \<bowtie> z"
  shows "\<lbrace>&x =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>b\<guillemotright>\<rbrace>
  z :== &x;;
  x :== &y;;
  y :== &z
  \<lbrace>&x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>a\<guillemotright>\<rbrace>\<^sub>u"
  apply (insert assms)
  unfolding lens_indep_def
  apply vcg_step
  done

lemma swap_testx:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
  and "x \<bowtie> y"
  and "x \<sharp> a" and "y \<sharp> a" and "z \<sharp> a"
  and "x \<sharp> b" and "y \<sharp> b" and "z \<sharp> b"
  shows "\<lbrace>&x =\<^sub>u a \<and> &y =\<^sub>u b\<rbrace>
  z :== &x;;
  x :== &y;;
  y :== &z
  \<lbrace>&x =\<^sub>u b \<and> &y =\<^sub>u a\<rbrace>\<^sub>u = \<lbrace>&x =\<^sub>u a \<and> &y =\<^sub>u b\<rbrace>
  z :== &x;;
  x :== &y
  \<lbrace>&x =\<^sub>u b \<and> &z =\<^sub>u a\<rbrace>\<^sub>u"
  using assms
  by rel_simp

subsection {*Even count program*}
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

lemma even_count_method:
  assumes "vwb_lens i" and "weak_lens start" and "vwb_lens j" and "weak_lens end"
  and "i \<bowtie> start" and "i \<bowtie> j" and "i \<bowtie> end" and "start \<bowtie> j" and "start \<bowtie> end" and "j \<bowtie> end"
  shows
  "\<lbrace>&start =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &end =\<^sub>u 1\<rbrace>
    i :== &start;; j :== 0;;
    (&start =\<^sub>u 0 \<and> &end =\<^sub>u 1 \<and> &j =\<^sub>u 0 \<and> &i =\<^sub>u &start)\<^sup>\<top> ;;
    while &i <\<^sub>u &end
    invr &start =\<^sub>u 0 \<and> &end =\<^sub>u 1 \<and> &j =\<^sub>u (((&i + 1) - &start) div 2) \<and> &i \<le>\<^sub>u &end \<and> &i \<ge>\<^sub>u &start
    do (j :== &j + 1 \<triangleleft> &i mod 2 =\<^sub>u 0 \<triangleright>\<^sub>r II) ;; i :== &i + 1 od
   \<lbrace>&j =\<^sub>u 1\<rbrace>\<^sub>u"
  by (insert assms) vcg

subsection {*Increment program*}

subsubsection \<open>Simple increment program\<close>

lemma increment_manual:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x :== 0;;
  (&x =\<^sub>u 0 \<and> &y =\<^sub>u 5)\<^sup>\<top>;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule seq_hoare_r[of _ _ true])
   defer
   apply (rule seq_hoare_r)
    apply (rule assume_hoare_r)
     apply (rule skip_hoare_r)
    defer
    apply (rule while_invr_hoare_r)
      unfolding lens_indep_def
      apply rel_auto
     apply rel_auto
    apply rel_auto
   apply rel_auto
  apply rel_auto
  done

lemma increment_method_step:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x :== 0;;
  (&x =\<^sub>u 0 \<and> &y =\<^sub>u 5)\<^sup>\<top>;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule seq_hoare_r[of _ _ true])
   apply vcg_step+
     unfolding lens_indep_def
     apply vcg_step+
  done

lemma increment_method:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x :== 0;;
  (&x =\<^sub>u 0 \<and> &y =\<^sub>u 5)\<^sup>\<top>;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>u"
  by (insert assms) vcg

lemma increment'_manual:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&x =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &y =\<^sub>u 5\<rbrace>
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule while_invr_hoare_r)
    unfolding lens_indep_def
    apply rel_auto
   apply rel_auto
  apply rel_auto
  done

lemma increment'_method:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&x =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &y =\<^sub>u 5\<rbrace>
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>u"
  by (insert assms) vcg

subsubsection \<open>Double increment program\<close>

lemma double_increment_manual:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&x =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &y =\<^sub>u 5\<rbrace>
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od;;
  (&x =\<^sub>u 5 \<and> &y =\<^sub>u 5)\<^sup>\<top>;;
  while &x <\<^sub>u &y * 2
  invr &x \<le>\<^sub>u &y * 2 \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x =\<^sub>u 10\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule seq_hoare_r[of _ _ true])
   apply (rule while_invr_hoare_r)
     unfolding lens_indep_def
     apply rel_auto
    apply rel_auto
   apply rel_auto
  apply (rule seq_hoare_r)
   apply (rule assume_hoare_r)
    apply (rule skip_hoare_r)
   apply rel_auto
  apply (rule while_invr_hoare_r)
    apply rel_auto
   apply rel_auto
  apply rel_auto
  done

lemma double_increment_method_step:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&x =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &y =\<^sub>u 5\<rbrace>
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od;;
  (&x =\<^sub>u 5 \<and> &y =\<^sub>u 5)\<^sup>\<top>;;
  while &x <\<^sub>u &y * 2
  invr &x \<le>\<^sub>u &y * 2 \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x =\<^sub>u 10\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule seq_hoare_r[of _ _ true])
   apply vcg_step+
     unfolding lens_indep_def
     apply vcg_step+
  done

lemma double_increment_method:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&x =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &y =\<^sub>u 5\<rbrace>
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od;;
  (&x =\<^sub>u 5 \<and> &y =\<^sub>u 5)\<^sup>\<top>;;
  while &x <\<^sub>u &y * 2
  invr &x \<le>\<^sub>u &y * 2 \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x =\<^sub>u 10\<rbrace>\<^sub>u"
  by (insert assms) vcg

subsubsection \<open>Building more complicated stuff\<close>

lemma if_increment_manual:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&x =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &y =\<^sub>u 5\<rbrace>
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<triangleleft> b \<triangleright>\<^sub>r
  while &x <\<^sub>u &y * 2
  invr &x \<le>\<^sub>u &y * 2 \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x \<in>\<^sub>u {5, 10}\<^sub>u\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule cond_hoare_r)
   unfolding lens_indep_def
   apply (rule while_invr_hoare_r)
     apply rel_auto+
  apply (rule while_invr_hoare_r)
    apply rel_auto+
  done

lemma if_increment_method:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&x =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &y =\<^sub>u 5\<rbrace>
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<triangleleft> b \<triangleright>\<^sub>r
  while &x <\<^sub>u &y * 2
  invr &x \<le>\<^sub>u &y * 2 \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x \<in>\<^sub>u {5, 10}\<^sub>u\<rbrace>\<^sub>u"
  by (insert assms) vcg

lemma if_increment_method_step:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&x =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &y =\<^sub>u 5\<rbrace>
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<triangleleft> b \<triangleright>\<^sub>r
  while &x <\<^sub>u &y * 2
  invr &x \<le>\<^sub>u &y * 2 \<and> &y =\<^sub>u 5
  do x :== &x + 1 od
  \<lbrace>&x \<in>\<^sub>u {5, 10}\<^sub>u\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule cond_hoare_r) (* needed as vcg_step tries
utp_methods first and that messes up cond rule *)
   apply vcg_step+
      unfolding lens_indep_def
      apply vcg_step+
  done


subsection {*If-based programs*}

lemma if_manual:
  assumes "weak_lens x"
  and "x \<sharp> exp\<^sub>2"
  and "x \<sharp> exp\<^sub>3"
  shows "\<lbrace>true\<rbrace>
  x :== exp\<^sub>2 \<triangleleft> exp\<^sub>1 \<triangleright>\<^sub>r (x :== exp\<^sub>3)
  \<lbrace>&x =\<^sub>u exp\<^sub>2 \<or> &x =\<^sub>u exp\<^sub>3\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule cond_hoare_r)
   apply rel_simp
  apply pred_simp (* needed for UTP predicates; pred_blast needed for sets *)
  done

lemma if_true:
  assumes "weak_lens x"
  and "x \<sharp> exp\<^sub>1"
  and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
  x :== &x - exp\<^sub>2 \<triangleleft> true \<triangleright>\<^sub>r (x :== &x + exp\<^sub>2)
  \<lbrace>&x =\<^sub>u exp\<^sub>1 - exp\<^sub>2\<rbrace>\<^sub>u"
  using assms
  by rel_simp

lemma if_true_manual:
  assumes "weak_lens x"
  and "x \<sharp> exp\<^sub>1"
  and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
  x :== &x - exp\<^sub>2 \<triangleleft> true \<triangleright>\<^sub>r (x :== &x + exp\<^sub>2)
  \<lbrace>&x =\<^sub>u exp\<^sub>1 - exp\<^sub>2\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule cond_hoare_r)
   defer
   apply simp
   apply (rule hoare_false)
  apply rel_simp
  done

lemma if_true_method:
  assumes "weak_lens x"
  and "x \<sharp> exp\<^sub>1"
  and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
  x :== &x - exp\<^sub>2 \<triangleleft> true \<triangleright>\<^sub>r (x :== &x + exp\<^sub>2)
  \<lbrace>&x =\<^sub>u exp\<^sub>1 - exp\<^sub>2\<rbrace>\<^sub>u"
  using assms
  by vcg

lemma if_true_method_step:
  assumes "weak_lens x"
  and "x \<sharp> exp\<^sub>1"
  and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
  x :== &x - exp\<^sub>2 \<triangleleft> true \<triangleright>\<^sub>r (x :== &x + exp\<^sub>2)
  \<lbrace>&x =\<^sub>u exp\<^sub>1 - exp\<^sub>2\<rbrace>\<^sub>u"
  by (insert assms) vcg_step

lemma if_false:
  assumes "weak_lens x"
  and "x \<sharp> exp\<^sub>1"
  and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
  x :== &x - exp\<^sub>2 \<triangleleft> false \<triangleright>\<^sub>r (x :== &x + exp\<^sub>2)
  \<lbrace>&x =\<^sub>u exp\<^sub>1 + exp\<^sub>2\<rbrace>\<^sub>u"
  using assms
  by rel_simp

lemma if_false_manual:
  assumes "weak_lens x"
  and "x \<sharp> exp\<^sub>1"
  and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
  x :== &x - exp\<^sub>2 \<triangleleft> false \<triangleright>\<^sub>r (x :== &x + exp\<^sub>2)
  \<lbrace>&x =\<^sub>u exp\<^sub>1 + exp\<^sub>2\<rbrace>\<^sub>u"
  apply (insert assms)
  apply (rule cond_hoare_r)
   apply simp
   apply (rule hoare_false)
  apply rel_simp
  done

lemma if_false_method:
  assumes "weak_lens x"
  and "x \<sharp> exp\<^sub>1"
  and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
  x :== &x - exp\<^sub>2 \<triangleleft> false \<triangleright>\<^sub>r (x :== &x + exp\<^sub>2)
  \<lbrace>&x =\<^sub>u exp\<^sub>1 + exp\<^sub>2\<rbrace>\<^sub>u"
  using assms
  by vcg

lemma if_false_method_step:
  assumes "weak_lens x"
  and "x \<sharp> exp\<^sub>1"
  and "x \<sharp> exp\<^sub>2"
  shows "\<lbrace>&x =\<^sub>u exp\<^sub>1\<rbrace>
  x :== &x - exp\<^sub>2 \<triangleleft> false \<triangleright>\<^sub>r (x :== &x + exp\<^sub>2)
  \<lbrace>&x =\<^sub>u exp\<^sub>1 + exp\<^sub>2\<rbrace>\<^sub>u"
  by (insert assms) vcg_step

lemma if_base:
  assumes "weak_lens x"
  and "x \<sharp> exp\<^sub>2"
  and "x \<sharp> exp\<^sub>3"
  shows "\<lbrace>true\<rbrace>
  x :== exp\<^sub>2 \<triangleleft> exp\<^sub>1 \<triangleright>\<^sub>r (x :== exp\<^sub>3)
  \<lbrace>&x =\<^sub>u exp\<^sub>2 \<or> &x =\<^sub>u exp\<^sub>3\<rbrace>\<^sub>u"
  using assms
  by rel_auto


lemma if_method:
  assumes "weak_lens x"
  and "x \<sharp> exp\<^sub>2"
  and "x \<sharp> exp\<^sub>3"
  shows "\<lbrace>true\<rbrace>
  x :== exp\<^sub>2 \<triangleleft> exp\<^sub>1 \<triangleright>\<^sub>r (x :== exp\<^sub>3)
  \<lbrace>&x =\<^sub>u exp\<^sub>2 \<or> &x =\<^sub>u exp\<^sub>3\<rbrace>\<^sub>u"
  using assms
  by vcg

lemma if_method_step:
  assumes "weak_lens x"
  and "x \<sharp> exp\<^sub>2"
  and "x \<sharp> exp\<^sub>3"
  shows "\<lbrace>true\<rbrace>
  x :== exp\<^sub>2 \<triangleleft> exp\<^sub>1 \<triangleright>\<^sub>r (x :== exp\<^sub>3)
  \<lbrace>&x =\<^sub>u exp\<^sub>2 \<or> &x =\<^sub>u exp\<^sub>3\<rbrace>\<^sub>u"
  by (insert assms) vcg_step


end 