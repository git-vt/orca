section \<open>Verification Condition Testing\<close>

theory features_test
  imports "utp_hoare_total"
begin

subsection {*Even count*}

term "

i:= &a ;; j := \<guillemotleft>0::int\<guillemotright> ;; 
 WHILE  &i <\<^sub>u &n  
   DO (IF &i mod \<guillemotleft>2\<guillemotright> =\<^sub>u  \<guillemotleft>0::int\<guillemotright> 
       THEN  j := &j + \<guillemotleft>1\<guillemotright> 
       ELSE SKIP) ;;  
       i := &i + \<guillemotleft>1\<guillemotright> 
   OD

"
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


lemma even_count_total:
   "\<lbrace>&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> 
     \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens a\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>weak_lens n\<guillemotright> \<and> 
     \<guillemotleft>i \<bowtie> a\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>  \<and> \<guillemotleft>i \<bowtie> n\<guillemotright> \<and> \<guillemotleft>a \<bowtie> j\<guillemotright> \<and> \<guillemotleft>a \<bowtie> n\<guillemotright> \<and> \<guillemotleft>j \<bowtie> n\<guillemotright>\<rbrace>
      i:= &a ;; 
      j := \<guillemotleft>0::int\<guillemotright> ;; 
     (&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> &j =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &i =\<^sub>u &a \<and> 
      \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens a\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>weak_lens n\<guillemotright> \<and> 
      \<guillemotleft>i \<bowtie> a\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>  \<and> \<guillemotleft>i \<bowtie> n\<guillemotright> \<and> \<guillemotleft>a \<bowtie> j\<guillemotright> \<and> \<guillemotleft>a \<bowtie> n\<guillemotright> \<and> \<guillemotleft>j \<bowtie> n\<guillemotright>)\<^sup>\<top>\<^sup>C;; 
     WHILE  &i <\<^sub>u &n 
       invr  &a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> 
             \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens a\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>weak_lens n\<guillemotright> \<and> 
             \<guillemotleft>i \<bowtie> a\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>  \<and> \<guillemotleft>i \<bowtie> n\<guillemotright> \<and> \<guillemotleft>a \<bowtie> j\<guillemotright> \<and> \<guillemotleft>a \<bowtie> n\<guillemotright> \<and> \<guillemotleft>j \<bowtie> n\<guillemotright>\<and> 
             &j =\<^sub>u (((&i + 1) - &a) div 2) \<and> &i \<le>\<^sub>u &n \<and>  &i \<ge>\<^sub>u &a
       DO (IF &i mod \<guillemotleft>2\<guillemotright> =\<^sub>u  \<guillemotleft>0::int\<guillemotright> 
           THEN  j := &j + \<guillemotleft>1\<guillemotright> 
           ELSE SKIP) ;;  
           i := &i + \<guillemotleft>1\<guillemotright> 
       OD
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

lemma "(TRY THROW CATCH SKIP END) = SKIP"
  by rel_auto

lemma "(TRY \<langle>a\<rangle>\<^sub>C CATCH SKIP END) = \<langle>a\<rangle>\<^sub>C"
  by rel_auto

lemma "(TRY (SKIP ;; \<langle>a\<rangle>\<^sub>C;;THROW) CATCH \<langle>b\<rangle>\<^sub>C END) = (\<langle>a\<rangle>\<^sub>C ;; \<langle>b\<rangle>\<^sub>C)"
  by rel_auto blast + 

lemma "(TRY THROW ;; \<langle>a\<rangle>\<^sub>C CATCH SKIP END) = SKIP "
  by rel_auto blast + 

lemma "(TRY (SKIP ;; \<langle>a\<rangle>\<^sub>C) CATCH SKIP END ) =  \<langle>a\<rangle>\<^sub>C"
  by rel_auto blast + 

lemma "(TRY (SKIP ;; \<langle>a\<rangle>\<^sub>C;;THROW) CATCH SKIP END) = \<langle>a\<rangle>\<^sub>C"
  by rel_auto blast + 

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

lemma   block_c_test1:
  shows "\<lbrace> \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace> 
          i := \<guillemotleft>2::int\<guillemotright>;; j := \<guillemotleft>0::int\<guillemotright> ;; 
          block_c (j := \<guillemotleft>5\<guillemotright>;; i:= \<guillemotleft>5\<guillemotright>) (II)
                  (\<lambda> (s, s') (t, t').  i:= \<guillemotleft>\<lbrakk>\<langle>id\<rangle>\<^sub>s i\<rbrakk>\<^sub>e ((cp_vars.more o des_vars.more) s)\<guillemotright> ;; 
                     j:= \<guillemotleft>\<lbrakk>\<langle>id\<rangle>\<^sub>s j\<rbrakk>\<^sub>e ((cp_vars.more o des_vars.more) s)\<guillemotright>) 
                  (\<lambda> (s, s') (t, t').  II)
         \<lbrace>&j =\<^sub>u \<guillemotleft>0::int\<guillemotright>\<and> &i =\<^sub>u \<guillemotleft>2::int\<guillemotright>\<rbrace>\<^sub>D"
  using assms  by rel_simp

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

lemma   block_c_test2:
  shows "\<lbrace> \<guillemotleft>weak_lens i\<guillemotright> \<and> \<guillemotleft>weak_lens j\<guillemotright> \<and> \<guillemotleft>i \<bowtie> j\<guillemotright>\<rbrace> 
          i := \<guillemotleft>2::int\<guillemotright>;; j := \<guillemotleft>0::int\<guillemotright> ;; 
          block_c (j := \<guillemotleft>5\<guillemotright>;; i:= \<guillemotleft>5\<guillemotright>) (II)
                  (\<lambda> (s, s') (t, t').  i:= \<guillemotleft>\<lbrakk>\<langle>id\<rangle>\<^sub>s i\<rbrakk>\<^sub>e ((cp_vars.more o des_vars.more) t)\<guillemotright> ;; 
                     j:= \<guillemotleft>\<lbrakk>\<langle>id\<rangle>\<^sub>s j\<rbrakk>\<^sub>e ((cp_vars.more o des_vars.more) t)\<guillemotright>) 
                  (\<lambda> (s, s') (t, t').  II)
         \<lbrace>&j =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<and> &i =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>\<^sub>D"
  using assms  unfolding lens_indep_def by rel_simp

subsection {*Infinite loops*}
text{*The next two lemmas are the witness needed to justify the theory of designs.*}

lemma 1:"while\<^sub>\<bottom> true do II od = true"
  unfolding while_bot_def
  apply rel_simp unfolding gfp_def apply transfer apply auto done

lemma "in\<alpha> \<sharp> ( x :== \<guillemotleft>c\<guillemotright>) \<Longrightarrow> while\<^sub>\<bottom> true  do II od;; x :== \<guillemotleft>c\<guillemotright> = x :== \<guillemotleft>c\<guillemotright>"
  apply (subst 1) apply (simp only: assigns_r.abs_eq )  
  apply (simp only: seqr_def) apply simp
 apply rel_simp  apply transfer apply auto done

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
