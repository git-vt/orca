section \<open>Verification Condition Testing\<close>

theory features_test
  imports "utp_hoare_total"
begin

subsection {*Even count*}

lemma even_count:
   assumes "weak_lens i" and  "weak_lens a" and  "weak_lens j"  and  "weak_lens n"and
           "i \<bowtie> a" and "i \<bowtie> j" and "i \<bowtie> n"  "a \<bowtie> j" and "a \<bowtie> n" and "j \<bowtie> n" 
   shows 
   "\<lbrace>&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright>\<rbrace>
       i:== &a ;; j :== \<guillemotleft>0::int\<guillemotright> ;; 
       (&a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> &j =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &i =\<^sub>u &a)\<^sup>\<top>;; 
     while  &i <\<^sub>u &n 
       invr  &a =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &n =\<^sub>u \<guillemotleft>1::int\<guillemotright> \<and> &j =\<^sub>u (((&i + 1) - &a) div 2) \<and> &i \<le>\<^sub>u &n \<and>  &i \<ge>\<^sub>u &a
       do (j :== &j + \<guillemotleft>1\<guillemotright> \<triangleleft> &i mod \<guillemotleft>2\<guillemotright> =\<^sub>u  \<guillemotleft>0::int\<guillemotright>\<triangleright>\<^sub>r II) ;;  i :== &i + \<guillemotleft>1\<guillemotright> od
     \<lbrace>&j =\<^sub>u \<guillemotleft>1::int\<guillemotright>\<rbrace>\<^sub>u"
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
subsection {*catch feature*}

lemma "(TRY THROW CATCH SKIP END ) = SKIP"
  by rel_auto

lemma "(TRY \<langle>a\<rangle>\<^sub>C CATCH  SKIP  END ) = \<langle>a\<rangle>\<^sub>C"
  by rel_auto

lemma "(TRY (SKIP ;; \<langle>a\<rangle>\<^sub>C) CATCH SKIP END ) =  \<langle>a\<rangle>\<^sub>C"
      by rel_auto blast + 

lemma "(TRY (SKIP ;; \<langle>a\<rangle>\<^sub>C;;THROW) CATCH SKIP END ) = \<langle>a\<rangle>\<^sub>C"
      by rel_auto blast + 

lemma "(TRY (SKIP ;; \<langle>a\<rangle>\<^sub>C;;THROW) CATCH \<langle>b\<rangle>\<^sub>C END) = (\<langle>a\<rangle>\<^sub>C ;; \<langle>b\<rangle>\<^sub>C)"
      by rel_auto blast + 

lemma "(TRY  THROW;; \<langle>a\<rangle>\<^sub>C CATCH SKIP END) = SKIP "
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

end
