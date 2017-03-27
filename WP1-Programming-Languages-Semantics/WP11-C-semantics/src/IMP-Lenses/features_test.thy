section \<open>Verification Condition Testing\<close>

theory features_test
  imports "utp/utp_hoare"
begin

subsection {*Even count*}

lemma even_count:
   assumes "vwb_lens i" and  "weak_lens a" and  "vwb_lens j"  and  "weak_lens n"and
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
     apply rel_auto[1]
    apply rel_auto[1]
    using mod_pos_pos_trivial apply auto[1]
   apply rel_auto[1]
  apply rel_auto[1]
 apply rel_auto[1]
 apply rel_auto[1]
done

subsection {*testing features*}

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

end
