section \<open>Examples using ML-level VCG for Total Correctness\<close>

theory examples_vcg_total
  imports "../hoare/VCG_total_ML"
begin

subsection Increment

lemma increment_manual:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x \<Midarrow> 0;;
  (&x =\<^sub>u 0 \<and> &y =\<^sub>u 5)\<^sup>\<top>\<^sup>C;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x \<Midarrow> &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  apply (insert assms)
  apply (rule seq_hoare_r_t)
   apply (rule seq_hoare_r_t[of _ _ true])
    apply rel_auto (* seq rule gives us a value of true in postcondition, which is trivial *)
   apply (rule assume_hoare_r_t)
    apply (rule skip_abr_hoare_r_t)
   apply rel_auto
  apply (rule while_invr_hoare_r_t)
    apply (rule assigns_abr_hoare_r_t)
    unfolding lens_indep_def
    apply pred_auto
   apply pred_auto
  apply pred_auto
  done

lemma increment_tactic1:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x \<Midarrow> 0;;
  x \<Midarrow> 0;;
  (&x =\<^sub>u 0 \<and> &y =\<^sub>u 5)\<^sup>\<top>\<^sup>C;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x \<Midarrow> &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  apply (tactic \<open>vcg_seq_split @{context} 1\<close>)+
  apply (tactic \<open>vcg_rule_tac @{context} 1\<close>)+
  defer
  apply (tactic \<open>vcg_rule_tac @{context} 1\<close>)+
  apply rel_auto
  defer
  apply rel_auto
  apply (tactic \<open>vcg_rule_tac @{context} 1\<close>)+
  apply (tactic \<open>vcg_insert_assms_tac @{context}\<close>)
  apply (tactic \<open>vcg_unfold_tac @{context}\<close>)
  apply pred_auto+
  done

lemma increment_tactic2:
  assumes "vwb_lens x" and "x \<bowtie> y"
  shows
  "\<lbrace>&y =\<^sub>u \<guillemotleft>5::int\<guillemotright>\<rbrace>
  x \<Midarrow> 0;;
  x \<Midarrow> 0;;
  (&x =\<^sub>u 0 \<and> &y =\<^sub>u 5)\<^sup>\<top>\<^sup>C;;
  while &x <\<^sub>u &y
  invr &x \<le>\<^sub>u &y \<and> &y =\<^sub>u 5
  do x \<Midarrow> &x + 1 od
  \<lbrace>&x =\<^sub>u 5\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  apply (tactic \<open>vcg_rules_all_tac @{context}\<close>)
  apply (tactic \<open>vcg_pre_tac @{context}\<close>)
  apply vcg_autos+
  done

subsection \<open>Even count\<close>

lemma even_count_tactic1:
  assumes "vwb_lens i" and "weak_lens start" and "vwb_lens j" and "weak_lens endd"
  and "i \<bowtie> start" and "i \<bowtie> j" and "i \<bowtie> endd" and "start \<bowtie> j" and "start \<bowtie> endd" and "j \<bowtie> endd"
  shows
  "\<lbrace>&start =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &endd =\<^sub>u 1\<rbrace>
    i \<Midarrow> &start;;
    j \<Midarrow> 0;;
    (&start =\<^sub>u 0 \<and> &endd =\<^sub>u 1 \<and> &j =\<^sub>u 0 \<and> &i =\<^sub>u &start)\<^sup>\<top>\<^sup>C;;
    while &i <\<^sub>u &endd
    invr &start =\<^sub>u 0 \<and> &endd =\<^sub>u 1 \<and> &j =\<^sub>u (((&i + 1) - &start) div 2) \<and> &i \<le>\<^sub>u &endd \<and> &i \<ge>\<^sub>u &start
    do
      bif &i mod 2 =\<^sub>u 0 then
        j \<Midarrow> &j + 1
      else
        SKIP\<^sub>A\<^sub>B\<^sub>R
      eif;;
      i \<Midarrow> &i + 1
    od
  \<lbrace>&j =\<^sub>u 1\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  apply (tactic \<open>vcg_rules_all_tac @{context}\<close>)
  apply vcg_autos
  apply vcg_autos
  apply (tactic \<open>vcg_rules_all_tac' @{context}\<close>)
  apply (tactic \<open>vcg_rules_all_tac' @{context}\<close>)
  apply (tactic \<open>vcg_pre_tac @{context}\<close>)
  apply vcg_autos+
  done


lemma even_count_tactic2:
  assumes "vwb_lens i" and "weak_lens start" and "vwb_lens j" and "weak_lens endd"
  and "i \<bowtie> start" and "i \<bowtie> j" and "i \<bowtie> endd" and "start \<bowtie> j" and "start \<bowtie> endd" and "j \<bowtie> endd"
  shows
  "\<lbrace>&start =\<^sub>u \<guillemotleft>0::int\<guillemotright> \<and> &endd =\<^sub>u 1\<rbrace>
    i \<Midarrow> &start;;
    j \<Midarrow> 0;;
    (&start =\<^sub>u 0 \<and> &endd =\<^sub>u 1 \<and> &j =\<^sub>u 0 \<and> &i =\<^sub>u &start)\<^sup>\<top>\<^sup>C;;
    while &i <\<^sub>u &endd
    invr &start =\<^sub>u 0 \<and> &endd =\<^sub>u 1 \<and> &j =\<^sub>u (((&i + 1) - &start) div 2) \<and> &i \<le>\<^sub>u &endd \<and> &i \<ge>\<^sub>u &start
    do
      bif &i mod 2 =\<^sub>u 0 then
        j \<Midarrow> &j + 1
      else
        SKIP\<^sub>A\<^sub>B\<^sub>R
      eif;;
      i \<Midarrow> &i + 1
    od
  \<lbrace>&j =\<^sub>u 1\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  apply (tactic \<open>vcg_rules_tac' @{context}\<close>)
  defer
  apply (tactic \<open>vcg_rules_tac' @{context}\<close>)
  apply vcg_autos
  apply (tactic \<open>vcg_rules_tac' @{context}\<close>)
  defer
  apply (tactic \<open>vcg_rules_tac' @{context}\<close>)
(*   apply (tactic \<open>vcg_pre_tac @{context}\<close>) *)
  apply (insert assms)
  apply (unfold lens_indep_def)
  using mod_pos_pos_trivial apply pred_auto
  apply pred_auto
  apply pred_auto
  apply pred_auto
  using mod_pos_pos_trivial apply pred_auto
  done

end
