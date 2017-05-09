section \<open>Verification Condition Generator for Total Correctness\<close>

theory VCG_total
  imports utp_hoare_total
begin

method rules =
  rule seq_hoare_r_t|
  rule skip_hoare_r_t|
  rule cond_hoare_r_t|
  rule assigns_hoare_r'_t| (* merges two subgoals? *)
  rule assigns_hoare_r_t|  (* may not be useful *)
  rule assert_hoare_r_t|
  rule assume_hoare_r_t|
  rule while_hoare_r_t|
  rule while_hoare_r'_t|
  rule while_invr_hoare_r_t

value "[x. x \<in> {0::int, 1, 2}]"
(* alphabet 'a josh = xs :: \<open>'a list\<close> *)

lemma bubble_sort_manual:
  assumes "mwb_lens xs" and "weak_lens n" and "weak_lens newn" and "weak_lens i"
      and "xs \<bowtie> n" and "xs \<bowtie> newn" and "xs \<bowtie> i"
      and "n \<bowtie> newn" and "n \<bowtie> i"
      and "newn \<bowtie> i"
  shows
  "\<lbrace>true\<rbrace>
  n \<Midarrow> #\<^sub>u(&xs);;
  (#\<^sub>u(&xs) \<ge>\<^sub>u &n \<and> &n \<ge>\<^sub>u 0)\<^sup>\<top>\<^sup>C;;
  while &n >\<^sub>u \<guillemotleft>0::nat\<guillemotright>
  invr #\<^sub>u(&xs) \<ge>\<^sub>u &n \<and> &n \<ge>\<^sub>u 0
  do
    newn \<Midarrow> 0;;
    i \<Midarrow> \<guillemotleft>1::nat\<guillemotright>;;
    (&n-1 \<ge>\<^sub>u &i \<and> &i \<ge>\<^sub>u 1)\<^sup>\<top>\<^sup>C;;
    while &i \<le>\<^sub>u &n-1
    invr &n-1 \<ge>\<^sub>u &i \<and> &i \<ge>\<^sub>u 1
    do
      bif &xs\<lparr>&i-1\<rparr>\<^sub>u >\<^sub>u &xs\<lparr>&i\<rparr>\<^sub>u then
        xs \<Midarrow> take\<^sub>u(&i-1, &xs) ^\<^sub>u \<langle>&xs\<lparr>&i\<rparr>\<^sub>u, &xs\<lparr>&i-1\<rparr>\<^sub>u\<rangle> ^\<^sub>u drop\<^sub>u(&i+1, &xs);;
        newn \<Midarrow> &i
      else
        II
      eif;;
      i \<Midarrow> &i + 1
    od;;
    n \<Midarrow> &newn
  od
  \<lbrace>sorted\<^sub>u(&xs)\<rbrace>\<^sub>D"
  oops

end
