section \<open>Verification Condition Generator for Total Correctness\<close>

theory VCG_total
  imports "../utp_hoare_total"
begin

method rules =
  rule seq_hoare_r_t|
  rule skip_hoare_r_t|
  rule cond_hoare_r_t|
  rule assigns_hoare_r'_t| (* merges two subgoals? *)
(*   rule assigns_hoare_r_t|  (* not useful for splitting/merging goals, but necessary for pred_* *) *)
  rule assert_hoare_r_t|
  rule assume_hoare_r_t|
  rule while_hoare_r_t|
  rule while_hoare_r'_t|
  rule while_invr_hoare_r_t

(* once proof done, remove any unnecessary bits from invariants/assumptions *)
lemma bubble_sort_manual:
  assumes "mwb_lens xs" and "mwb_lens n" and "mwb_lens newn" and "mwb_lens i"
      and "xs \<bowtie> n" and "xs \<bowtie> newn" and "xs \<bowtie> i"
      and "n \<bowtie> newn" and "n \<bowtie> i"
      and "newn \<bowtie> i"
  shows
  "\<lbrace>true\<rbrace>
  n \<Midarrow> #\<^sub>u(&xs);;
  (&n =\<^sub>u #\<^sub>u(&xs))\<^sup>\<top>\<^sup>C;;
  while &n >\<^sub>u 0
  invr &n \<le>\<^sub>u #\<^sub>u(&xs) \<and> &n \<ge>\<^sub>u 0 \<and> sorted\<^sub>u(drop\<^sub>u(&n, &xs))
  do
    newn \<Midarrow> 0;;
    i \<Midarrow> 1;;
    (* If the outer loop is executing then we know the list isn't empty. *)
    (#\<^sub>u(&xs) >\<^sub>u 0 \<and> &newn =\<^sub>u 0 \<and> &i =\<^sub>u 1 \<and> &n \<le>\<^sub>u #\<^sub>u(&xs) \<and> &n >\<^sub>u 0 \<and> sorted\<^sub>u(drop\<^sub>u(&n, &xs)))\<^sup>\<top>\<^sup>C;;
    while &i <\<^sub>u &n
    (* If the inner loop ever executes then we know the list has more than one element (#\<^sub>u(&xs) >\<^sub>u 1)
       ...but where do we put that info? Is it even necessary? *)
    invr &i \<ge>\<^sub>u 1 \<and> &i \<le>\<^sub>u &n \<and> &newn \<le>\<^sub>u &i \<and> &newn <\<^sub>u &n \<and> &n \<le>\<^sub>u #\<^sub>u(&xs) \<and> &n >\<^sub>u 0 \<and> sorted\<^sub>u(drop\<^sub>u(&n, &xs))
    do
      bif &xs\<lparr>&i-1\<rparr>\<^sub>u >\<^sub>u &xs\<lparr>&i\<rparr>\<^sub>u then
        xs \<Midarrow> take\<^sub>u(&i-1, &xs) ^\<^sub>u \<langle>&xs\<lparr>&i\<rparr>\<^sub>u, &xs\<lparr>&i-1\<rparr>\<^sub>u\<rangle> ^\<^sub>u drop\<^sub>u(&i+1, &xs);;
        newn \<Midarrow> &i
      else
        SKIP
      eif;;
      i \<Midarrow> &i + 1
    od;;
    n \<Midarrow> &newn
  od
  \<lbrace>sorted\<^sub>u(&xs)\<rbrace>\<^sub>D"
  apply (insert assms)
  apply (rule seq_hoare_r_t[of _ _ true])
   defer
   apply (rule seq_hoare_r_t)
    apply (rule assume_hoare_r_t)
     apply (rule skip_hoare_r_t)
    apply rel_auto
   apply (rule while_invr_hoare_r_t)
     apply (rule seq_hoare_r_t)
      defer
      apply (rule seq_hoare_r_t[of _ _ true])
       defer
       apply (rule seq_hoare_r_t)
        apply (rule assume_hoare_r_t)
         apply (rule skip_hoare_r_t)
        apply rel_auto
       apply (rule seq_hoare_r_t)
        apply (rule while_invr_hoare_r_t)
          apply (rule seq_hoare_r_t)
           apply (rule cond_hoare_r_t)
            defer
            apply (rule skip_hoare_r_t)
           prefer 4
           apply (rule assigns_hoare_r'_t) (* use to instantiate schematic variable precondition *)
          prefer 9
          apply (rule seq_hoare_r_t)
           prefer 2
           apply (rule assigns_hoare_r'_t)
          prefer 9
          apply (rule assigns_hoare_r'_t)
         apply (rule assigns_hoare_r_t)
         prefer 2
         apply (rule assigns_hoare_r_t)
         prefer 8
         apply (rule assigns_hoare_r_t)
         prefer 8
         apply rel_auto
        apply rel_auto
       apply rel_auto
      unfolding lens_indep_def
      apply pred_auto
       prefer 3
       apply pred_auto
      prefer 4
      apply pred_auto
     prefer 4
     apply pred_auto
    prefer 3
    apply pred_simp
    defer
    apply (smt diff_diff_cancel diff_le_self length_take less_imp_le min.absorb2 not_le nth_Cons_0 nth_Cons_Suc nth_append nth_append_length order_trans)
   apply (smt Suc_diff_Suc Suc_le_lessD Suc_pred drop_Suc_Cons drop_append id_take_nth_drop leD length_take less_imp_le min_def min_less_iff_conj sorted_append)
(*       apply (case_tac "get\<^bsub>xs\<^esub> A")
       apply auto *)

end
