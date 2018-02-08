(*****************************************************************************************)
(* Orca: A Functional Correctness Verifier for Imperative Programs Based on Isabelle/UTP *)
(*                                                                                       *)
(* Copyright (c) 2016-2018 Virginia Tech, USA                                            *)
(* This software may be distributed and modified according to the terms of               *)
(* the GNU Lesser General Public License version 3.0 or any later version.               *)
(* Note that NO WARRANTY is provided.                                                    *)
(* See CONTRIBUTORS, LICENSE and CITATION files for details.                             *)
(*****************************************************************************************)

subsection {* Relational Hoare calculus *}

theory utp_hoare_helper
imports utp_hoare_total 
begin
named_theorems utp_hoare_hp

subsection {*Try Catch Laws*}

text{*In this section we introduce the algebraic laws of programming related to the assignment
      statement.*}


lemma try_catch_unfold_hoare: (*because seq is assoc*)
  "\<lbrace>p\<rbrace>try  R ;; P catch  Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace>R ;; try  P catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
   apply pred_simp
   apply rel_simp
   apply auto
   apply smt+
done

lemma try_catch_abr_fold_hoare[utp_hoare_hp]: (*because seq is assoc*)
  "\<lbrace>p\<rbrace>R ;; try  P catch Q end \<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace>try  R ;; P catch  Q end \<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
   apply pred_simp
   apply rel_simp
   apply auto
   apply smt+
done

lemma try_catch_abr_throw_abr_hoare [utp_hoare_hp]:
  "\<lbrace>p\<rbrace> try THROW\<^sub>A\<^sub>B\<^sub>R  catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace> Q \<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
   apply pred_simp
   apply rel_simp
   apply auto
   apply smt+
done

lemma try_catch_abr_skip_abr_hoare [utp_hoare_hp]:
  "\<lbrace>p\<rbrace>try  SKIP\<^sub>A\<^sub>B\<^sub>R catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace>SKIP\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
   apply pred_simp
   apply rel_simp
   apply auto
   apply smt
done

lemma try_catch_abr_assigns_abr_hoare [utp_hoare_hp]:
  "\<lbrace>p\<rbrace>try   \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace> \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
   apply pred_simp
   apply rel_simp
   apply auto
   apply smt+
done

subsection {*Examples*}

lemma
  "\<lbrace>p\<rbrace> try THROW\<^sub>A\<^sub>B\<^sub>R ;; SKIP\<^sub>A\<^sub>B\<^sub>R catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>Q\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
   by (simp only: utp_hoare_hp  uabr_comp)

lemma 
  "\<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R ;; try \<langle>\<sigma>\<rangle>\<^sub>A\<^sub>B\<^sub>R catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace>Q \<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by (simp only: utp_hoare_hp  uabr_comp)

lemma
  "\<lbrace>p\<rbrace>THROW\<^sub>A\<^sub>B\<^sub>R ;; try Simpl\<^sub>A\<^sub>B\<^sub>R P catch Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = \<lbrace>p\<rbrace>Q\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
  by (simp only: utp_hoare_hp  uabr_comp)

lemma 
  "\<lbrace>p\<rbrace> try THROW\<^sub>A\<^sub>B\<^sub>R;; Simpl\<^sub>A\<^sub>B\<^sub>R P catch Simpl\<^sub>A\<^sub>B\<^sub>R Q end\<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R = 
   \<lbrace>p\<rbrace>Simpl\<^sub>A\<^sub>B\<^sub>R Q \<lbrace>q\<rbrace>\<^sub>A\<^sub>B\<^sub>R"
   by (simp only: utp_hoare_hp  uabr_comp)


end

