(******************************************************************************
 * Orca: A Functional Correctness Verifier for Imperative Programs
 *       Based on Isabelle/UTP
 *
 * Copyright (c) 2016-2018 Virginia Tech, USA
 *               2016-2018 Technische Universität München, Germany
 *               2016-2018 University of York, UK
 *               2016-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * This software may be distributed and modified according to the terms of
 * the GNU Lesser General Public License version 3.0 or any later version.
 * Note that NO WARRANTY is provided.
 *
 * See CONTRIBUTORS, LICENSE and CITATION files for details.
 ******************************************************************************)

theory algorithms

  imports "../Backend/VCG/vcg"
begin

section \<open>Simple algorithms\<close>

text 
\<open>
 Through these experiments I want to observe the following problems:
     \begin{itemize}
       \item I want to deal with the problem of nested existential(SOLVED).
       \item I want to deal with the problem of blow up due to the semantic machinery coming with lenses(SOLVED).
       \item I want to have modularity(NOT SOLVED).
     \end{itemize}
\<close>
subsection \<open>Increment method\<close>
  
lemma increment_method: 
  assumes "vwb_lens x"
  shows  
    "\<lbrace>\<guillemotleft>a\<guillemotright> >\<^sub>u 0\<rbrace>
   x :== 0 ; 
   INVAR \<guillemotleft>a\<guillemotright> >\<^sub>u 0 \<and> \<guillemotleft>a\<guillemotright> \<ge>\<^sub>u &x 
   VRT \<guillemotleft>(measure o Rep_uexpr) (\<guillemotleft>a\<guillemotright> - &x)\<guillemotright> 
   WHILE &x <\<^sub>u \<guillemotleft>a\<guillemotright> DO x:== (&x + 1) OD
 \<lbrace>\<guillemotleft>a\<guillemotright> =\<^sub>u &x\<rbrace>\<^sub>P"
  apply (insert assms) (*Make this automatic *)
  apply vcg_hoare_sp_steps_pp_beautify                           
  done
    
subsection \<open>even count program\<close> 

lemma even_count_gen:
  assumes "lens_indep_all [i,j]"
  assumes "vwb_lens i" "vwb_lens j"  
  shows  
    "\<lbrace>\<guillemotleft>a\<guillemotright> >\<^sub>u 0 \<rbrace>
   i :== \<guillemotleft>0::int\<guillemotright>;
   j :== 0 ; 
   INVAR  (&j =\<^sub>u (&i + 1) div \<guillemotleft>2\<guillemotright> \<and> &i \<le>\<^sub>u \<guillemotleft>a\<guillemotright>) 
   VRT \<guillemotleft>measure (nat o (Rep_uexpr (\<guillemotleft>a\<guillemotright> - &i)))\<guillemotright>
   WHILE &i <\<^sub>u \<guillemotleft>a\<guillemotright>
   DO
     IF &i mod \<guillemotleft>2\<guillemotright> =\<^sub>u 0 
     THEN j :== (&j + 1)
     ELSE SKIP 
     FI;
    i :== (&i + 1)
   OD
 \<lbrace>&j =\<^sub>u (\<guillemotleft>a\<guillemotright> + 1)div \<guillemotleft>2\<guillemotright>\<rbrace>\<^sub>P" 
  apply (insert assms)(*Make this automatic*)
  apply vcg_hoare_sp_steps_pp_beautify
   apply presburger+    
  done   

lemma even_count_gen':
  assumes "lens_indep_all [i,j]"
  assumes "vwb_lens i" "vwb_lens j"  
  shows  
    "\<lbrace>\<guillemotleft>a\<guillemotright> >\<^sub>u 0\<rbrace>
   i :== \<guillemotleft>0::int\<guillemotright>;
   j :== 0 ; 
   INVAR  (&j =\<^sub>u (&i + 1) div 2 \<and> &i \<le>\<^sub>u \<guillemotleft>a\<guillemotright>) 
   VRT \<guillemotleft>measure (nat o (Rep_uexpr (\<guillemotleft>a\<guillemotright> - &i)))\<guillemotright>
   WHILE &i <\<^sub>u \<guillemotleft>a\<guillemotright>
   DO
     IF &i mod 2 =\<^sub>u 0 
     THEN j :== (&j + 1)
     ELSE SKIP 
     FI;
    i :== (&i + 1)
   OD
 \<lbrace>&j =\<^sub>u (\<guillemotleft>a\<guillemotright> + 1)div 2\<rbrace>\<^sub>P"  
  apply (insert assms)(*Make this automatic*)
  apply vcg_hoare_sp_steps_pp_beautify
   apply (simp_all add: zdiv_zadd1_eq)
  done    
    
subsection \<open>sqrt program\<close>
  
definition Isqrt :: "int \<Rightarrow> int \<Rightarrow> bool" 
   where "Isqrt n\<^sub>0 r \<equiv> 0\<le>r \<and> (r-1)\<^sup>2 \<le> n\<^sub>0" 
     
lemma Isqrt_aux:
  "0 \<le> n\<^sub>0 \<Longrightarrow> Isqrt n\<^sub>0 1"
  "\<lbrakk>0 \<le> n\<^sub>0; r * r \<le> n\<^sub>0; Isqrt n\<^sub>0 r\<rbrakk> \<Longrightarrow> Isqrt n\<^sub>0 (r + 1)"
  "\<lbrakk>0 \<le> n\<^sub>0; \<not> r * r \<le> n\<^sub>0; Isqrt n\<^sub>0 r\<rbrakk> \<Longrightarrow> (r - 1)\<^sup>2 \<le> n\<^sub>0 \<and> n\<^sub>0 < r\<^sup>2"
  "Isqrt n\<^sub>0 r \<Longrightarrow> r * r \<le> n\<^sub>0 \<Longrightarrow> r\<le>n\<^sub>0"
  "\<lbrakk>0 \<le> n\<^sub>0; \<not> r * r \<le> n\<^sub>0; Isqrt n\<^sub>0 r\<rbrakk> \<Longrightarrow> 0 < r"
  apply (auto simp: Isqrt_def power2_eq_square algebra_simps)
  by (smt combine_common_factor mult_right_mono semiring_normalization_rules(3))
      
lemma sqrt_prog_correct:
  assumes "vwb_lens r"
  shows
    "\<lbrace>0 \<le>\<^sub>u \<guillemotleft>a\<guillemotright>\<rbrace>
   r :== 1 ; 
   INVAR 0\<le>\<^sub>u \<guillemotleft>a\<guillemotright> \<and> bop Isqrt \<guillemotleft>a\<guillemotright> (&r)
   VRT  \<guillemotleft>measure (nat o (Rep_uexpr ((\<guillemotleft>a\<guillemotright> + 1) - &r)))\<guillemotright>
   WHILE (&r * &r \<le>\<^sub>u \<guillemotleft>a\<guillemotright>)
   DO 
    r :== (&r + 1)
   OD;
   r :== (&r - 1)
 \<lbrace>0\<le>\<^sub>u &r \<and> uop power2 (&r) \<le>\<^sub>u \<guillemotleft>a\<guillemotright> \<and> \<guillemotleft>a\<guillemotright> <\<^sub>u uop power2 (&r + 1)\<rbrace>\<^sub>P" 
  apply (insert assms)
  supply Isqrt_aux [simp]
  apply (vcg_hoare_sp_steps_pp_beautify)
  done    
    
subsection \<open>gcd\<close>
  
text \<open>In the followin we illustrate the effect of domain theory based approach. 
      Namely, in the lemma gcd_correct we use the hard coded max function 
      @{term "(trop If (&r >\<^sub>u &x) (&r) (&x))"}. This leads to long proof. 
      However in gcd_correct' we use the max function from HOL library. 
      This leads to a shorter proof since max library contains the necessary lemmas that simplify
      the reasoning.\<close>
  
lemma gcd_correct:
  assumes "lens_indep_all [r, x]"
  assumes "vwb_lens r" "vwb_lens x" 
  shows  
    "\<lbrace>&r =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> \<guillemotleft>b\<guillemotright> >\<^sub>u 0 \<and> \<guillemotleft>a\<guillemotright>>\<^sub>u 0\<rbrace> 
   INVAR &r >\<^sub>u0 \<and> &x >\<^sub>u 0 \<and> bop gcd (&r) (&x) =\<^sub>u  bop gcd \<guillemotleft>a\<guillemotright> \<guillemotleft>b\<guillemotright>
   VRT \<guillemotleft>measure (Rep_uexpr (trop If (&r >\<^sub>u &x) (&r) (&x)))\<guillemotright>
   WHILE \<not>(&r =\<^sub>u &x)
   DO
    IF &r >\<^sub>u &x
    THEN r :== (&r - &x)
    ELSE x :== (&x - &r)
    FI
   OD
 \<lbrace>&r =\<^sub>u &x \<and> &r =\<^sub>u bop gcd \<guillemotleft>a\<guillemotright> \<guillemotleft>b\<guillemotright>\<rbrace>\<^sub>P"
  apply (insert assms)   
  apply vcg_hoare_sp_steps_pp_beautify
     apply (auto simp: gcd_diff1_nat)
   apply (metis gcd.commute gcd_diff1_nat not_le)+
  done  
     
lemma gcd_correct':
  assumes "lens_indep_all [r, x]"
  assumes "vwb_lens r" "vwb_lens x" 
  shows  
    "\<lbrace>&r =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> \<guillemotleft>b\<guillemotright>>\<^sub>u 0 \<and> \<guillemotleft>a\<guillemotright>>\<^sub>u 0\<rbrace> 
   INVAR &r >\<^sub>u0 \<and> &x >\<^sub>u 0 \<and> bop gcd (&r) (&x) =\<^sub>u  bop gcd \<guillemotleft>a\<guillemotright> \<guillemotleft>b\<guillemotright>
   VRT \<guillemotleft>measure (Rep_uexpr (bop max (&r) (&x)))\<guillemotright>
   WHILE \<not>(&r =\<^sub>u &x)
   DO
    IF &r >\<^sub>u &x
    THEN r :== (&r - &x)
    ELSE x :== (&x - &r)
    FI
   OD
 \<lbrace>&r =\<^sub>u &x \<and> &r =\<^sub>u bop gcd \<guillemotleft>a\<guillemotright> \<guillemotleft>b\<guillemotright>\<rbrace>\<^sub>P"
  apply (insert assms)  
  apply vcg_hoare_sp_steps_pp_beautify
   apply (simp add: gcd_diff1_nat)
  apply (metis gcd.commute gcd_diff1_nat not_le)
  done  
    
section \<open>Arrays\<close>
  
subsection \<open>Array Max program: one-variable loop\<close>

lemma max_program_correct:
  assumes "r \<bowtie> i" 
  assumes "vwb_lens i" "vwb_lens r" 
  shows  
"\<lbrace>uop length \<guillemotleft>a\<guillemotright> \<ge>\<^sub>u1 \<and> &i =\<^sub>u 1 \<and> &r =\<^sub>u bop nth \<guillemotleft>a:: int list\<guillemotright> 0\<rbrace> 
   INVAR  0 <\<^sub>u &i \<and> &i \<le>\<^sub>u uop length \<guillemotleft>a\<guillemotright> \<and> &r =\<^sub>u uop Max ran\<^sub>u(bop take (&i) \<guillemotleft>a\<guillemotright>) 
   VRT  \<guillemotleft>measure (Rep_uexpr (uop length \<guillemotleft>a\<guillemotright> - (&i)))\<guillemotright>  
   WHILE \<not>(&i =\<^sub>u uop length \<guillemotleft>a\<guillemotright>) 
   DO 
      IF &r <\<^sub>u  bop nth \<guillemotleft>a\<guillemotright> (&i) 
      THEN r :== bop nth \<guillemotleft>a\<guillemotright> (&i)
      ELSE SKIP
      FI;
      i :== (&i + 1)
   OD   
 \<lbrace>&r =\<^sub>uuop Max ran\<^sub>u(\<guillemotleft>a\<guillemotright>)\<rbrace>\<^sub>P"  
  apply (insert assms)
  apply vcg_hoare_sp_steps_pp_beautify    
  subgoal for A 
    by (cases a; auto)
  subgoal for A i                  
    apply (clarsimp simp: take_Suc_conv_app_nth)
    apply (subst Max_insert) by auto
  subgoal for A i 
    apply (clarsimp simp: take_Suc_conv_app_nth)  
    apply (subst Max_insert) by auto
  done  
    
find_theorems name: "rep_eq" "(Rep_uexpr ?e = ?t)" (*This what pred_simp uses...*)
 
(*
TODO List for next iteration:

*)    
  
 
lemma demo_VAR_BIND:
  assumes "lens_indep_all [r, x]"
  assumes "vwb_lens r" "vwb_lens x" 
  assumes VAR_BIND: "(get\<^bsub>r\<^esub> )  = r\<^sub>0 \<and> (get\<^bsub>x\<^esub> )  = x\<^sub>0"  
  shows  
"\<lbrace>&r =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> \<guillemotleft>b\<guillemotright>>\<^sub>u 0 \<and> \<guillemotleft>a\<guillemotright>>\<^sub>u 0\<rbrace> 
   INVAR &r >\<^sub>u0 \<and> &x >\<^sub>u 0 \<and> bop gcd (&r) (&x) =\<^sub>u  bop gcd \<guillemotleft>a\<guillemotright> \<guillemotleft>b\<guillemotright>
   VRT \<guillemotleft>measure (Rep_uexpr (bop max (&r) (&x)))\<guillemotright>
   WHILE \<not>(&r =\<^sub>u &x)
   DO
    IF &r >\<^sub>u &x
    THEN r :== (&r - &x)
    ELSE x :== (&x - &r)
    FI
   OD
 \<lbrace>&r =\<^sub>u &x \<and> &r =\<^sub>u bop gcd \<guillemotleft>a\<guillemotright> \<guillemotleft>b\<guillemotright>\<rbrace>\<^sub>P"
  apply (insert assms(1) assms(2))  
  apply(hoare_sp_vcg_steps_pp; (vcg_elim_determ beautify_thms)?)
    apply (auto simp only: VAR_BIND)
   apply (simp add: gcd_diff1_nat)
  apply (metis gcd.commute gcd_diff1_nat not_le)
  done
    
    
end

