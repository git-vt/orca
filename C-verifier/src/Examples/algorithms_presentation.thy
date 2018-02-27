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

theory algorithms_presentation

  imports "../Front-End/Syntax_Interface"
begin

sledgehammer_params [stop_on_first, parallel_subgoals, join_subgoals]
  
section \<open>Simple algorithms\<close>

subsection \<open>Increment method\<close>
  
program_spec increment_method_sp_H1_H3:
  assumes "vwb_lens x"
  assumes_utp "\<guillemotleft>a\<guillemotright> >\<^sub>u 0"
  prog_utp    "x :== 0 ; 
               INVAR \<guillemotleft>a\<guillemotright> >\<^sub>u 0 \<and> \<guillemotleft>a\<guillemotright> \<ge>\<^sub>u &x 
               VRT \<guillemotleft>(measure o Rep_uexpr) (\<guillemotleft>a\<guillemotright> - &x)\<guillemotright> 
               WHILE &x <\<^sub>u \<guillemotleft>a\<guillemotright> DO x:== (&x + 1) OD"
  ensures_utp "\<guillemotleft>a\<guillemotright> =\<^sub>u &x"
  vcg_sp
  done

program_spec increment_method_wp_H1_H3:
  assumes "vwb_lens x"
  assumes_utp "\<guillemotleft>a\<guillemotright> >\<^sub>u 0"
  prog_utp    "x :== 0 ; 
               INVAR \<guillemotleft>a\<guillemotright> >\<^sub>u 0 \<and> \<guillemotleft>a\<guillemotright> \<ge>\<^sub>u &x 
               VRT \<guillemotleft>(measure o Rep_uexpr) (\<guillemotleft>a\<guillemotright> - &x)\<guillemotright> 
               WHILE &x <\<^sub>u \<guillemotleft>a\<guillemotright> DO x:== (&x + 1) OD"
  ensures_utp "\<guillemotleft>a\<guillemotright> =\<^sub>u &x"
  vcg_wp
  done
    
subsection \<open>even count program\<close> 

program_spec even_count_gen_sp_H1_H3:
  assumes "lens_indep_all [i,j]"
  assumes "vwb_lens i" "vwb_lens j"  
  assumes_utp "\<guillemotleft>a\<guillemotright> >\<^sub>u 0"
  prog_utp    "i :== \<guillemotleft>0::int\<guillemotright>;
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
               OD" 
  ensures_utp "&j =\<^sub>u (\<guillemotleft>a\<guillemotright> + 1)div \<guillemotleft>2\<guillemotright>"
  vcg_sp
   apply presburger+
  done   

program_spec even_count_gen'_sp_H1_H3:
  assumes "lens_indep_all [i,j]"
  assumes  "vwb_lens i" "vwb_lens j"  
  assumes_utp "\<guillemotleft>a\<guillemotright> >\<^sub>u 0"
  prog_utp    "i :== \<guillemotleft>0::int\<guillemotright>;
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
               OD" 
  ensures_utp "&j =\<^sub>u (\<guillemotleft>a\<guillemotright> + 1)div 2"
  vcg_sp
   apply simp
  by presburger

program_spec even_count_gen'_wp_H1_H3:
  assumes "lens_indep_all [i,j]"
  assumes  "vwb_lens i" "vwb_lens j"  
  assumes_utp "\<guillemotleft>a\<guillemotright> >\<^sub>u 0"
  prog_utp    "i :== \<guillemotleft>0::int\<guillemotright>;
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
               OD" 
  ensures_utp "&j =\<^sub>u (\<guillemotleft>a\<guillemotright> + 1)div 2"
  vcg_wp
    apply simp_all
  using dvd_imp_mod_0 odd_succ_div_two
  apply blast
  done

end