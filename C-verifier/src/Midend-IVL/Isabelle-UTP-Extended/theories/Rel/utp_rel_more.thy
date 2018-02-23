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

theory utp_rel_more
imports   "../../../Isabelle-UTP/utp/utp_rel"
begin
section \<open>More on Rel programs\<close> 
subsection \<open>skip\<close>  
  
abbreviation skip'::"'\<alpha> hrel" ("SKIP\<^sub>r")
  where "SKIP\<^sub>r \<equiv> skip_r" 
    
subsection \<open>conditional\<close>  

abbreviation rcond'::"'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow>  '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("bif (_)/ then (_) else (_) eif")
where "bif b then P else Q eif \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>< \<triangleright> Q)"  

subsection \<open>Iterations and loops \<close>
text \<open>We propose a generic scheme fro iterations inspired by eiffel~\url{https://www.ecma-international.org/publications/files/ECMA-ST/ECMA-367.pdf}.
      The same scheme was used in~url{https://arxiv.org/pdf/1211.4470.pdf}. 
      Since this iteration scheme is generic all other iterations can be derived from it.\<close>
  
definition from_until_gfp_rel :: "'\<alpha> hrel \<Rightarrow>'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("from\<^sup>\<top> _ until _ do _ od") 
  where "from\<^sup>\<top> init until exit do body od =  
         init ;; (\<nu> X \<bullet> bif \<not> exit then (body ;; X) else SKIP\<^sub>r eif)" 
  
definition from_until_lfp_rel :: "'\<alpha> hrel \<Rightarrow>'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("from\<^sub>\<bottom> _ until _ do _ od") 
  where "from\<^sub>\<bottom> init until exit do body od =  
         init ;; (\<mu> X \<bullet> bif \<not> exit then (body ;; X) else SKIP\<^sub>r eif)" 

definition while_gfp_rel :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sup>\<top> _ do _ od")
where "while\<^sup>\<top> b do body od = from\<^sup>\<top> SKIP\<^sub>r until \<not> b do body od"

definition while_lfp_rel :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sub>\<bottom> _ do _ od") 
  where "while\<^sub>\<bottom> b do body od =  from\<^sub>\<bottom> SKIP\<^sub>r until \<not> b do body od"
    
definition do_while_gfp_rel :: 
  "'\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel" ("do _ while\<^sup>\<top> _ od")
where "do body while\<^sup>\<top> b od = from\<^sup>\<top> body until \<not> b do body od"

definition do_while_lfp_rel :: 
  "'\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow>  '\<alpha> hrel" ("do _ while\<^sub>\<bottom> _ od") 
  where "do body while\<^sub>\<bottom> b od = from\<^sub>\<bottom> body until \<not> b do body od"
    
definition for_gfp_rel :: 
  "'\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("for\<^sup>\<top> '(_,_,_') do _ od")
where "for\<^sup>\<top> (init, b, incr) do body od = from\<^sup>\<top> init until \<not> b do body ;; incr od"

definition for_lfp_rel:: 
  "'\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("for\<^sub>\<bottom> '(_,_,_') do _ od")
where "for\<^sub>\<bottom> (init, b, incr) do body od = from\<^sub>\<bottom> init until \<not> b do body ;; incr od"
    
text \<open>Iterations with invariant decoration\<close>

definition from_until_lfp_invr_rel :: "'\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("from\<^sub>\<bottom> _ invr _ until _ do _ od") 
  where "from\<^sub>\<bottom> init invr invar  until exit do body od = from\<^sub>\<bottom> init until exit do body od"

definition from_until_gfp_invr_rel :: "'\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("from\<^sup>\<top> _ invr _ until _ do _ od") 
  where "from\<^sup>\<top> init invr invar until exit do body od = from\<^sup>\<top> init until exit do body od"

definition while_lfp_invr_rel :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("invr _ while\<^sub>\<bottom> _ do _ od") 
where "invr invar while\<^sub>\<bottom> b do body od = while\<^sub>\<bottom> b do body od"

definition while_gfp_invr_rel :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("invr _ while\<^sup>\<top> _ do _ od") 
where "invr invar while\<^sup>\<top> b do body od = while\<^sup>\<top> b do body od"

definition do_while_gfp_invr_rel :: 
  "'\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel" ("do _ while\<^sup>\<top> _ invr _ od")
where "do body while\<^sup>\<top> b invr invar od = from\<^sup>\<top> body until \<not> b do body od"

definition do_while_lfp_invr_rel :: 
  "'\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel" ("do _ while\<^sub>\<bottom> _ invr _ od") 
where "do body while\<^sub>\<bottom> b invr invar od = from\<^sub>\<bottom> body until \<not> b do body od"  
  
definition for_gfp_invr_rel :: 
  "'\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("for\<^sup>\<top> '(_,_,_') invr _ do _ od")
where "for\<^sup>\<top> (init, b, incr) invr invar do body od = from\<^sup>\<top> init until \<not> b do body ;; incr od"

definition for_lfp_invr_rel :: 
  "'\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow>  '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("for\<^sub>\<bottom> '(_,_,_') invr _ do _ od")
where "for\<^sub>\<bottom> (init, b, incr) invr invar do body od = from\<^sub>\<bottom> init until \<not> b do body ;; incr od"
  
text \<open>Iterations with invariant and variant decoration\<close>
  
definition from_until_lfp_invr_vrt_rel :: 
  "'\<alpha> hrel \<Rightarrow>'\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("from\<^sub>\<bottom> _ invr _ vrt _ until _ do _ od") 
  where "from\<^sub>\<bottom> init invr invar vrt vari until exit do body od =  from\<^sub>\<bottom> init until exit do body od"

definition from_until_gfp_invr_vrt_rel :: 
  "'\<alpha> hrel \<Rightarrow>'\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("from\<^sup>\<top> _ invr _ vrt _ until _ do _ od") 
  where "from\<^sup>\<top> init invr invar vrt vari until exit do body od =  from\<^sup>\<top> init until exit do body od"
    
definition while_lfp_invr_vrt_rel :: 
  "'\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow>  '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("invr _ vrt _ while\<^sub>\<bottom> _ do _ od") 
where "invr invar vrt vari while\<^sub>\<bottom> b do body od = while\<^sub>\<bottom> b do body od"

definition while_gfp_invr_vrt_rel :: 
  "'\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow>  '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("invr _ vrt _ while\<^sup>\<top> _ do _ od") 
where "invr invar vrt vari while\<^sup>\<top> b do body od = while\<^sup>\<top> b do body od"

definition do_while_gfp_invr_vrt_rel :: 
   "'\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel" ("do _ while\<^sup>\<top> _ invr _ vrt _ od")
where "do body while\<^sup>\<top> b invr invar vrt vari od = from\<^sup>\<top> body until \<not> b do body od"

definition do_while_lfp_invr_vrt_rel :: 
   "'\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel" ("do _ while\<^sub>\<bottom> _ invr _ vrt _ od") 
   where "do body while\<^sub>\<bottom> b invr invar vrt vari od = from\<^sub>\<bottom> body until \<not> b do body od"
     
definition for_gfp_invr_vrt_rel :: 
  "'\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("for\<^sup>\<top> '(_,_,_') invr _ vrt_ do _ od")
where "for\<^sup>\<top> (init, b, incr) invr invar vrt vari do body od = from\<^sup>\<top> init until \<not> b do body ;; incr od"

definition for_lfp_invr_vrt_rel :: 
  "'\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> cond \<Rightarrow> ('t,'\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("for\<^sub>\<bottom> '(_,_,_') invr _ vrt _ do _ od")
where "for\<^sub>\<bottom> (init, b, incr) invr invar vrt vari do body od = from\<^sub>\<bottom> init until \<not> b do body ;; incr od"
 

end

