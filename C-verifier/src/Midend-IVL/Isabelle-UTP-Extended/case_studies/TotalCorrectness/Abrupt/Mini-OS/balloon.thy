subsection \<open>Ballooning\<close>

theory balloon
imports
  "../../../../../../Backend/VCG/VCG_total_ML"
begin

subsubsection \<open>From header file \texttt{balloon.h}\<close>

text \<open>Keeping some pages free for allocations while ballooning/interrupts are disabled.\<close>
abbreviation "BALLOON_EMERGENCY_PAGES \<equiv> \<guillemotleft>64::nat\<guillemotright>"

(* globals: nr_max_pages, nr_mem_pages *)

definition "chk_free_pages
  (* input *) needed
  (* global variable *) nr_free_pages
  =
  (&needed \<le>\<^sub>u &nr_free_pages)
  "

subsubsection \<open>From source file \texttt{balloon.c}\<close>

text \<open>Size of \texttt{balloon\_frames}\<close>
abbreviation "N_BALLOON_FRAMES \<equiv> \<guillemotleft>64::nat\<guillemotright>"

(* get_max_pages needs struct? *)
(* mm_alloc_bitmap_remap needs function calls *)
(* balloon_up needs structs, pointers, function calls; try-catch can be used to emulate early return *)
(* chk_free_pages needs function calls *)

end
