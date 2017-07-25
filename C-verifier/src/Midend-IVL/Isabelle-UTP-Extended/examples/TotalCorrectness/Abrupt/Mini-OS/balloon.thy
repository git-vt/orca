subsection \<open>Ballooning for Emergency Pages\<close>

theory balloon
imports
  "../../../../../../Backend/VCG/VCG_total_ML"
begin

text \<open>Size of \texttt{balloon\_frames}\<close>
abbreviation "N_BALLOON_FRAMES \<equiv> \<guillemotleft>64::nat\<guillemotright>"

(* get_max_pages needs struct? *)
(* mm_alloc_bitmap_remap needs function calls *)
(* balloon_up needs structs, pointers, function calls *)
(* chk_free_pages needs function calls *)

end
