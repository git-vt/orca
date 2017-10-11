subsection \<open>Memory management\<close>

theory mman
imports
  "../../../../../../../hoare/AlgebraicLaws/Abrupt/algebraic_laws_abrupt"
begin

abbreviation "PROT_READ \<equiv> \<guillemotleft>0b001::nat\<guillemotright>"
abbreviation "PROT_WRITE \<equiv> \<guillemotleft>0b010::nat\<guillemotright>"
abbreviation "PROT_EXEC \<equiv> \<guillemotleft>0b100::nat\<guillemotright>"

abbreviation "MAP_SHARED \<equiv> \<guillemotleft>0x01::nat\<guillemotright>"
abbreviation "MAP_PRIVATE \<equiv> \<guillemotleft>0x02::nat\<guillemotright>"
abbreviation "MAP_ANON \<equiv> \<guillemotleft>0x20::nat\<guillemotright>"

text \<open>Pages are always resident, apparently\<close>
abbreviation "MAP_LOCKED \<equiv> \<guillemotleft>0::nat\<guillemotright>"

(* MAP_FAILED is void* 0, but that's just NULL so the cast seems pointless. *)

definition "mlock addr len = \<guillemotleft>0::nat\<guillemotright>" (* TODO: actually return as 0 *)
definition "munlock addr len = \<guillemotleft>0::nat\<guillemotright>" (* TODO: actually return as 0 *)

end
