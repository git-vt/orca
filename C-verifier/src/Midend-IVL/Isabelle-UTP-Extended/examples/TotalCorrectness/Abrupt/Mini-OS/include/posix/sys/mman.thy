subsection \<open>Memory management\<close>

theory mman
imports
  "../../../../../../../hoare/AlgebraicLaws/Abrupt/algebraic_laws_abrupt"
begin

abbreviation "PROT_READ \<equiv> \<guillemotleft>1::nat\<guillemotright>"  -- \<open>0b001\<close>
abbreviation "PROT_WRITE \<equiv> \<guillemotleft>2::nat\<guillemotright>" -- \<open>0b010\<close>
abbreviation "PROT_EXEC \<equiv> \<guillemotleft>4::nat\<guillemotright>"  -- \<open>0b100\<close>

abbreviation "MAP_SHARED \<equiv> \<guillemotleft>1::nat\<guillemotright>" -- \<open>0x01\<close>
abbreviation "MAP_PRIVATE \<equiv> \<guillemotleft>2::nat\<guillemotright>" -- \<open>0b02\<close>
abbreviation "MAP_ANON \<equiv> \<guillemotleft>32::nat\<guillemotright>" -- \<open>0x20\<close>

text \<open>Pages are always resident, apparently\<close>
abbreviation "MAP_LOCKED \<equiv> \<guillemotleft>0::nat\<guillemotright>"

(* MAP_FAILED is void* 0, but that's just NULL so the cast seems pointless. *)

definition "mlock addr len = \<guillemotleft>0::nat\<guillemotright>" (* TODO: actually return as 0 *)
definition "munlock addr len = \<guillemotleft>0::nat\<guillemotright>" (* TODO: actually return as 0 *)

end
