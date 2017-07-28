subsection \<open>Input/Output Control\<close>

theory ioctl
imports
(*   "../../../../../../../hoare/AlgebraicLaws/Abrupt/algebraic_laws_abrupt" *)
  "../../../helpers"
begin

text \<open>Just constants here, plus a helper define\<close>

abbreviation "IOC_NONE' \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "IOC_WRITE' \<equiv> \<guillemotleft>1::nat\<guillemotright>"
abbreviation "IOC_READ' \<equiv> \<guillemotleft>2::nat\<guillemotright>"

text \<open>Assuming unsigned int/uint32\<close>
abbreviation "IOC' rw class n size' \<equiv>
  rw \<lless>\<^bsub>u/SIZEOF_INT\<^esub> 30 \<or>\<^sub>b\<^sub>u
  class \<lless>\<^bsub>u/SIZEOF_INT\<^esub> 22 \<or>\<^sub>b\<^sub>u
  n \<lless>\<^bsub>u/SIZEOF_INT\<^esub> 14 \<or>\<^sub>b\<^sub>u
  size' \<lless>\<^bsub>u/SIZEOF_INT\<^esub> 0" (* could just do `size'` *)

end
