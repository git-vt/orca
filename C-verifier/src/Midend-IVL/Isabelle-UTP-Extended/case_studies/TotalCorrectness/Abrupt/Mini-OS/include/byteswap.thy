subsection \<open>Byte swapping\<close>

theory byteswap
imports
  "../../../../../../../Backend/VCG/VCG_total_ML" (* Might do some proofs here *)
begin

text \<open>These may be unnecessary, but could be useful for conversions\<close>
abbreviation "to_uint8 x \<equiv> x \<and>\<^sub>b\<^sub>u 0xff"
abbreviation "to_uint16 x \<equiv> x \<and>\<^sub>b\<^sub>u 0xffff"
abbreviation "to_uint32 x \<equiv> x \<and>\<^sub>b\<^sub>u 0xffffffff"
abbreviation "to_uint64 x \<equiv> x \<and>\<^sub>b\<^sub>u 0xffffffffffffffff"

(* The ::nats are required as, for whatever reason, the type nat couldn't be implicitly determined
like with some of the other literals. *)
abbreviation "bswap_16 x \<equiv>
  (x \<and>\<^sub>b\<^sub>u 0x00ff) \<lless>\<^bsub>u/\<guillemotleft>16::nat\<guillemotright>\<^esub> 8 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 0xff00) \<ggreater>\<^bsub>u/\<guillemotleft>16::nat\<guillemotright>\<^esub> 8"

text \<open>GCC since version 4.3 has had optimized builtins for the following, but we check the
correctness of the non-optimized versions just in case.\<close>

abbreviation "bswap_32 x \<equiv>
  (x \<and>\<^sub>b\<^sub>u 0x000000ff) \<lless>\<^bsub>u/\<guillemotleft>32::nat\<guillemotright>\<^esub> 24 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 0x0000ff00) \<lless>\<^bsub>u/\<guillemotleft>32::nat\<guillemotright>\<^esub> 8 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 0x00ff0000) \<ggreater>\<^bsub>u/\<guillemotleft>32::nat\<guillemotright>\<^esub> 8 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 0xff000000) \<ggreater>\<^bsub>u/\<guillemotleft>32::nat\<guillemotright>\<^esub> 24"

abbreviation "bswap_64 x \<equiv>
  (x \<and>\<^sub>b\<^sub>u 0x00000000000000ff) \<lless>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 56 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 0x000000000000ff00) \<lless>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 40 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 0x0000000000ff0000) \<lless>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 24 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 0x00000000ff000000) \<lless>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 8 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 0x000000ff00000000) \<ggreater>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 8 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 0x0000ff0000000000) \<ggreater>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 24 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 0x00ff000000000000) \<ggreater>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 40 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 0xff00000000000000) \<ggreater>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 56"

end
