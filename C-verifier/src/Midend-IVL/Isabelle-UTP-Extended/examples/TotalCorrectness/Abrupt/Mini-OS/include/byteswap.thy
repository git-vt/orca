subsection \<open>Byte swapping\<close>

theory byteswap
imports
  "../../../../../../../Backend/VCG/VCG_total_ML" (* Might do some proofs here *)
begin

text \<open>These may be unnecessary, but could be useful for conversions\<close>
abbreviation "to_uint8 x \<equiv> x \<and>\<^sub>b\<^sub>u 255" -- \<open>0xff\<close>
abbreviation "to_uint16 x \<equiv> x \<and>\<^sub>b\<^sub>u 65535" -- \<open>0xffff\<close>
abbreviation "to_uint32 x \<equiv> x \<and>\<^sub>b\<^sub>u 4294967295" -- \<open>0xffffffff\<close>
abbreviation "to_uint64 x \<equiv> x \<and>\<^sub>b\<^sub>u 18446744073709551615" -- \<open>0xffffffffffffffff\<close>

text \<open>0x00ff = 255, 0xff00 = 65280\<close>
(* The ::nats are required as, for whatever reason, the type nat couldn't be implicitly determined
like with some of the other literals. *)
abbreviation "bswap_16 x \<equiv>
  (x \<and>\<^sub>b\<^sub>u 255) \<lless>\<^bsub>u/\<guillemotleft>16::nat\<guillemotright>\<^esub> 8 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 65280) \<ggreater>\<^bsub>u/\<guillemotleft>16::nat\<guillemotright>\<^esub> 8"

text \<open>GCC since version 4.3 has had optimized builtins for the following, but we check the
correctness of the non-optimized versions just in case.\<close>

text \<open>0xff0000 = 16711680, 0xff000000 = 4278190080\<close>
abbreviation "bswap_32 x \<equiv>
  (x \<and>\<^sub>b\<^sub>u 255) \<lless>\<^bsub>u/\<guillemotleft>32::nat\<guillemotright>\<^esub> 24 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 65280) \<lless>\<^bsub>u/\<guillemotleft>32::nat\<guillemotright>\<^esub> 8 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 16711680) \<ggreater>\<^bsub>u/\<guillemotleft>32::nat\<guillemotright>\<^esub> 8 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 4278190080) \<ggreater>\<^bsub>u/\<guillemotleft>32::nat\<guillemotright>\<^esub> 24"

text \<open>0xff00000000 = 1095216660480,
0xff0000000000 = 280375465082880,
0xff000000000000 = 71776119061217280,
0xff00000000000000 = 18374686479671623680\<close>
abbreviation "bswap_64 x \<equiv>
  (x \<and>\<^sub>b\<^sub>u 255) \<lless>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 56 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 65280) \<lless>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 40 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 16711680) \<lless>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 24 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 4278190080) \<lless>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 8 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 1095216660480) \<ggreater>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 8 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 280375465082880) \<ggreater>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 24 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 71776119061217280) \<ggreater>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 40 \<or>\<^sub>b\<^sub>u
  (x \<and>\<^sub>b\<^sub>u 18374686479671623680) \<ggreater>\<^bsub>u/\<guillemotleft>64::nat\<guillemotright>\<^esub> 56"

end
