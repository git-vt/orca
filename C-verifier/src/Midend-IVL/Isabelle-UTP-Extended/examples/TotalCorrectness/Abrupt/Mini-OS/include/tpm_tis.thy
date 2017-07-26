subsection \<open>Derivations from Linux's \texttt{drivers/char/tpm.c}\<close>

theory tpm_tis
imports
  "../../../../../hoare/AlgebraicLaws/Abrupt/algebraic_laws_abrupt" (* Might not need proofs *)
begin

text \<open>Bare numeric literals are (possibly signed) integers in C, and usually compilers try to fit
the value in a larger type if regular \texttt{int} is too small.\<close>

abbreviation "TPM_TIS_EN_LOCL0 \<equiv> \<guillemotleft>1::nat\<guillemotright>" -- \<open>0b1\<close>
abbreviation "TPM_TIS_EN_LOCL1 \<equiv> \<guillemotleft>2::nat\<guillemotright>" -- \<open>1 << 1, 0b10\<close>
abbreviation "TPM_TIS_EN_LOCL2 \<equiv> \<guillemotleft>4::nat\<guillemotright>" -- \<open>1 << 2, 0b100\<close>
abbreviation "TPM_TIS_EN_LOCL3 \<equiv> \<guillemotleft>8::nat\<guillemotright>" -- \<open>1 << 3, 0b1000\<close>
abbreviation "TPM_TIS_EN_LOCL4 \<equiv> \<guillemotleft>16::nat\<guillemotright>" -- \<open>1 << 4, 0b10000\<close>
abbreviation "TPM_TIS_EN_LOCLALL \<equiv>
  TPM_TIS_EN_LOCL0 \<or>\<^sub>b\<^sub>u
  TPM_TIS_EN_LOCL1 \<or>\<^sub>b\<^sub>u
  TPM_TIS_EN_LOCL2 \<or>\<^sub>b\<^sub>u
  TPM_TIS_EN_LOCL3 \<or>\<^sub>b\<^sub>u
  TPM_TIS_EN_LOCL4"
abbreviation "TPM_BASEADDR \<equiv> \<guillemotleft>4275306496::nat\<guillemotright>" -- \<open>0xFED40000\<close>
abbreviation "TPM_PROBE_IRQ \<equiv> \<guillemotleft>65535::nat\<guillemotright>" -- \<open>0xFFFF\<close>
abbreviation "TPM_TIS_LOCL_INT_TO_FLAG x \<equiv> 1 \<lless>\<^bsub>u/\<guillemotleft>32::nat\<guillemotright>\<^esub> x"

end
