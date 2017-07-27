subsection \<open>Helper constants and such\<close>

theory helpers
imports
  "../../../../../../Backend/VCG/VCG_total_ML"
begin

text \<open>sizeof(int); 32 bits on the vast majority of modern non-embedded architectures.\<close>
abbreviation "SIZEOF_INT \<equiv> \<guillemotleft>32::nat\<guillemotright>"

text \<open>sizeof(unsigned long); assuming non-Windows 64-bit architecture.\<close>
abbreviation "SIZEOF_ULONG \<equiv> \<guillemotleft>64::nat\<guillemotright>"

end
