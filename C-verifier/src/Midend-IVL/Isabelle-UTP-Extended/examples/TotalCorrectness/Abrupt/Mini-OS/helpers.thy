subsection \<open>Helper constants and such\<close>

theory helpers
imports
  "../../../../../../Backend/VCG/VCG_total_ML"
begin

text \<open>sizeof([unsigned] int); 32 bits on the vast majority of modern non-embedded architectures.\<close>
abbreviation "SIZEOF_INT \<equiv> \<guillemotleft>32::nat\<guillemotright>"

text \<open>sizeof([unsigned] long); non-Windows-style 64-bit architecture.\<close>
abbreviation "SIZEOF_LONG \<equiv> \<guillemotleft>64::nat\<guillemotright>"

text \<open>Implementation-dependent in the Mini-OS source files (arch\_limits files); assuming 64-bit for
now. ARM vs.\ x86, etc.\ doesn't seem to be that important for this bit, though.\<close>

abbreviation "PAGE_SHIFT \<equiv> \<guillemotleft>12::nat\<guillemotright>"
abbreviation "PAGE_SIZE \<equiv> 1 \<lless>\<^bsub>u/SIZEOF_INT\<^esub> PAGE_SHIFT"
abbreviation "PAGE_MASK \<equiv> \<not>\<^bsub>u/SIZEOF_INT\<^esub> (PAGE_SIZE - 1)"

end
