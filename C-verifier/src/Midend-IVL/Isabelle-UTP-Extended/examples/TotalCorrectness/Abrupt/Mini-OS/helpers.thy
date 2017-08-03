subsection \<open>Helper constants and such\<close>

theory helpers
imports
  "../../../../../../Backend/VCG/VCG_total_ML"
begin

text \<open>\texttt{sizeof([unsigned] int)}; 32 bits on the vast majority of modern non-embedded
architectures.\<close>
abbreviation "SIZEOF_INT \<equiv> \<guillemotleft>32::nat\<guillemotright>"

text \<open>\texttt{sizeof([unsigned] long)}; non-Windows-style 64-bit architecture.\<close>
abbreviation "SIZEOF_LONG \<equiv> \<guillemotleft>64::nat\<guillemotright>"

paragraph \<open>For time.h\<close>
text \<open>\texttt{sizeof}s for \texttt{s\_time\_t} (nanoseconds elapsed since boot time),
\texttt{time\_t} (wall clock time), \texttt{suseconds\_t} (also wall clock).\<close>
abbreviation "SIZEOF_S_TIME_T \<equiv> \<guillemotleft>64::nat\<guillemotright>" -- \<open>\texttt{int64\_t}\<close>
abbreviation "SIZEOF_TIME_T \<equiv> \<guillemotleft>64::nat\<guillemotright>" -- \<open>\texttt{long}\<close>
abbreviation "SIZEOF_SUSECONDS_T \<equiv> \<guillemotleft>64::nat\<guillemotright>" -- \<open>\texttt{long}\<close>

text \<open>Implementation-dependent in the Mini-OS source files (arch\_limits files); assuming 64-bit for
now. ARM vs.\ x86, etc.\ doesn't seem to be that important for this bit, though.\<close>

abbreviation "PAGE_SHIFT \<equiv> \<guillemotleft>12::nat\<guillemotright>"
abbreviation "PAGE_SIZE \<equiv> 1 \<lless>\<^bsub>u/SIZEOF_INT\<^esub> PAGE_SHIFT"
abbreviation "PAGE_MASK \<equiv> \<not>\<^bsub>u/SIZEOF_INT\<^esub> (PAGE_SIZE - 1)"

end
