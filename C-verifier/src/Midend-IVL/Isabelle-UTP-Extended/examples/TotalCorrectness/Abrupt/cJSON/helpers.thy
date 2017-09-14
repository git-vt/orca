section \<open>Helper constants and such\<close>

theory helpers
imports
  "../../../../../../Backend/VCG/VCG_total_Floyd"
begin

text \<open>For now structs are being represented as basic records (which has significant limitations);
pointers are represented as lenses, e.g. a \texttt{int*} has type @{text \<open>int \<Longrightarrow> '\<alpha>\<close>}; this means
that a variable holding that pointer has type @{text \<open>(int \<Longrightarrow> '\<alpha>) \<Longrightarrow> '\<alpha>\<close>}.
That also has limitations as we lack byte accesses and pointer arithmetic, but it works for some
parts of the code.

It may be better to represent struct fields as lenses rather than simple types such that we bypass
the immutability of records, but that then has its own problems in terms of copying (or the lack
thereof).\<close>

text \<open>\texttt{sizeof([unsigned] int)}; 32 bits on the vast majority of modern non-embedded
architectures.\<close>
abbreviation "SIZEOF_INT \<equiv> \<guillemotleft>32::nat\<guillemotright>"

text \<open>\texttt{sizeof([unsigned] long)}; non-Windows-style 64-bit architecture.\<close>
abbreviation "SIZEOF_LONG \<equiv> \<guillemotleft>64::nat\<guillemotright>"

text \<open>\texttt{sizeof(void*); assuming 64-bit systems.\<close>
abbreviation "SIZEOF_VOIDP \<equiv> \<guillemotleft>64::nat\<guillemotright>"

end
