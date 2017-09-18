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

type_synonym size_t = nat

abbreviation \<open>NULL \<equiv> \<guillemotleft>0\<guillemotright>\<close>

text \<open>Borrowed from the @{typ nat} implementation of \texttt{shows} from the Real_Impl theory set
in the Archive of Formal Proofs (\url{https://www.isa-afp.org/entries/Real_Impl.html}); some slight
modifications were done for my own personal preferences.\<close>

definition string_of_digit :: \<open>nat \<Rightarrow> string\<close> where
  \<open>string_of_digit n =
    (if n = 0 then ''0''
    else if n = 1 then ''1''
    else if n = 2 then ''2''
    else if n = 3 then ''3''
    else if n = 4 then ''4''
    else if n = 5 then ''5''
    else if n = 6 then ''6''
    else if n = 7 then ''7''
    else if n = 8 then ''8''
    else ''9'')\<close>

fun shows_nat' :: \<open>string \<Rightarrow> nat \<Rightarrow> string\<close> where
  \<open>shows_nat' p n =
  (if n < 10 then string_of_digit n
  else shows_nat' p (n div 10) @ string_of_digit (n mod 10))\<close>
abbreviation \<open>shows_nat n \<equiv> shows_nat' '''' n\<close>

end
