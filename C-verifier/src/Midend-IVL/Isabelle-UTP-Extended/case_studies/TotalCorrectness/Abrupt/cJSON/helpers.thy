section \<open>Helper constants and such\<close>

theory helpers
imports
  "../../../../utils/utp_extensions"
  "../../../../../../Backend/VCG/VCG_total_Floyd"
begin

text \<open>Somehow the rel while loop syntax was being reincluded, causing ambiguous parse warnings;
this requires recalling syntax again.\<close>
recall_syntax

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

text \<open>String upper/lower borrowed from the Isabelle Meta Model in the AFP.\<close>
definition \<open>lowercase =
  map (\<lambda>c. let n = nat_of_char c in if n < 97 then char_of_nat (n + 32 ) else c)\<close>
abbreviation \<open>lowercase\<^sub>u \<equiv> uop lowercase\<close>

definition \<open>uppercase =
  map (\<lambda>c. let n = nat_of_char c in if n < 97 then c else char_of_nat (n - 32))\<close>
abbreviation \<open>uppercase\<^sub>u \<equiv> uop uppercase\<close>

definition int_of_char :: \<open>char \<Rightarrow> int\<close> where
  \<open>int_of_char = int_of_integer \<circ> integer_of_char\<close>
abbreviation \<open>int_of_char\<^sub>u \<equiv> uop int_of_char\<close>
abbreviation \<open>nat_of_char\<^sub>u \<equiv> uop nat_of_char\<close>

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

fun shows_aux :: \<open>string \<Rightarrow> nat \<Rightarrow> string\<close> where
  \<open>shows_aux p n =
  (if n < 10 then string_of_digit n
  else shows_aux p (n div 10) @ string_of_digit (n mod 10))\<close>
abbreviation \<open>shows n \<equiv> shows_aux '''' n\<close>

syntax
  "_ushows" :: \<open>(nat, '\<alpha>) uexpr \<Rightarrow> (string, '\<alpha>) uexpr\<close> ("shows\<^sub>u'(_')")
translations
  "shows\<^sub>u(n)" == "CONST uop CONST shows n"

end
