subsection \<open>Integral limits\<close>

theory limits
imports
  "../../helpers"
begin

text \<open>Assuming 64-bit system; for our purposes, @{const SIZEOF_INT} versus @{const SIZEOF_LONG} is
not so important here.\<close>

abbreviation "STACK_SIZE_PAGE_ORDER_x86 \<equiv> \<guillemotleft>4::nat\<guillemotright>"
abbreviation "STACK_SIZE_x86 \<equiv> PAGE_SIZE * 1 \<lless>\<^bsub>u/SIZEOF_INT\<^esub> PAGE_SHIFT"

abbreviation "STACK_SIZE_PAGE_ORDER_ARM \<equiv> \<guillemotleft>2::nat\<guillemotright>"
abbreviation "STACK_SIZE_ARM \<equiv> 4 * PAGE_SIZE"

abbreviation "PATH_MAX \<equiv> PAGE_SIZE"

subsubsection \<open>Characters\<close>
text \<open>Ignoring wide character support for now. (That would be in a different header file if it
existed anyway.)\<close>

abbreviation "CHAR_BIT \<equiv> \<guillemotleft>8::nat\<guillemotright>"

abbreviation "SCHAR_MAX \<equiv> \<guillemotleft>0x7f::int\<guillemotright>"
abbreviation "SCHAR_MIN \<equiv> -SCHAR_MAX - 1"
abbreviation "UCHAR_MAX \<equiv> \<guillemotleft>0xff::nat\<guillemotright>"

text \<open>Assuming \texttt{char} is signed by default; this is true for x86, but not for ARM. Luckily,
\texttt{char} is the only type for which the default sign type is implementation-dependent.\<close>

abbreviation "CHAR_MIN \<equiv> SCHAR_MIN"
abbreviation "CHAR_MAX \<equiv> SCHAR_MAX"

subsubsection \<open>Regular integers\<close>
abbreviation "INT_MAX \<equiv> \<guillemotleft>0x7fffffff::int\<guillemotright>"
abbreviation "INT_MIN \<equiv> -INT_MAX - 1"
abbreviation "UINT_MAX \<equiv> \<guillemotleft>0xffffffff::nat\<guillemotright>"

subsubsection \<open>Short integers\<close>
abbreviation "SHRT_MAX \<equiv> \<guillemotleft>0x7fff::int\<guillemotright>"
abbreviation "SHRT_MIN \<equiv> -SHRT_MAX - 1"
abbreviation "USHRT_MAX \<equiv> \<guillemotleft>0xffff::nat\<guillemotright>"

subsubsection \<open>Long integers\<close>
text \<open>Non-Windows style.\<close>
abbreviation "LONG_MAX \<equiv> \<guillemotleft>0x7fffffffffffffff::int\<guillemotright>" -- \<open>L\<close>
abbreviation "LONG_MIN \<equiv> -LONG_MAX - 1"
abbreviation "ULONG_MAX \<equiv> \<guillemotleft>0xffffffffffffffff::nat\<guillemotright>" -- \<open>UL\<close>

subsubsection \<open>Long long integers\<close>
abbreviation "LLONG_MAX \<equiv> \<guillemotleft>0x7fffffffffffffff::int\<guillemotright>" -- \<open>LL\<close>
abbreviation "LLONG_MIN \<equiv> -LLONG_MAX - 1"
abbreviation "ULLONG_MAX \<equiv> \<guillemotleft>0xffffffffffffffff::nat\<guillemotright>" -- \<open>ULL\<close>

abbreviation "LONG_LONG_MAX \<equiv> LLONG_MAX"
abbreviation "LONG_LONG_MIN \<equiv> LLONG_MIN"
abbreviation "ULONG_LONG_MAX \<equiv> ULLONG_MAX"

end
