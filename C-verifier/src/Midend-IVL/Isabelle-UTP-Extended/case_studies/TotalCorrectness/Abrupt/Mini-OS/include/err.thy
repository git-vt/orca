subsection \<open>Errors\<close>

theory err
imports
  "../helpers"
begin

text \<open>The header file may be hard to convert in full as it involves pointer-to-integer and
integer-to-pointer conversions, which is hard to do if verification pointers aren't implemented as
numeric values.\<close>

abbreviation "IS_ERR_VALUE x \<equiv> x >\<^sub>u -\<^bsub>u/SIZEOF_LONG\<^esub> 1000"

end
