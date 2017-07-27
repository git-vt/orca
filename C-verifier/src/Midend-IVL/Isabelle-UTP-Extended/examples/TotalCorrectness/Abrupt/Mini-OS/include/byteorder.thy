subsection \<open>Byte reordering\<close>

theory byteorder
imports
  byteswap
begin

text \<open>Assuming little-endian, the most common endianness on architectures these days (both ARM and
x86 32- and 64-bit use this). Mini-OS itself has support for big-endian architectures as well as
the middle-endian format used by PDP systems (though \texttt{byteorder.h} doesn't use that).\<close>

abbreviation "be16_to_cpu v \<equiv> bswap_16 v"
abbreviation "be32_to_cpu v \<equiv> bswap_32 v"
abbreviation "be64_to_cpu v \<equiv> bswap_64 v"

abbreviation le16_to_cpu :: "(nat, 'a) uexpr \<Rightarrow> (nat, 'a) uexpr" where
  "le16_to_cpu v \<equiv> v"
abbreviation le32_to_cpu :: "(nat, 'a) uexpr \<Rightarrow> (nat, 'a) uexpr" where
  "le32_to_cpu v \<equiv> v"
abbreviation le64_to_cpu :: "(nat, 'a) uexpr \<Rightarrow> (nat, 'a) uexpr" where
  "le64_to_cpu v \<equiv> v"

abbreviation "cpu_to_be16 v \<equiv> be16_to_cpu v"
abbreviation "cpu_to_be32 v \<equiv> be32_to_cpu v"
abbreviation "cpu_to_be64 v \<equiv> be64_to_cpu v"

abbreviation "cpu_to_le16 v \<equiv> le16_to_cpu v"
abbreviation "cpu_to_le32 v \<equiv> le32_to_cpu v"
abbreviation "cpu_to_le64 v \<equiv> le64_to_cpu v"

end
