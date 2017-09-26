section \<open>Binary Operations\<close>

theory BitOps
imports
  Main
  "~~/src/HOL/Word/Bits_Bit" (* Maybe Word.thy instead *)
begin

text \<open>Bits of BitOperations.thy and MoreWord.thy from the VAMP machine model theories,
Copyright 2003-2009 Kara Abdul-Qadar, Matthias Daum, Mark Hillebrand, Dirk Leinenbach,
Elena Petrova, Mareike Schmidt, Alexandra Tsyban, and Martin Wildmoser
and licensed under the German-Jurisdiction Creative Commons Attribution Non-commercial Share Alike
2.0 License (https://creativecommons.org/licenses/by-nc/2.0/de/legalcode), simplified English
version at https://creativecommons.org/licenses/by-nc/2.0/de/deed.en.

The only changes made (by Joshua A. Bockenek in 2017) were spacing adjustments and usage of
pretty-printing characters (like @{text \<Rightarrow>} instead of @{text \<open>=>\<close>}, cartouches, etc.), plus some
minor syntactic tweaks that do not affect the semantics. For now the associated lemmas have been
left out, but those may be necessary for any proofs involving bit operations.
This may eventually be replaced given the reliance on a non-commercial-use license.\<close>

subsection \<open>Building blocks\<close>

definition bv_msb :: \<open>bit list \<Rightarrow> bit\<close> where
  \<open>bv_msb w = (if w = [] then 0 else hd w)\<close>

definition bv_extend :: \<open>[nat, bit, bit list] \<Rightarrow> bit list\<close> where
  \<open>bv_extend i b w = (replicate (i - length w) b) @ w\<close>

fun rem_initial :: \<open>bit \<Rightarrow> bit list \<Rightarrow> bit list\<close> where
  \<open>rem_initial b [] = []\<close>
| \<open>rem_initial b (x # xs) = (if b = x then rem_initial b xs else x # xs)\<close>

abbreviation \<open>norm_unsigned \<equiv> rem_initial 0\<close>

primrec norm_signed :: \<open>bit list \<Rightarrow> bit list\<close> where
  norm_signed_Nil:  \<open>norm_signed [] = []\<close>
| norm_signed_Cons: \<open>norm_signed (b # bs) =
    (case b of 1 \<Rightarrow> b # rem_initial b bs  
             | 0 \<Rightarrow> if norm_unsigned bs = [] then [] else b # norm_unsigned bs)\<close>  

fun nat_to_bv_helper :: \<open>nat \<Rightarrow> bit list \<Rightarrow> bit list\<close> where
  Zeroo: \<open>nat_to_bv_helper 0 bs = bs\<close>
| Succ:  \<open>nat_to_bv_helper (Suc n) bs = 
         (nat_to_bv_helper (Suc n div 2) ((if Suc n mod 2 = 0
                                           then (0::bit) 
                                           else (1::bit)) # bs))\<close>

definition nat_to_bv :: \<open>nat \<Rightarrow> bit list\<close> where
  \<open>nat_to_bv n = nat_to_bv_helper n []\<close>

abbreviation \<open>bv_not \<equiv> map (\<lambda>x::bit. NOT x)\<close>

definition int_to_bv :: \<open>int \<Rightarrow> bit list\<close> where
  \<open>int_to_bv n = (if 0 \<le> n
                 then norm_signed (0 # nat_to_bv (nat n))
                 else norm_signed (bv_not (0 # nat_to_bv (nat (-n - 1)))))\<close>

primrec bitval :: \<open>bit \<Rightarrow> nat\<close> where
  \<open>bitval 0 = 0\<close>
| \<open>bitval 1 = 1\<close>

definition bv_to_nat :: \<open>bit list \<Rightarrow> nat\<close> where
  \<open>bv_to_nat = foldl (%bn b. 2 * bn + bitval b) 0\<close>

definition bv_to_int :: \<open>bit list \<Rightarrow> int\<close> where
  \<open>bv_to_int w =
    (case bv_msb w of 0 \<Rightarrow> int (bv_to_nat w)
                    | 1 \<Rightarrow> - int (bv_to_nat (bv_not w) + 1))\<close>

\<comment> \<open>convert int to bv of a desired length\<close>
definition int2bvn :: \<open>nat \<Rightarrow> int \<Rightarrow> bit list\<close> where
  \<open>int2bvn n a = (let v = int_to_bv a in drop (length v - n) (bv_extend n (bv_msb v) v))\<close>

\<comment> \<open>convert nat to bv of a desired length\<close>
definition nat2bvn :: \<open>nat \<Rightarrow> nat \<Rightarrow> bit list\<close> where
  \<open>nat2bvn n a = (let v = nat_to_bv a in drop (length v - n) (bv_extend n (0::bit) v))\<close>

subsection \<open>Base definitions for AND/OR/XOR\<close>

definition s_bitop :: \<open>(bit \<Rightarrow> bit \<Rightarrow> bit) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int\<close> where
  \<open>s_bitop f x y \<equiv> let v = int_to_bv x; w = int_to_bv y in
     bv_to_int (map (\<lambda> (a, b). f a b)
                    (zip (bv_extend (length w) (bv_msb v) v)
                         (bv_extend (length v) (bv_msb w) w)))\<close>

definition u_bitop :: \<open>(bit \<Rightarrow> bit \<Rightarrow> bit) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>u_bitop f x y \<equiv> let v = nat_to_bv x; w = nat_to_bv y in
     bv_to_nat (map (\<lambda> (a, b). f a b)
                    (zip (bv_extend (length w) (0::bit) v)
                         (bv_extend (length v) (0::bit) w)))\<close>

subsection \<open>Bit shifting\<close>

definition \<open>s_lsh x w a \<equiv> bv_to_int ((drop a (int2bvn w x)) @ replicate a 0)\<close>
definition \<open>u_lsh x w a \<equiv> bv_to_nat ((drop a (nat2bvn w x)) @ replicate a 0)\<close>
definition \<open>s_rsh x w a \<equiv> if a > 0
                           then int (bv_to_nat (take (w - a) (int2bvn w x)))
                           else x\<close>
definition \<open>u_rsh x w a \<equiv> bv_to_nat (take (length (nat_to_bv x) - a) (nat_to_bv x))\<close>

subsection \<open>Negation\<close>
text \<open>This subsection covers both plain bitwise NOT and two's-complement negation (only needed for
unsigned/nat values?)\<close>

definition \<open>s_not w x \<equiv> bv_to_int (bv_not (int2bvn w x))\<close>
definition \<open>u_not w x \<equiv> bv_to_nat (bv_not (nat2bvn w x))\<close>
definition \<open>u_neg w x \<equiv> 1 + u_not w x\<close>

end
