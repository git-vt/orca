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
pretty-printing characters (like @{text \<Rightarrow>} instead of @{text \<open>=>\<close>}, etc.), plus some minor
syntactic tweaks that do not affect the semantics. For now the associated lemmas have been left out,
but those may be necessary for any proofs involving bit operations.
This may eventually be replaced given the reliance on a non-commercial-use license.\<close>

subsection \<open>Building blocks\<close>

definition bv_msb :: "bit list \<Rightarrow> bit" where
  "bv_msb w = (if w = [] then 0 else hd w)"

definition bv_extend :: "[nat, bit, bit list] \<Rightarrow> bit list" where
  "bv_extend i b w = (replicate (i - length w) b) @ w"

fun rem_initial :: "bit \<Rightarrow> bit list \<Rightarrow> bit list" where
  "rem_initial b [] = []"
| "rem_initial b (x # xs) = (if b = x then rem_initial b xs else x # xs)"

abbreviation "norm_unsigned \<equiv> rem_initial 0"

primrec norm_signed :: "bit list \<Rightarrow> bit list" where
  norm_signed_Nil:  "norm_signed [] = []"
| norm_signed_Cons: "norm_signed (b # bs) =
    (case b of 1 \<Rightarrow> b # rem_initial b bs  
             | 0 \<Rightarrow> if norm_unsigned bs = [] then [] else b # norm_unsigned bs)"  

fun nat_to_bv_helper :: "nat \<Rightarrow> bit list \<Rightarrow> bit list" where
  Zeroo: "nat_to_bv_helper 0 bs = bs"
| Succ:  "nat_to_bv_helper (Suc n) bs = 
         (nat_to_bv_helper (Suc n div 2) ((if Suc n mod 2 = 0
                                           then (0::bit) 
                                           else (1::bit)) # bs))"

definition nat_to_bv :: "nat \<Rightarrow> bit list" where
  "nat_to_bv n = nat_to_bv_helper n []"

abbreviation "bv_not \<equiv> map (\<lambda> x::bit. NOT x)"

definition int_to_bv :: "int \<Rightarrow> bit list" where
  "int_to_bv n = (if 0 \<le> n
                 then norm_signed (0 # nat_to_bv (nat n))
                 else norm_signed (bv_not (0 # nat_to_bv (nat (-n - 1)))))"

primrec bitval :: "bit \<Rightarrow> nat" where
  "bitval 0 = 0"
| "bitval 1 = 1"

definition bv_to_nat :: "bit list \<Rightarrow> nat" where
  "bv_to_nat = foldl (%bn b. 2 * bn + bitval b) 0"

definition bv_to_int :: "bit list \<Rightarrow> int" where
  "bv_to_int w =
    (case bv_msb w of 0 \<Rightarrow> int (bv_to_nat w)
                    | 1 \<Rightarrow> - int (bv_to_nat (bv_not w) + 1))"

-- \<open>convert int to bv of a desired length\<close>
definition int2bvn :: "nat \<Rightarrow> int \<Rightarrow> bit list" where
  "int2bvn n a = (let v = int_to_bv a in drop (length v - n) (bv_extend n (bv_msb v) v))"

-- \<open>convert nat to bv of a desired length\<close>
definition nat2bvn :: "nat \<Rightarrow> nat \<Rightarrow> bit list" where
  "nat2bvn n a = (let v = nat_to_bv a in drop (length v - n) (bv_extend n (0::bit) v))"

subsection \<open>Base definitions for AND/OR/XOR\<close>

definition s_bitop :: "(bit \<Rightarrow> bit \<Rightarrow> bit) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "s_bitop f x y \<equiv> let v = int_to_bv x; w = int_to_bv y in
     bv_to_int (map (\<lambda> (a, b). f a b)
                    (zip (bv_extend (length w) (bv_msb v) v)
                         (bv_extend (length v) (bv_msb w) w)))"

definition u_bitop :: "(bit \<Rightarrow> bit \<Rightarrow> bit) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "u_bitop f x y \<equiv> let v = nat_to_bv x; w = nat_to_bv y in
     bv_to_nat (map (\<lambda> (a, b). f a b)
                    (zip (bv_extend (length w) (0::bit) v)
                         (bv_extend (length v) (0::bit) w)))"

subsection \<open>Bit shifting\<close>

definition "s_lsh x w a \<equiv> bv_to_int ((drop a (int2bvn w x)) @ replicate a 0)"
definition "u_lsh x w a \<equiv> bv_to_nat ((drop a (nat2bvn w x)) @ replicate a 0)"
definition "s_rsh x w a \<equiv> if a > 0
                           then int (bv_to_nat (take (w - a) (int2bvn w x)))
                           else x"
definition "u_rsh x w a \<equiv> bv_to_nat (take (length (nat_to_bv x) - a) (nat_to_bv x))"

end
