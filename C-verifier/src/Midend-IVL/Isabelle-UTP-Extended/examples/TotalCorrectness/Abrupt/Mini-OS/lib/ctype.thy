subsection \<open>Properties of characters\<close>

theory ctype
imports
  "../../../../../../../Backend/VCG/VCG_total_ML" (* Needs some proofs *)
begin

text \<open>Apparently the Mini-OS \texttt{ctype} library is not conformant to the C standard in regards
to EOF handling.\<close>

(* Explicit nats not necessarily needed but useful to keep track of things. *)
abbreviation "U' \<equiv> \<guillemotleft>1::nat\<guillemotright>" -- upper
abbreviation "L' \<equiv> \<guillemotleft>2::nat\<guillemotright>" -- lower
abbreviation "D' \<equiv> \<guillemotleft>4::nat\<guillemotright>" -- digit
abbreviation "C' \<equiv> \<guillemotleft>8::nat\<guillemotright>" -- cntrl
abbreviation "P' \<equiv> \<guillemotleft>16::nat\<guillemotright>" -- punct
abbreviation "S' \<equiv> \<guillemotleft>32::nat\<guillemotright>" -- whitespace
abbreviation "X' \<equiv> \<guillemotleft>64::nat\<guillemotright>" -- \<open>hex digit\<close>
abbreviation "SP' \<equiv> \<guillemotleft>128::nat\<guillemotright>" -- \<open>hard space (0x20)\<close>

definition "ctype = \<langle>
  C', C', C', C', C', C', C', C', (* 0-7 *)
  C', C' \<or>\<^sub>b\<^sub>u S', C' \<or>\<^sub>b\<^sub>u S', C' \<or>\<^sub>b\<^sub>u S', C' \<or>\<^sub>b\<^sub>u S', C' \<or>\<^sub>b\<^sub>u S', C', C', (* 8-15 *)
  C', C', C', C', C', C', C', C', (* 16-23 *)
  C', C', C', C', C', C', C', C', (* 24-31 *)
  S' \<or>\<^sub>b\<^sub>u SP', P', P', P', P', P', P', P', (* 32-39 *)
  P', P', P', P', P', P', P', P', (* 40-47 *)
  D', D', D', D', D', D', D', D', (* 48-55 *)
  D', D', P', P', P', P', P', P', (* 56-63 *)
  P', U' \<or>\<^sub>b\<^sub>u X', U' \<or>\<^sub>b\<^sub>u X', U' \<or>\<^sub>b\<^sub>u X', U' \<or>\<^sub>b\<^sub>u X', U' \<or>\<^sub>b\<^sub>u X', U' \<or>\<^sub>b\<^sub>u X', U', (* 64-71 *)
  U', U', U', U', U', U', U', U', (* 72-79 *)
  U', U', U', U', U', U', U', U', (* 80-87 *)
  U', U', U', P', P', P', P', P', (* 88-95 *)
  P', L' \<or>\<^sub>b\<^sub>u X', L' \<or>\<^sub>b\<^sub>u X', L' \<or>\<^sub>b\<^sub>u X', L' \<or>\<^sub>b\<^sub>u X', L' \<or>\<^sub>b\<^sub>u X', L' \<or>\<^sub>b\<^sub>u X', L', (* 96-103 *)
  L', L', L', L', L', L', L', L', (* 104-111 *)
  L', L', L', L', L', L', L', L', (* 112-119 *)
  L', L', L', P', P', P', P', C', (* 120-127 *)
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (* 128-143 *)
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (* 144-159 *)
  S' \<or>\<^sub>b\<^sub>u SP', P', P', P', P', P', P', P', P', P', P', P', P', P', P', P', (* 160-175 *)
  P', P', P', P', P', P', P', P', P', P', P', P', P', P', P', P', (* 176-191 *)
  U', U', U', U', U', U', U', U', U', U', U', U', U', U', U', U', (* 192-207 *)
  U', U', U', U', U', U', U', P', U', U', U', U', U', U', U', L', (* 208-223 *)
  L', L', L', L', L', L', L', L', L', L', L', L', L', L', L', L', (* 224-239 *)
  L', L', L', L', L', L', L', P', L', L', L', L', L', L', L', L' (* 240-255 *)
\<rangle>"

text \<open>The original definition uses a cast to \texttt{unsigned char}, as that type could potentially
have a size other than eight bits, but for our purposes we'll stick with eight-bit bytes.\<close>
abbreviation "ismask' x \<equiv> ctype\<lparr>x \<and>\<^sub>b\<^sub>u 255\<rparr>\<^sub>u"

abbreviation "isalnum c \<equiv> ismask' c \<and>\<^sub>b\<^sub>u (U' \<or>\<^sub>b\<^sub>u L' \<or>\<^sub>b\<^sub>u D') \<noteq>\<^sub>u 0"
abbreviation "isalpha c \<equiv> ismask' c \<and>\<^sub>b\<^sub>u (U' \<or>\<^sub>b\<^sub>u L') \<noteq>\<^sub>u 0"
abbreviation "iscntrl c \<equiv> ismask' c \<and>\<^sub>b\<^sub>u C' \<noteq>\<^sub>u 0"
abbreviation "isdigit c \<equiv> ismask' c \<and>\<^sub>b\<^sub>u D' \<noteq>\<^sub>u 0"
abbreviation "isgraph c \<equiv> ismask' c \<and>\<^sub>b\<^sub>u (P' \<or>\<^sub>b\<^sub>u U' \<or>\<^sub>b\<^sub>u L' \<or>\<^sub>b\<^sub>u D') \<noteq>\<^sub>u 0"
abbreviation "islower c \<equiv> ismask' c \<and>\<^sub>b\<^sub>u L' \<noteq>\<^sub>u 0"
abbreviation "isprint c \<equiv> ismask' c \<and>\<^sub>b\<^sub>u (P' \<or>\<^sub>b\<^sub>u U' \<or>\<^sub>b\<^sub>u L' \<or>\<^sub>b\<^sub>u D' \<or>\<^sub>b\<^sub>u SP') \<noteq>\<^sub>u 0"
abbreviation "ispunct c \<equiv> ismask' c \<and>\<^sub>b\<^sub>u P' \<noteq>\<^sub>u 0"
abbreviation "isspace c \<equiv> ismask' c \<and>\<^sub>b\<^sub>u S' \<noteq>\<^sub>u 0"
abbreviation "isupper c \<equiv> ismask' c \<and>\<^sub>b\<^sub>u U' \<noteq>\<^sub>u 0"
abbreviation "isxdigit c \<equiv> ismask' c \<and>\<^sub>b\<^sub>u (D' \<or>\<^sub>b\<^sub>u X') \<noteq>\<^sub>u 0"

abbreviation "isascii c \<equiv> c \<le>\<^sub>u 127"
abbreviation "toascii c \<equiv> c \<and>\<^sub>b\<^sub>u 127"

text \<open>The ASCII value of `A' is 65 while the value of `a' is 97. Thus, `A - a' is -32 while `a - A'
is 32.\<close>

definition "tolower c =
  bif isupper &c then
    c \<Midarrow> &c + 32
  else
    II
  eif
  "

definition "toupper c =
  bif islower &c then
    c \<Midarrow> &c - 32
  else
    II
  eif
  "

end
