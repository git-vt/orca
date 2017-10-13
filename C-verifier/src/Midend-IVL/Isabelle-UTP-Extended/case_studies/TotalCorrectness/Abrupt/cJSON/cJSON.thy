section \<open>JSON parsing library for C\<close>

theory cJSON
  imports helpers
begin

subsection \<open>From header file \texttt{cJSON.h}\<close>

text \<open>Project version; used in souce code for a compile-time check that is intended to verify that
the header file and source file match up.\<close>
abbreviation \<open>CJSON_VERSION_MAJOR \<equiv> \<guillemotleft>1::nat\<guillemotright>\<close>
abbreviation \<open>CJSON_VERSION_MINOR \<equiv> \<guillemotleft>5::nat\<guillemotright>\<close>
abbreviation \<open>CJSON_VERSION_PATCH \<equiv> \<guillemotleft>8::nat\<guillemotright>\<close>

abbreviation \<open>cJSON_Invalid \<equiv> \<guillemotleft>0b00000000::nat\<guillemotright>\<close>
abbreviation \<open>cJSON_False   \<equiv> \<guillemotleft>0b00000001::nat\<guillemotright>\<close>
abbreviation \<open>cJSON_True    \<equiv> \<guillemotleft>0b00000010::nat\<guillemotright>\<close>
abbreviation \<open>cJSON_NULL    \<equiv> \<guillemotleft>0b00000100::nat\<guillemotright>\<close>
abbreviation \<open>cJSON_Number  \<equiv> \<guillemotleft>0b00001000::nat\<guillemotright>\<close>
abbreviation \<open>cJSON_String  \<equiv> \<guillemotleft>0b00010000::nat\<guillemotright>\<close>
abbreviation \<open>cJSON_Array   \<equiv> \<guillemotleft>0b00100000::nat\<guillemotright>\<close>
abbreviation \<open>cJSON_Object  \<equiv> \<guillemotleft>0b01000000::nat\<guillemotright>\<close>
abbreviation \<open>cJSON_Raw     \<equiv> \<guillemotleft>0b10000000::nat\<guillemotright>\<close>

abbreviation \<open>cJSON_IsReference \<equiv> \<guillemotleft>256::nat\<guillemotright>\<close>
abbreviation \<open>cJSON_StringIsConst \<equiv> \<guillemotleft>512::nat\<guillemotright>\<close>

text \<open>Limiting nesting prevents stack overflows.\<close>
abbreviation \<open>CJSON_NESTING_LIMIT \<equiv> \<guillemotleft>1000::nat\<guillemotright>\<close>

text \<open>Using @{typ \<open>'a option\<close>} to emulate null strings/pointers for now; this requires a UTP-level
way of accessing the contents of the option when it exists, of course.\<close>
abbreviation \<open>the\<^sub>u \<equiv> uop the\<close>

record cJSON =
  type :: int
  valuestring :: \<open>string option\<close> \<comment> \<open>if \texttt{type==cJSON\_String}\<close>
  valueint :: int \<comment> \<open>Writing directly is deprecated, should use \texttt{cJSON\_SetNumberValue}\<close>
  valuedouble :: real \<comment> \<open>if \texttt{type==cJSON\_Number}\<close>
  string :: \<open>string option\<close> \<comment> \<open>name string if this item is the child of or is in the list of
                               subitems of some parent object\<close>

text \<open>As we do not currently have a proper memory model for pointers and records cannot normally have
deferred types, we must use a separate structure for that kind of thing that holds cJSON items.\<close>
datatype cJSON_tree =
  Leaf
| Node (data: cJSON) (nextt: cJSON_tree) (prev: cJSON_tree) (child: cJSON_tree)

(* TODO: These aren't written right, returning a nat as a pointer isn't good enough *)
record '\<alpha> cJSON_Hooks =
  malloc_fn :: \<open>(size_t \<Rightarrow> nat) \<Longrightarrow> '\<alpha>\<close>
  free_fn :: \<open>(nat \<Rightarrow> unit) \<Longrightarrow> '\<alpha>\<close> \<comment> \<open>Function that doesn't return anything, not sure how to
                                      properly represent\<close>

record '\<alpha> internal_hooks =
  allocate :: \<open>(size_t \<Rightarrow> nat) \<Longrightarrow> '\<alpha>\<close>
  deallocate :: \<open>(nat \<Rightarrow> unit) \<Longrightarrow> '\<alpha>\<close>
  reallocate :: \<open>(nat \<Rightarrow> size_t \<Rightarrow> nat) \<Longrightarrow> '\<alpha>\<close>
(* TODO: static internal_hooks global_hooks = { malloc, free, realloc }; *)

(* I'd prefer to use bool but cJSON doesn't use the C99 bool type. *)
type_synonym cJSON_bool = int

type_synonym '\<alpha> str_lens = \<open>string option \<Longrightarrow> '\<alpha>\<close>
type_synonym '\<alpha> str_expr = \<open>(string option, '\<alpha>) uexpr\<close>

subsection \<open>From source file \texttt{cJSON.c}\<close>

abbreviation \<open>true' \<equiv> \<guillemotleft>1::cJSON_bool\<guillemotright>\<close>
abbreviation \<open>false' \<equiv> \<guillemotleft>0::cJSON_bool\<guillemotright>\<close>

record error =
  json :: \<open>string option\<close>
  position :: size_t \<comment> \<open>Index into JSON string\<close>
abbreviation \<open>global_error \<equiv> \<guillemotleft>\<lparr>json = None, position = 0\<rparr>\<guillemotright>\<close> (* TODO: fix up, must be a lens *)

record '\<alpha> parse_buffer =
  content :: \<open>'\<alpha> str_lens\<close>
  length :: size_t
  offset :: size_t
  depth :: size_t \<comment> \<open>How deeply nested (in arrays/objects) is the input at the current offset.\<close>
  hooks :: \<open>'\<alpha> internal_hooks\<close>

type_synonym '\<alpha> parse_buffer_lens = \<open>'\<alpha> parse_buffer option \<Longrightarrow> '\<alpha>\<close>
type_synonym '\<alpha> parse_buffer_expr = \<open>('\<alpha> parse_buffer option, '\<alpha>) uexpr\<close>

(* TODO: Need a mutable setup because we're verifying C and C expects buffer' to be a set buffer
that can be modified, not a list to be replaced with new versions. *)
record '\<alpha> printbuffer =
  buffer' :: \<open>'\<alpha> str_lens\<close>
  length' :: size_t
  offset' :: size_t
  depth' :: size_t \<comment> \<open>current nesting depth (for formatted printing)\<close>
  noalloc :: cJSON_bool
  format :: cJSON_bool \<comment> \<open>is this print a formatted print\<close>
  hooks' :: \<open>'\<alpha> internal_hooks\<close>

(* Creating a new alphabet to add global_error as a global variable would be a pain as it would
require a lot of manual copypasting, so going with good old pass-as-argument style.
TODO: use in locale? *)
definition \<open>cJSON_GetErrorPtr g = drop\<^sub>u(&g\<lparr>position\<rparr>\<^sub>r, &g\<lparr>json\<rparr>\<^sub>r)\<close>
(* TODO: Need to figure out how to use option type on the UTP level. *)

definition \<open>cJSON_Version = shows\<^sub>u(CJSON_VERSION_MAJOR) ^\<^sub>u \<guillemotleft>''.''\<guillemotright> ^\<^sub>u
                            shows\<^sub>u(CJSON_VERSION_MINOR) ^\<^sub>u \<guillemotleft>''.''\<guillemotright> ^\<^sub>u
                            shows\<^sub>u(CJSON_VERSION_PATCH)\<close>

(* TODO: global/local variable differentiation? *)
locale cJSON =
  fixes int_ret :: \<open>int \<Longrightarrow> '\<alpha>\<close>
    and nat_ret :: \<open>nat \<Longrightarrow> '\<alpha>\<close>
    and tempstr\<^sub>1 :: \<open>string \<Longrightarrow> '\<alpha>\<close> \<comment> \<open>Assuming already shown non-@{const None}\<close>
    and tempstr\<^sub>2
  assumes INDEP: \<open>vwb_lens int_ret\<close> \<open>vwb_lens nat_ret\<close>
          \<open>lens_indep_all [tempstr\<^sub>1, tempstr\<^sub>2]\<close>
          \<open>int_ret \<bowtie> tempstr\<^sub>1\<close> \<open>int_ret \<bowtie> tempstr\<^sub>2\<close>
          \<open>int_ret \<bowtie> nat_ret\<close>
          \<open>nat_ret \<bowtie> tempstr\<^sub>1\<close> \<open>nat_ret \<bowtie> tempstr\<^sub>2\<close>
begin

(* TODO: Block or frame? *)
definition case_insensitive_strcmp :: \<open>'\<alpha> str_expr \<Rightarrow> '\<alpha> str_expr \<Rightarrow> '\<alpha> hrel_cpa\<close> where
  \<open>case_insensitive_strcmp string\<^sub>1 string\<^sub>2 \<equiv>
try
  bif string\<^sub>1 =\<^sub>u \<guillemotleft>None\<guillemotright> \<or> string\<^sub>2 =\<^sub>u \<guillemotleft>None\<guillemotright> then
    int_ret \<Midarrow> 1;;
    THROW\<^sub>A\<^sub>B\<^sub>R
  else II eif;;
  bif string\<^sub>1 =\<^sub>u string\<^sub>2 then
    int_ret \<Midarrow> 0;;
    THROW\<^sub>A\<^sub>B\<^sub>R
  else II eif;;
  tempstr\<^sub>1 \<Midarrow> lowercase\<^sub>u (the\<^sub>u string\<^sub>1);;
  tempstr\<^sub>2 \<Midarrow> lowercase\<^sub>u (the\<^sub>u string\<^sub>2);;
  while head\<^sub>u(&tempstr\<^sub>1) =\<^sub>u head\<^sub>u(&tempstr\<^sub>2)
  invr #\<^sub>u(&tempstr\<^sub>1) \<le>\<^sub>u #\<^sub>u(the\<^sub>u string\<^sub>1) \<and> #\<^sub>u(&tempstr\<^sub>2) \<le>\<^sub>u #\<^sub>u(the\<^sub>u string\<^sub>2) do (* TODO: probably needs more/something else, might require extra ghost variable *)
    bif #\<^sub>u(&tempstr\<^sub>1) =\<^sub>u 0 then (* Strings here aren't null-terminated *)
      int_ret \<Midarrow> 0;;
      THROW\<^sub>A\<^sub>B\<^sub>R  
    else II eif;;
    (#\<^sub>u(&tempstr\<^sub>1) \<le>\<^sub>u #\<^sub>u(the\<^sub>u string\<^sub>2) \<and> #\<^sub>u(&tempstr\<^sub>2) \<le>\<^sub>u #\<^sub>u(the\<^sub>u string\<^sub>2))\<^sub>\<bottom>\<^sub>C;;
    tempstr\<^sub>1 \<Midarrow> tail\<^sub>u(&tempstr\<^sub>1);;
    tempstr\<^sub>2 \<Midarrow> tail\<^sub>u(&tempstr\<^sub>2)
  od;;
  int_ret \<Midarrow> (int_of_char\<^sub>u head\<^sub>u(&tempstr\<^sub>1) - int_of_char\<^sub>u head\<^sub>u(&tempstr\<^sub>2))
catch
  II
end
\<close>
(* TODO: cJSON_strdup (needs good memory model as it uses memcpy, etc.) *)
(* TODO: cJSON_New_Item *)
(* TODO: cJSON_Delete *)
(* TODO: get_decimal_point (needs locale access somehow? or just nondeterminism) *)

text \<open>Check if the given size is left to read in a given parse buffer (starting with 1)\<close>
abbreviation can_read :: \<open>'\<alpha> parse_buffer_expr \<Rightarrow> (size_t, '\<alpha>) uexpr \<Rightarrow> '\<alpha> upred\<close> where
  \<open>can_read buffer size' \<equiv> buffer \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright> \<and>
                           (the\<^sub>u buffer)\<lparr>offset\<rparr>\<^sub>r + size' \<le>\<^sub>u (the\<^sub>u buffer)\<lparr>length\<rparr>\<^sub>r\<close>
abbreviation \<open>cannot_read buffer size' \<equiv> \<not> can_read buffer size'\<close>

text \<open>Check if the buffer can be accessed at the given index (starting with 0)\<close>
abbreviation can_access_at_index :: \<open>'\<alpha> parse_buffer_expr \<Rightarrow> (size_t, '\<alpha>) uexpr \<Rightarrow> '\<alpha> upred\<close> where
  \<open>can_access_at_index buffer index \<equiv> buffer \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright> \<and>
                                      (the\<^sub>u buffer)\<lparr>offset\<rparr>\<^sub>r + index \<le>\<^sub>u (the\<^sub>u buffer)\<lparr>length\<rparr>\<^sub>r\<close>
abbreviation \<open>cannot_access_at_index buffer index \<equiv> \<not> can_access_at_index buffer index\<close>

(* TODO: figure out buffer_at_offset when using memory model; arrays are usually mutable but
Isabelle lists/etc. are not and we can't just return a reference to the remnant of the list/string.
*)
(* TODO: parse_number *)
(* TODO: ensure *)
(* TODO: update_offset; not be necessary when not working with actual pointers *)
(* TODO: print_number; has some stuff involving C-specific number handling *)

end

text \<open>Creating locale extensions for individual functions as necessary.\<close>
locale parse_hex4 = cJSON +
  constrains int_ret :: \<open>int \<Longrightarrow> '\<alpha>\<close> \<comment> \<open>@{typ '\<alpha>} not propagated from base locale.\<close>
         and tempstr\<^sub>1 :: \<open>string \<Longrightarrow> '\<alpha>\<close>
         and tempstr\<^sub>2 :: \<open>string \<Longrightarrow> '\<alpha>\<close>
  fixes h i chari and tinput :: \<open>string \<Longrightarrow> '\<alpha>\<close>
  assumes INDEP: \<open>lens_indep_all [nat_ret, h, i, chari]\<close>
          \<open>int_ret \<bowtie> h\<close> \<open>int_ret \<bowtie> i\<close>
          \<open>int_ret \<bowtie> tinput\<close>
begin

text \<open>parse 4 digit hexadecimal number\<close>
definition parse_hex4 :: \<open>'\<alpha> str_expr \<Rightarrow> '\<alpha> hrel_cpa\<close> where
  \<open>parse_hex4 input \<equiv>
h \<Midarrow> 0;;
i \<Midarrow> 0;;
tinput \<Midarrow> the\<^sub>u input;; (* Assumes not NULL/None *)
try
  while &i <\<^sub>u 4 invr true do (* TODO: invariant; assumes input has at least 4 chars *)
    chari \<Midarrow> nat_of_char\<^sub>u (&tinput(&i)\<^sub>a);;
    bif &chari \<ge>\<^sub>u \<guillemotleft>nat_of_char CHR ''0''\<guillemotright> then
      h \<Midarrow> (&h + &chari - \<guillemotleft>nat_of_char CHR ''0''\<guillemotright>)
    else
      bif &chari \<ge>\<^sub>u \<guillemotleft>nat_of_char CHR ''A''\<guillemotright> \<and> &chari \<le>\<^sub>u \<guillemotleft>nat_of_char CHR ''F''\<guillemotright> then
        h \<Midarrow> (&h + 10 + &chari - \<guillemotleft>nat_of_char CHR ''A''\<guillemotright>)
      else
        bif &chari \<ge>\<^sub>u \<guillemotleft>nat_of_char CHR ''a''\<guillemotright> \<and> &chari \<le>\<^sub>u \<guillemotleft>nat_of_char CHR ''f''\<guillemotright> then
          h \<Midarrow> (&h + 10 + &chari - \<guillemotleft>nat_of_char CHR ''a''\<guillemotright>)
        else
          nat_ret \<Midarrow> 0;;
          THROW\<^sub>A\<^sub>B\<^sub>R
        eif
      eif
    eif;; (* TODO: assertion? *)
    bif &i <\<^sub>u 3 then
      h \<Midarrow> &h \<lless>\<^bsub>u/SIZEOF_INT\<^esub> 4 (* shift left to make place for the next nibble *)
    else II eif (* TODO: assertion? *)
  od
catch
  II
end
\<close>

end

end
