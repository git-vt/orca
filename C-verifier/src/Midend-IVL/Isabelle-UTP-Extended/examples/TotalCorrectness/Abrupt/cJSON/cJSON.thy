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

record cJSON =
  type :: int
  valuestring :: string -- \<open>if \texttt{type==cJSON\_String}; not worrying about C string handling\<close>
  valueint :: int -- \<open>Writing directly is deprecated, should use \texttt{cJSON\_SetNumberValue}\<close>
  valuedouble :: real -- \<open>if \texttt{type==cJSON\_Number}\<close>
  string :: string -- \<open>name string if this item is the child of or is in the list of subitems of
some parent object\<close>

text \<open>As we do not currently have a proper memory model for pointers and records cannot normally have
deferred types, we must use a separate structure for that kind of thing that holds cJSON items.\<close>
datatype cJSON_tree =
  Leaf
| Node (data: cJSON) (nextt: cJSON) (prev: cJSON) (child: cJSON)

(* TODO: cJSON_Hooks is a struct holding functions *)

(* I'd prefer to use bool but cJSON doesn't use the C99 bool type. *)
type_synonym cJSON_bool = int

subsection \<open>From source file \texttt{cJSON.c}\<close>

abbreviation \<open>true' \<equiv> \<guillemotleft>1::cJSON_bool\<guillemotright>\<close>
abbreviation \<open>false' \<equiv> \<guillemotleft>0::cJSON_bool\<guillemotright>\<close>

record error =
  json :: \<open>string option\<close> \<comment> \<open>Using option type to emulate null strings/pointers\<close>
  position :: size_t \<comment> \<open>Index into JSON string\<close>
abbreviation \<open>global_error \<equiv> \<guillemotleft>\<lparr>json = None, position = 0\<rparr>\<guillemotright>\<close> (* TODO: fix up, must be a lens *)

(* Creating a new alphabet to add global_error as a global variable would be a pain as it would
require a lot of manual copypasting, so going with good old pass-as-argument style. *)
definition \<open>cJSON_GetErrorPtr g = drop\<^sub>u(&g\<lparr>position\<rparr>\<^sub>r, &g\<lparr>json\<rparr>\<^sub>r)\<close>
(* TODO: Need to figure out how to use option type on the UTP level. *)

definition \<open>cJSON_Version = shows\<^sub>u(CJSON_VERSION_MAJOR) ^\<^sub>u \<guillemotleft>''.''\<guillemotright> ^\<^sub>u
                            shows\<^sub>u(CJSON_VERSION_MINOR) ^\<^sub>u \<guillemotleft>''.''\<guillemotright> ^\<^sub>u
                            shows\<^sub>u(CJSON_VERSION_PATCH)\<close>

end
