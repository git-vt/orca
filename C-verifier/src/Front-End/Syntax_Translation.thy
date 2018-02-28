(******************************************************************************
 * Orca: A Functional Correctness Verifier for Imperative Programs
 *       Based on Isabelle/UTP
 *
 * Copyright (c) 2016-2018 Virginia Tech, USA
 *               2016-2018 Technische Universität München, Germany
 *               2016-2018 University of York, UK
 *               2016-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * This software may be distributed and modified according to the terms of
 * the GNU Lesser General Public License version 3.0 or any later version.
 * Note that NO WARRANTY is provided.
 *
 * See CONTRIBUTORS, LICENSE and CITATION files for details.
 ******************************************************************************)

theory Syntax_Translation
imports Main
keywords "translations_params" "translations'" :: thy_decl
  and "parse_ast_translation'" "parse_translation'" "print_translation'"
    "typed_print_translation'" "print_ast_translation'" :: thy_decl % "ML"
begin

ML\<open>
(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_commands.ML
    Author:     Jasmin Blanchette, TU Muenchen

Adds "sledgehammer" and related commands to Isabelle/Isar's outer syntax.
*)

structure Sledgehammer_Commands' =
struct

open ATP_Util
open Sledgehammer_Util
open Sledgehammer_Prover
open Sledgehammer_Prover_Minimize

(*** parameters ***)


type raw_param = string * string list

val default_default_params =
  [("parse", "true"),
   ("print", "true"),
   ("equal_as_parse", "false"),
   ("equal_as_print", "false")]

val alias_params =
  []
val negated_alias_params =
  [("no_parse", "parse"),
   ("no_print", "print")]

val property_dependent_params = []

fun is_known_raw_param s =
  AList.defined (op =) default_default_params s orelse
  AList.defined (op =) alias_params s orelse
  AList.defined (op =) negated_alias_params s orelse
  member (op =) property_dependent_params s (*orelse s = "expect"*)

fun is_prover_list ctxt s =
  (case space_explode " " s of
    ss as _ :: _ => forall (is_prover_supported ctxt) ss
  | _ => false)

fun unalias_raw_param (name, value) =
  (case AList.lookup (op =) alias_params name of
    SOME (name', []) => (name', value)
  | SOME (param' as (name', _)) =>
    if value <> ["false"] then
      param'
    else
      error ("Parameter " ^ quote name ^ " cannot be set to \"false\" (cf. " ^ quote name' ^ ")")
  | NONE =>
    (case AList.lookup (op =) negated_alias_params name of
      SOME name' => (name',
        (case value of
          ["false"] => ["true"]
        | ["true"] => ["false"]
        | [] => ["false"]
        | _ => value))
    | NONE => (name, value)))


(* "provers =", "type_enc =", "lam_trans =", "fact_filter =", and "max_facts ="
   can be omitted. For the last four, this is a secret feature. *)
fun normalize_raw_param ctxt =
  unalias_raw_param
  #> (fn (name, value) =>
         if is_known_raw_param name then
           (name, value)
         else if null value then
           (*if is_prover_list ctxt name then
             ("provers", [name])
           else if can (type_enc_of_string Strict) name then
             ("type_enc", [name])
           else if can (trans_lams_of_string ctxt any_type_enc) name then
             ("lam_trans", [name])
           else if member (op =) fact_filters name then
             ("fact_filter", [name])
           else if is_some (Int.fromString name) then
             ("max_facts", [name])
           else*)
             error ("Unknown parameter: " ^ quote name)
         else
           error ("Unknown parameter: " ^ quote name))

(* Ensures that type encodings such as "mono_native?" and "poly_guards!!" are
   read correctly. *)
val implode_param = strip_spaces_except_between_idents o space_implode " "

(* FIXME: use "Generic_Data" *)
structure Data = Theory_Data
(
  type T = raw_param list
  val empty = default_default_params |> map (apsnd single)
  val extend = I
  fun merge data : T = AList.merge (op =) (K true) data
)


fun set_default_raw_param param thy =
  let val ctxt = Proof_Context.init_global thy in
    thy |> Data.map (AList.update (op =) (normalize_raw_param ctxt param))
  end

fun default_raw_params mode thy =
  let val ctxt = Proof_Context.init_global thy in
    Data.get thy
    |> fold (AList.default (op =))
         [(*("provers", [(case !provers of "" => default_provers_param_value mode ctxt | s => s)]),
          ("timeout",
           let val timeout = Options.default_int @{system_option sledgehammer_timeout} in
             [if timeout <= 0 then "none" else string_of_int timeout]
           end)*)]
  end

fun extract_params mode default_params override_params =
  let
    val raw_params = rev override_params @ rev default_params
    val lookup = Option.map implode_param o AList.lookup (op =) raw_params
    val lookup_string = the_default "" o lookup

    fun general_lookup_bool option default_value name =
      (case lookup name of
        SOME s => parse_bool_option option name s
      | NONE => default_value)
    val lookup_bool = the o general_lookup_bool false (SOME false)
    fun lookup_time name =
      (case lookup name of
        SOME s => parse_time name s
      | NONE => Time.zeroTime)
    fun lookup_int name =
      (case lookup name of
        NONE => 0
      | SOME s =>
        (case Int.fromString s of
          SOME n => n
        | NONE => error ("Parameter " ^ quote name ^ " must be assigned an integer value")))
    fun lookup_real name =
      (case lookup name of
        NONE => 0.0
      | SOME s =>
        (case Real.fromString s of
          SOME n => n
        | NONE => error ("Parameter " ^ quote name ^ " must be assigned a real value")))
    fun lookup_real_pair name =
      (case lookup name of
        NONE => (0.0, 0.0)
      | SOME s =>
        (case s |> space_explode " " |> map Real.fromString of
          [SOME r1, SOME r2] => (r1, r2)
        | _ => error ("Parameter " ^ quote name ^ " must be assigned a pair of floating-point \
                 \values (e.g., \"0.6 0.95\")")))
    fun lookup_option lookup' name =
      (case lookup name of
        SOME "smart" => NONE
      | _ => SOME (lookup' name))
    val parse = lookup_bool "parse"
    val print = lookup_bool "print"
    val equal_as_parse = lookup_bool "equal_as_parse"
    val equal_as_print = lookup_bool "equal_as_print"
    val _ = if equal_as_parse andalso equal_as_print then
              error "Combination of options not yet supported"
            else ()
  in
    {parse = parse, print = print, equal_as_parse = equal_as_parse, equal_as_print = equal_as_print}
  end

fun get_params mode = extract_params mode o default_raw_params mode

fun get_params' f (override_params, args) thy = 
  f (get_params Normal thy (override_params
     |> map (normalize_raw_param (Proof_Context.init_global thy)))) args thy

fun string_of_raw_param (key, values) =
  key ^ (case implode_param values of "" => "" | value => " = " ^ value)

val parse_query_bang = @{keyword "?"} || @{keyword "!"} || @{keyword "!!"}
val parse_key = Scan.repeat1 (Parse.embedded || parse_query_bang) >> implode_param
val parse_value = Scan.repeat1 (Parse.name || Parse.float_number || parse_query_bang)
val parse_param = parse_key -- Scan.optional (@{keyword "="} |-- parse_value) []
val parse_params = Scan.optional (Args.bracks (Parse.list parse_param)) []

val _ =
  Outer_Syntax.command @{command_keyword translations_params}
    "set and display the default parameters"
    (parse_params >> (fn params =>
      Toplevel.theory (fold set_default_raw_param params #> tap (fn thy =>
        writeln ("Default parameters:\n" ^
          (case rev (default_raw_params Normal thy) of
            [] => "none"
          | params => params |> map string_of_raw_param |> sort_strings |> cat_lines))))))

end
\<close>

ML\<open>
val trans_pat =
  Scan.optional
    (@{keyword "("} |-- Parse.!!! (Parse.inner_syntax Parse.name --| @{keyword ")"})) "logic"
    -- Parse.inner_syntax Parse.string;

fun trans_arrow toks =
  ((@{keyword "\<rightharpoonup>"} || @{keyword "=>"}) >> K Syntax.Parse_Rule ||
    (@{keyword "\<leftharpoondown>"} || @{keyword "<="}) >> K Syntax.Print_Rule ||
    (@{keyword "\<rightleftharpoons>"} || @{keyword "=="}) >> K Syntax.Parse_Print_Rule) toks;

val trans_line =
  trans_pat -- Parse.!!! (trans_arrow -- trans_pat)
    >> (fn (left, (arr, right)) => arr (left, right));

local
open Sledgehammer_Commands'
val _ =
  Outer_Syntax.command @{command_keyword translations'} "add syntax translation rules"
    (parse_params -- Scan.repeat1 trans_line >>
      (Toplevel.theory
       o get_params' (fn {parse, print, equal_as_parse, equal_as_print} => fn args =>
          Isar_Cmd.translations
            (args |> equal_as_parse ? map (fn Syntax.Parse_Print_Rule x => Syntax.Parse_Rule x | x => x)
                  |> equal_as_print ? map (fn Syntax.Parse_Print_Rule x => Syntax.Print_Rule x | x => x)
                  |> not parse ? map_filter (fn Syntax.Parse_Rule _ => NONE | x => SOME x)
                  |> not print ? map_filter (fn Syntax.Print_Rule _ => NONE | x => SOME x)))));
in end
\<close>
  
ML \<open>
local
open Sledgehammer_Commands'

val _ =
  Outer_Syntax.command @{command_keyword parse_ast_translation'}
    "install parse ast translation functions"
    (parse_params -- Parse.ML_source >> (Toplevel.theory
       o get_params' (fn {parse, ...} => fn source =>
                        parse ? Isar_Cmd.parse_ast_translation source)));

val _ =
  Outer_Syntax.command @{command_keyword parse_translation'}
    "install parse translation functions"
    (parse_params -- Parse.ML_source >> (Toplevel.theory
       o get_params' (fn {parse, ...} => fn source =>
                        parse ? Isar_Cmd.parse_translation source)));

val _ =
  Outer_Syntax.command @{command_keyword print_translation'}
    "install print translation functions"
    (parse_params -- Parse.ML_source >> (Toplevel.theory
       o get_params' (fn {print, ...} => fn source =>
                        print ? Isar_Cmd.print_translation source)));

val _ =
  Outer_Syntax.command @{command_keyword typed_print_translation'}
    "install typed print translation functions"
    (parse_params -- Parse.ML_source >> (Toplevel.theory
       o get_params' (fn {print, ...} => fn source =>
                        print ? Isar_Cmd.typed_print_translation source)));

val _ =
  Outer_Syntax.command @{command_keyword print_ast_translation'}
    "install print ast translation functions"
    (parse_params -- Parse.ML_source >> (Toplevel.theory
       o get_params' (fn {print, ...} => fn source =>
                        print ? Isar_Cmd.print_ast_translation source)));

in end\<close>

end