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

theory Syntax_Interface
  imports "../Backend/VCG/vcg"
  keywords "program_spec" :: thy_goal
  and "assumes_utp" "ensures_utp" "prog_utp" "vcg_sp" "vcg_wp" :: quasi_command
begin

method vcg_prog_spec = vcg wp | vcg sp

ML\<open>
structure Element' = struct

datatype ('typ, 'term, 'fact) ctxt_stmt =
  Shows of (Attrib.binding * ('term * 'term list) list) list |
  Obtains of ('typ, 'term) Element.obtain list |
  Fixes of (binding * 'typ option * mixfix) list |
  Constrains of (string * 'typ) list |
  Assumes of (Attrib.binding * ('term * 'term list) list) list |
  Defines of (Attrib.binding * ('term * 'term list)) list |
  Notes of string * (Attrib.binding * ('fact * Token.src list) list) list |
  Assumes_UTP of 'term |
  Ensures_UTP of 'term |
  Prog_UTP of 'term |
  Vcg_sp |
  Vcg_wp
type context = (string, string, Facts.ref) ctxt_stmt

fun to_elem_stmt l = 
  case
    ( map_filter (fn Shows l => SOME l | _ => NONE) l
    , map_filter (fn Obtains l => SOME l | _ => NONE) l)
  of (l_shows, []) =>
      let val l_shows = List.concat l_shows
          val escape = map (fn s => "(" ^ YXML.content_of s ^ ")") in
        case
          ( map_filter (fn Assumes_UTP t => SOME t | _ => NONE) l
          , map_filter (fn Ensures_UTP t => SOME t | _ => NONE) l
          , map_filter (fn Prog_UTP t => SOME t | _ => NONE) l)
        of (l_ass, l_ens, [t_prog]) =>
             ( SOME (l_ass, l_ens, t_prog)
             , Element.Shows
                 ((Binding.empty_atts,
                  [(String.concatWith
                      " "
                      ("hoare_prog_t"
                       :: (case l_ass of [] => "utrue" | _ => "(" ^ String.concatWith "\<and>\<^sub>p" (escape l_ass) ^ ")")
                       :: escape [t_prog]
                        @ [case l_ens of [] => "ufalse" | _ => "(" ^ String.concatWith "\<and>\<^sub>p" (escape l_ens) ^ ")"]), [])])
                 :: l_shows))
         | _ => (NONE, Element.Shows ((case l_shows of [] => warning "not yet supported" | _ => ()); l_shows))
      end
   | ([], l) => (NONE, Element.Obtains (List.concat l))
   | _ => error "shows and obtains are both present"

val to_elem_context_list = 
  map_filter (fn Fixes l => SOME (Element.Fixes l)
               | Constrains l => SOME (Element.Constrains l)
               | Assumes l => SOME (Element.Assumes l)
               | Defines l => SOME (Element.Defines l)
               | Notes l => SOME (Element.Notes l)
               | _ => NONE)

val exists_assumes = List.exists (fn Assumes _ => true | _ => false)
end

structure Parse_Spec' = struct

local

val loc_element =
  Parse.$$$ "fixes" |-- Parse.!!! Parse_Spec.locale_fixes >> Element'.Fixes ||
  Parse.$$$ "constrains" |--
    Parse.!!! (Parse.and_list1 (Parse.name -- (Parse.$$$ "::" |-- Parse.typ)))
    >> Element'.Constrains ||
  Parse.$$$ "assumes" |-- Parse.!!! (Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Scan.repeat1 Parse.propp))
    >> Element'.Assumes ||
  Parse.$$$ "defines" |-- Parse.!!! (Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Parse.propp))
    >> Element'.Defines ||
  Parse.$$$ "notes" |-- Parse.!!! (Parse.and_list1 (Parse_Spec.opt_thm_name "=" -- Parse.thms1))
    >> (curry Element'.Notes "") ||
  Parse.$$$ "obtains" |-- Parse.!!! Parse_Spec.obtains >> Element'.Obtains ||
  Parse.$$$ "shows" |-- Parse.!!! Parse_Spec.statement >> Element'.Shows ||
  Parse.$$$ "assumes_utp" |-- Parse.!!! Parse.term >> Element'.Assumes_UTP ||
  Parse.$$$ "ensures_utp" |-- Parse.!!! Parse.term >> Element'.Ensures_UTP ||
  Parse.$$$ "prog_utp" |-- Parse.!!! Parse.term >> Element'.Prog_UTP ||
  Parse.$$$ "vcg_sp" >> K Element'.Vcg_sp ||
  Parse.$$$ "vcg_wp" >> K Element'.Vcg_wp;

in

val context_element = Parse.group (fn () => "context element") loc_element;

end;

val long_statement = Scan.repeat context_element;

val long_statement_keyword =
  Parse.$$$ "fixes" || Parse.$$$ "constrains" || Parse.$$$ "assumes" ||
  Parse.$$$ "defines" || Parse.$$$ "notes" ||
  Parse.$$$ "obtains" || Parse.$$$ "shows" ||
  Parse.$$$ "assumes_utp" || Parse.$$$ "ensures_utp" || Parse.$$$ "prog_utp" ||
  Parse.$$$ "vcg_sp" || Parse.$$$ "vcg_wp";

end

local

val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec'.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec'.long_statement
    >> (fn ((binding, includes), elems) => (true, binding, includes, elems));

val _ = Outer_Syntax.commands @{command_keyword program_spec} ""
 (long_statement >> 
  (fn (long, binding, includes, elems) =>
  List.concat
    [ [(@{command_keyword lemma},
        Toplevel.local_theory_to_proof' NONE NONE
          (fn b => fn ctxt =>
            let val (assumes, shows) =
                  case Element'.to_elem_stmt elems of
                    (SOME (l_ass, l_ens, t_prog), shows) =>
                      let val (t_prog :: _) = Syntax.read_terms ctxt (t_prog :: l_ass @ l_ens)
                          fun get_vars acc t =
                            (fn Const (@{const_name passigns}, _)
                                $ ( Const (@{const_name subst_upd_uvar}, _)
                                  $ Const (@{const_name id}, _)
                                  $ ( Const (@{const_name pr_var}, _)
                                    $ Free (s, _))
                                  $ _) => s :: acc
                              | Abs (_, _, t) => get_vars acc t
                              | op $ (t1, t2) => get_vars (get_vars acc t1) t2
                              | _ => acc) t
                          fun f_bowtie acc l = case l of x :: xs => f_bowtie (map (pair x) xs :: acc) xs
                                                       | [] => acc
                          val assign_vars = get_vars [] t_prog |> Symtab.make_set |> Symtab.keys in
                      ( map (fn x => Element.Assumes [(Binding.empty_atts, [(@{const_name vwb_lens} ^ " " ^ x, [])])]) assign_vars
                        @
                        map (fn (x1, x2) => Element.Assumes [(Binding.empty_atts, [(@{const_name lens_indep} ^ " " ^ x1 ^ " " ^ x2, [])])])
                            (List.concat (f_bowtie [] assign_vars))
                      , shows)
                      end
                  | (NONE, shows) => ([], shows) in
            Specification.theorem_cmd long Thm.theoremK NONE (K I) binding includes (assumes @ Element'.to_elem_context_list elems) shows b ctxt end))]
    , [(@{command_keyword apply},
        let val m = ( Method.Combinator (Method.no_combinator_info, Method.Then,
                                           [Method.Basic (fn ctxt => Method.insert (Proof_Context.get_thms ctxt "assms" handle ERROR _ => []))])
                    , (Position.none, Position.none)) in
        (Method.report m; Toplevel.proofs (Proof.apply m))
        end)]
    , [(@{command_keyword apply},
        let val m = ( Method.Combinator
                        ( Method.no_combinator_info
                        , Method.Then
                        , [Method.Source
                            (case map_filter (fn Element'.Vcg_sp => SOME true
                                               | Element'.Vcg_wp => SOME false
                                               | _ => NONE) elems
                               of [true] => [Token.make_string ("vcg", Position.none), Token.make_string ("sp", Position.none)]
                                | [false] => [Token.make_string ("vcg", Position.none), Token.make_string ("wp", Position.none)]
                                | [] => [Token.make_string ("vcg_prog_spec", Position.none)]
                                | _ => error "Combination of vcg options not yet supported")])
                    , (Position.none, Position.none)) in
        (Method.report m; Toplevel.proofs (Proof.apply m))
       end) ]]))
in end\<close>
  
end
