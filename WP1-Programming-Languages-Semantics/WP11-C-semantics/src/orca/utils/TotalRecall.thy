(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: TotalRecall.thy                                                      *)
(* Authors: Simon Foster & Frank Zeyda (University of York, UK)               *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)

section {* Recall Undeclarations *}

theory TotalRecall
imports Main
keywords
  "purge_syntax" :: thy_decl and
  "purge_notation" :: thy_decl and
  "recall_syntax" :: thy_decl
begin

subsection {* ML File Import *}
                   
ML_file "TotalRecall.ML"

ML {*
  val _ =
    Outer_Syntax.command @{command_keyword purge_syntax}
      "purge raw syntax clauses"
      ((Scan.repeat1 Parse.const_decl) >> 
        (Toplevel.theory o  (fn args => 
          (TotalRecall.record_no_syntax Syntax.mode_input args) o 
          (Sign.del_syntax_cmd Syntax.mode_input args))));

  val _ =
    Outer_Syntax.local_theory @{command_keyword purge_notation}
      "purge concrete syntax for constants / fixed variables"
      ((Parse.and_list1 (Parse.const -- Parse.mixfix)) >>
        (fn args =>
          (Local_Theory.background_theory
            (TotalRecall.record_no_notation Syntax.mode_input args)) o
          (Specification.notation_cmd false Syntax.mode_input args)));

  val _ =
    Outer_Syntax.command @{command_keyword recall_syntax}
      "recall undecarations of all purged items"
      (Scan.succeed (Toplevel.theory TotalRecall.execute_all))
*}
end