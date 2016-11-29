theory SymbolicState
imports Main

begin
section \<open>C-state\<close>
subsection \<open>Generic type\<close>
text \<open>When formalizing C semantics, our first challenge is to find a generic type for
      the state. What is the state of the program? 
      In our framework we split a program into two part: the symbolic part and the physical part.
      In the sequel we will talk about the symbolic part.
      Our framework follows the terminology of Glynn Winskel.
      The symbolic part of the program consists of its source code. 
      The source code
      can be seen as a relation between symbolic names and their content represented by
      the \emph{evaluation} of the different \emph{expressions}. 
      This relation is updated by \emph{commands}. The commands can 
      update the content of symbolic names by new values or provide an \emph{observation}. 
      When a command update a state it can provide a value for a given
      symbolic name or an observation. The state of the source code of a program is 
      represented by a record type. Two main relations characterise the state,
       @{term values} and @{term observations}.
      The field @{term inputs} is used to trace the executed commands on the state. This
      field will be used for testing purposes, where the recorded trace will be used
      in testing scenarios for the real implementation of the source code. 
      The field @{term bugs} is used for proofs purposes. Any time a command detect an expression
      with a bug, \eg, an arithmetic expression with division by zero, the command prepend a
      bug value on the field @{term bugs}. Bug values are explicitly represented by a datatype
      enumerating the different bugs covered by our specification. Proving that the verified
      source code does not contain a given bug is reduced to prove that the field @{term bugs}
      contains an empty list.
     \<close>

record ('name, 'val, 'inputs, 'obs, 'bugs) state = 
  "values"     :: "('name  \<times> ('name list) option) \<Rightarrow> 'val option"
  inputs       :: "'inputs list"
  observations :: "('name  \<times> ('name list) option) \<Rightarrow> 'obs option"
  bugs         :: "'bugs list"


end