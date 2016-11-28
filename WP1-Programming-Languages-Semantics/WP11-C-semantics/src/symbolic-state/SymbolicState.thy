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
      update the content symbolic names by new values or provide an \emph{observation} on
      the evaluation process. When a command update 
      We  formalize this relation by the field @{term source_code} in the 
      record @{term source_code}.
      
     \<close>

record ('name, 'val, 'inputs, 'obs, 'bugs) state = 
  "values"     :: "('name  \<times> ('name list) option) \<Rightarrow> 'val option"
  inputs       :: "'inputs list"
  observations :: "('name  \<times> ('name list) option) \<Rightarrow> 'obs option"
  bugs         :: "'bugs list"
  
text \<open>A name is just a concatenation of chars.
      A value is a result of an \emph{evaluation} of a given \emph{expression}.
      In our formalization a symbolic state defines a relation between
      names and, the  \emph{evaluation} of the different
      expressions, in a source code.\<close>

end