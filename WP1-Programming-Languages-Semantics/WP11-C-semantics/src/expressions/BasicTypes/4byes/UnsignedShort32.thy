theory SymbolicState
imports Main

begin
section \<open>C-state\<close>
subsection \<open>Generic type\<close>
text \<open>When formalizing C semantics, our first challenge is to find a generic type for
      the state. What is the state of the program? 
      In our framework we split a program into two part: the symbolic part and the physical part.
      In the sequel we will talk about the symbolic part.
      Our framework follows the terminology of Glyn Winskel.
      The symbolic the program  consists of its source code. 
      The source code
      can be seen as a relation between symbolic names and their \emph{values}.
      We call this relation a state and we formalize it by:
     \<close>

type_synonym ('name, 'val) state = "('name  \<times> ('name list) option) \<Rightarrow> 'val option"

text \<open>A name is just a concatenation of chars.
      A value is a result of an \emph{evaluation} of a given \emph{expression}.
      In our formalization a symbolic state defines a relation between
      names and, the  \emph{evaluation} of the different
      expressions, in a source code.\<close>

end