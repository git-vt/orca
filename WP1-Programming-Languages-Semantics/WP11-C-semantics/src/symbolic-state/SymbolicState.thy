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
      The symbolic part of the program consists of the state of the program's source code. 
      The state characterising the source code of the program
      can be seen as a relation between symbolic names and their content. The content
      is represented by an \emph{evaluation} of the a given \emph{expression}.
      Since we opted for shallow embedding we do not need to express explicitly the type
      of the different expressions and their evaluation functions.
      The state is updated by \emph{commands}. The commands can 
      update the content of symbolic names by new values or provide an \emph{observation}. 
      The state of the source code of a program is 
      represented by a record type. Two main relations characterise the state,
       @{term values} functions and @{term observations} functions. The other fields
      represent information holders.
     \<close>

record ('name, 'val, 'inputs, 'obs, 'bugs) state = 
  gVars    :: "'name list"
  gFuns    :: "'name list"
  gVarsVal :: "'name \<Rightarrow> 'val option option"
  gVarObs  :: "'name \<Rightarrow> 'obs option"
  gFunVal  :: "('name  \<times> ('name list) option) \<Rightarrow> 'val option option"
  gFunObs  :: "'name \<Rightarrow> 'obs option"
  gfunLVars:: "'name  \<Rightarrow> ('name list) option"
  lVars    :: "('name  \<times> 'name) list"
  lVarsVal :: "('name  \<times> 'name) \<Rightarrow> 'val option option"
  lVarsObs :: "('name  \<times> 'name) \<Rightarrow> 'obs option"
  lVarFun  :: "'name  \<Rightarrow> 'name option"
  inputs   :: "'inputs list"
  bugs     :: "'bugs list"

text \<open>The type @{typ " ('name, 'val, 'inputs, 'obs, 'bugs) state"} specifies
      a container for evaluations such as: @{const gVarsVal},  @{const lVarsVal}, 
      @{const gfunLVars} etc. and also a container for stacks to hold needed information from the source
      code such as: @{const gVars} @{const gFuns} @{const lVars} etc.
      The different fields characterise the symbolic state of a C source code, the role of each 
      field and its inputs and output is explained in the sequel:
     \begin{itemize}
        \item field @{const gVars}: This field is a stack used to store  all global variables name.
        \item field @{const gFuns}: This field is a stack used to store  all functions name.
        \item field @{const gVarsVal}: This field is an evaluation function for global variables. 
              It takes as an input the name of the global variable and returns as an output a value
              of the variable. The output value is characterised by a double lifting to capture
              undefined variables values by @{value "Some None"} during a declaration for example.
              Initialized variables are captured by @{value "Some val"}. 
        \item field @{const gVarObs}: This field stores observations after the execution of 
              a given command on a \emph{declared} global function such as casts de-cast etc.
        \item field @{const gFunVal}: This field is an evaluation function for functions, in C
              any function returns a value. The output value is characterised by a double 
              lifting to capture undefined values for function return  by @{value "Some None"} 
              Initialized variables are captured by @{value "Some val"}.
        \item field @{const gFunObs}: This field stores observations after the execution of 
              a given command inside a function such as commands resulting with abrupt terminations
              etc.
        \item field @{const gfunLVars}: This field is used to get all local variables
              of a function.
        \item field @{const lVars}: This field is a stack of local variables.
        \item field @{const lVarsVal}: This field is an evaluation function for local variables.
        \item field @{const lVarsObs}: This field stores observations after the execution of 
              a given command on a \emph{declared} local variable.
        \item field @{const lVarFun}: This field is used to get the function name of a given
              local variable.
        \item field @{const inputs}: This field is a stack of inputs abstracting the executed 
              commands. It main use will be in testing scenarios for the verified program.
        \item field @{const bugs}: This field is a stack of bugs abstracting the verified
              property. It main use will be in deductive verification; If this field is empty
              then the system under verification is correct with regard the specification;
              if it contains something then one or more properties are not satisfied by the 
              system under verification
     \end{itemize}   
     \<close>

end