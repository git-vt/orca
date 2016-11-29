theory SymbolicStateInst
imports SymbolicState
        (*"$ISABELLE_HOME/src/HOL/Library/Float"*)
       "$ISABELLE_HOME/src/HOL/Real"

begin
subsection \<open>Instantiations for the state type\<close>
text \<open>In this theory we instantiate the arguments of the state type @{typ "('name, 'val, 'inputs, 'obs, 'bugs)state"}
         in @{theory SymbolicState} by other types.\<close>

text \<open>A name is just a concatenation of chars this argument is intantiated by @{typ "string"}.
      \<close>

text \<open>A value is a result of an evaluation of a given expression in C language.
      For the moment we focus on the basic C types to encode the expressions of C in our 
      specification.
      The argument value in @{typ "('name, 'val, 'inputs, 'obs, 'bugs)state"},
      can have the following:
      \begin {itemize}
        \item Basic Types: integer types such as:@{typ "char"},@{term "unsigned char"},
             @{term "int32"}, and all types that
               cast up and down with @{typ "int"}. Also, we have 
               all floating point types cast up and down with @{typ "real"}.
        \item Enumeration types: a subset of basic types.
        \item Derived types: pointers type, structures types, array types, functions types.
      \end {itemize}\<close>

text \<open>In @{typ "('name, 'val, 'inputs, 'obs, 'bugs)state"},
      inputs are abstractions on the executed commands. Commands are represented
      by a shallow embedding. Each time a command is executed, it updates the field input by its
      abstraction. For the moment these abstractions are without arguments but it will be changed 
      during the development.\<close>

text \<open>Observations, are abstract values for the execution of the commands on the state.
      It is used to highlight abrupt terminations of loops and recursive functions etc.\<close>

text \<open>Bugs, are captured by the different commands. They represent an abstraction on an undesired
      behavior in the system under verification.\<close>


datatype vals = Int int|Real real
datatype inputs = basic|conditional|loop|funDef|decl
datatype obs = abrupts
datatype bugs = DivByZero

type_synonym stateInst = "(string, vals, inputs, obs, bugs) state"


end