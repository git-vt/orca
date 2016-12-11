theory StatementsUpdates
imports "../symbolic-state/SymbolicStateInst"

begin
section \<open>C-statements\<close>

text \<open>Statements are functions that update the state (\ie, program instructions,program commands). 
      Since we opt for shallow embedding,
      statements are represented by constant definitions, function definitions with 
      well founded recursions etc. A statement takes \emph{arguments} and a state, 
      and it returns an updated state. The generic type of statements is:\<close>

type_synonym  'a statements = 
             "'a stateInst \<Rightarrow> 'a stateInst"

subsection \<open>Statements for global constants declaration\<close>

text \<open>The constant definition @{term "declIni_gCons"} is a specification for global constants
      declaration \emph{with} value initialization, \ie, away to specify variables with read only
      capability in C language. In other words, constants can not be updated during the execution. 
      All the checks are wrapped around  @{term "declIni_gCons"} later by a different function. 
      An example of a check function is: if the constant name was declared before for another constant
      then a bug is pre-pended in @{term "bugs"} else @{term "declIni_gConsCons"} is executed. 
      In the sequel we focus only on the updates done by @{term "declIni_gCons"}:
      \begin{itemize}
         \item inputs: 
                 \begin{itemize}
                    \item  a constant name @{term "name"} of type @{typ "string"}.
                    \item  a value @{term "val"} of type @{typ "vals option option"}
                           for the constant name.
                    \item  a state @{term "\<sigma>"} of type @{typ "'a stateInst"}
                  \end{itemize}
         \item output: 
               a new state @{term "\<sigma>'"} of type @{typ "'a stateInst"} with the following updated 
               fields:
                 \begin{itemize}
                    \item Since global constants name is specified by  @{term "name"}
                          we update the field @{term "gConsts"} of the record 
                          by pre-pending the name of the global constant .
                    \item The field @{term "gConsVal"} is updated by the given value @{term "val"}.
                    \item An abstraction of the operation  @{term "declIni_gConsCons"}
                          is pre-pended in @{term "inputs"} 
                 \end{itemize}
      \end{itemize}\<close>

definition declIni_gCons :: 
  "string \<Rightarrow> vals \<Rightarrow>  'a statements" where
  "declIni_gCons name val =  
    (\<lambda>\<sigma>. \<sigma>\<lparr>gConsts  := name#gConsts \<sigma>,
           gConsVal := gConsVal \<sigma>(name \<mapsto> Some val),
           inputs   := DeclIni_gCons name (Some (Some val)) #inputs \<sigma>\<rparr>)"

text \<open>The constant definition @{term "declIni_gConsCons"} is a specification for global constants
      declaration with an initialization value contained in another constant, \ie, 
      away to specify read only variables initialized by another read only variable 
      in C language. Constants can not be updated during the execution. 
      All the checks are wrapped around @{term "declIni_gConsCons"} later by a different function.
      An example of a check function is: if the constant name was declared before for another constant
      then a bug is pre-pended in @{term "bugs"} else @{term "declIni_gConsCons"} is executed. 
      In the sequel we focus only on the updates done by @{term "declIni_gConsCons"}:
      \begin{itemize}
         \item inputs: 
                 \begin{itemize}
                    \item  a constant name @{term "name"} of type @{typ "string"}.
                    \item a constant name @{term "name"} of type @{typ "string"}.
                    \item  a state @{term "\<sigma>"} of type @{typ "'a stateInst"}
                  \end{itemize}
         \item output: 
              The same state @{term "\<sigma>"} of type @{typ "'a stateInst"} with no updates.
              This statements is allowed in C but it leads always to an error 
              (see\autoref{subsec:statementsSynEval}).    
      \end{itemize}\<close>

definition declIni_gConsCons :: 
  "string \<Rightarrow> string \<Rightarrow>  'a statements" where
  "declIni_gConsCons name name' =  (\<lambda>\<sigma>. \<sigma>)"

text \<open>The constant definition @{term "declNone_gCons"} is a specification for global constants
      declaration with no initialization value, \ie, 
      away to specify read only variables that is not initialized. 
     Constants can not be updated during the execution. 
      All the checks are wrapped around @{term "declNone_gCons"} later by a different function.
      An example of a check function is: if the constant name was declared before for another constant
      then a bug is pre-pended in @{term "bugs"} else @{term "declNone_gCons"} is executed. 
      In the sequel we focus only on the updates done by @{term "declNone_gCons"}:
      \begin{itemize}
         \item inputs: 
                 \begin{itemize}
                    \item  a constant name @{term "name"} of type @{typ "string"}.
                    \item  a state @{term "\<sigma>"} of type @{typ "'a stateInst"}
                  \end{itemize}
         \item output: 
               a new state @{term "\<sigma>'"} of type @{typ "'a stateInst"} with the following updated 
               fields:
                 \begin{itemize}
                    \item Since global constants name is specified by  @{term "name"}
                          we update the field @{term "gConsts"} of the record 
                          by pre-pending the global constant name.
                    \item The field @{term "gConsVal"} is updated by  @{value "Some None"} which
                          specify that the constant is not initialized.
                    \item An abstraction of the operation used to declare constants
                          is pre-pended in @{term "inputs"} 
                 \end{itemize}
      \end{itemize}\<close>

definition declNone_gCons :: 
  "string \<Rightarrow>  'a statements" where
  "declNone_gCons name =  
    (\<lambda>\<sigma>. \<sigma>\<lparr>gConsts  := name#gConsts \<sigma>,
           gConsVal := gConsVal \<sigma>(name \<mapsto> None),
           inputs   := DeclNone_gCons name #inputs \<sigma>\<rparr>)"

subsection \<open>Statements for global variables declaration\<close>

text \<open>The constant definition @{term "declIni_gVar"} is a specification for global variables
      declaration \emph{with} value initialization.
      \begin{itemize}
         \item inputs: 
                 \begin{itemize}
                    \item  a variable name @{term "name"} of type @{typ "string"}.
                    \item  a value @{term "val"} for the variable name.
                    \item  a state @{term "\<sigma>"} of type @{typ "'a stateInst"}
                  \end{itemize}
         \item output: 
               a new state @{term "\<sigma>'"} of type @{typ "'a stateInst"} with the following updated 
               fields:
                 \begin{itemize}
                    \item Since global variables name is specified by a pair @{term "name"}
                          we update the field @{term "gVars"} of the record 
                          by pre-pending the global variable name.
                    \item The field @{term "gVarsVal"} is updated by mapping
                          @{term "name"} with @{term "val"}.
                    \item An abstraction of the operation used to declare constants
                          is pre-pended in @{term "inputs"}
                 \end{itemize}
      \end{itemize}\<close>

definition declIni_gVar :: 
  "string \<Rightarrow> vals \<Rightarrow>  'a statements" where
  "declIni_gVar name val =  
    (\<lambda>\<sigma>. \<sigma>\<lparr>gVars    := name#gVars \<sigma>,
           gVarsVal := gVarsVal \<sigma>(name \<mapsto> Some val),
           inputs   := DeclIni_gVar name (Some (Some val)) #inputs \<sigma>\<rparr>)"

text \<open>The constant definition @{term "declIni_gVarVar"} is a specification for global variables
      declaration with value initialization contained in another variable name or function.
      \begin{itemize}
         \item inputs: 
                 \begin{itemize}
                    \item  a variable name @{term "name"} of type @{typ "string"}.
                    \item  a variable name @{term "name'"} of type @{typ "string"}.
                    \item  a state @{term "\<sigma>"} of type @{typ "'a stateInst"}
                  \end{itemize}
         \item output: 
               a new state @{term "\<sigma>'"} of type @{typ "'a stateInst"} with the following updated 
               fields:
                 \begin{itemize}
                    \item Since global variables name is specified by a pair @{term "name"}
                          we update the field @{term "gVars"} of the record 
                          by pre-pending the global variable name.
                    \item The field @{term "gVarsVal"} is updated by mapping
                          @{term "name"} with @{term "gVarsVal \<sigma> name'"}.
                    \item An abstraction of the operation used to declare constants
                          is pre-pended in @{term "inputs"}
                 \end{itemize}
      \end{itemize}\<close>

definition declIni_gVarVar :: 
  "string \<Rightarrow> string \<Rightarrow>  'a statements" where
  "declIni_gVarVar name name' =  
    (\<lambda>\<sigma>. \<sigma>\<lparr>gVars    := name#gVars \<sigma>,
           gVarsVal := (gVarsVal \<sigma>)(name := gVarsVal \<sigma> name'),
           inputs   := DeclIni_gVar name (gVarsVal \<sigma> name') #inputs \<sigma>\<rparr>)"

text \<open>The constant definition @{term "declNone_gVar"} is a specification for global variables
      with no initialization.
      \begin{itemize}
         \item inputs: 
                 \begin{itemize}
                    \item  a variable name @{term "name"} of type @{typ "string"}.
                    \item  a state @{term "\<sigma>"} of type @{typ "'a stateInst"}.
                  \end{itemize}
         \item output: 
               a new state @{term "\<sigma>'"} of type @{typ "'a stateInst"} with the following updated 
               fields:
                 \begin{itemize}
                    \item Since global variables name is specified by a pair @{term "name"}
                          we update the field @{term "gVars"} of the record 
                          by pre-pending the global variable name.
                    \item The field @{term "gVarsVal"} is updated by mapping
                          @{term "name"} with @{value "name"}.
                    \item An abstraction of the operation used to declare constants
                          is pre-pended in @{term "inputs"}
                 \end{itemize}
      \end{itemize}\<close>

definition declNone_gVar :: 
  "string \<Rightarrow> 'a statements" where 
  "declNone_gVar name = 
    (\<lambda>\<sigma>.  \<sigma>\<lparr>gVars    := name #gVars \<sigma>,
            gVarsVal := gVarsVal \<sigma>(name \<mapsto> None),
            inputs   := DeclNone_gVar name #inputs \<sigma>\<rparr>)"

subsection \<open>Statements for functions declaration\<close>
(*TODO YAKOUB: FIND AWAY TO REPRESENT C FUNCTION*)
definition declArgs_fun :: 
  "string \<Rightarrow>string list \<Rightarrow> 'a stateInst \<Rightarrow>  'a statements" where
  "declArgs_fun Fname Vnames \<sigma> = 
   (\<lambda>\<sigma>'. \<sigma>'\<lparr>gFuns    := Fname #gFuns \<sigma>',
            gFunVal  := (gFunVal \<sigma>')((Fname, Some Vnames) := gFunVal \<sigma> (Fname, Some Vnames)),
            gFunObs  := (gFunObs \<sigma>')(Fname := gFunObs \<sigma> Fname),
            gfunLVars:= (gfunLVars \<sigma>') (Fname:=  Some (Vnames @ the (gfunLVars \<sigma> Fname))),
            lVars    := lVars \<sigma> @ map (\<lambda>x. (Fname, x)) Vnames @ lVars \<sigma>',
            inputs   := (inputs \<sigma>')@(inputs \<sigma>),
            synBugs  := (synBugs \<sigma>)@(synBugs \<sigma>'),
            semBugs  := (semBugs \<sigma>)@(semBugs \<sigma>')\<rparr>)"

definition declNoArgs_fun :: 
  "string \<Rightarrow> 'a stateInst \<Rightarrow>  'a statements" where
  "declNoArgs_fun Fname \<sigma> = 
   (\<lambda>\<sigma>'.  \<sigma>'\<lparr>gFuns    := Fname #gFuns \<sigma>',
             gFunVal  := (gFunVal \<sigma>')((Fname, Some []) := gFunVal \<sigma> (Fname, Some [])),
             gFunObs  := (gFunObs \<sigma>')(Fname := gFunObs \<sigma> Fname),
             gfunLVars:= (gfunLVars \<sigma>') (Fname:=  Some (the (gfunLVars \<sigma> Fname))),
             lVars    := lVars \<sigma> @ lVars \<sigma>',
             inputs   := (inputs \<sigma>')@(inputs \<sigma>),
            synBugs  := (synBugs \<sigma>)@(synBugs \<sigma>'),
            semBugs  := (semBugs \<sigma>)@(semBugs \<sigma>')\<rparr>)"

subsection \<open>Statements for local variables declaration\<close>

definition declIni_lCons :: 
  "string \<Rightarrow>string \<Rightarrow> vals \<Rightarrow> 'a statements" where
  "declIni_lCons Fname Cname val = 
    (\<lambda>\<sigma>. \<sigma>\<lparr>lConsts  := (Fname, Cname)# lVars \<sigma>,
           gfunLVars:= (gfunLVars \<sigma>) (Fname:=  Some (Cname#the (gfunLVars \<sigma> Fname))),
           lConsVal := lVarsVal \<sigma>((Fname, Cname) \<mapsto> Some val),
           inputs   := DeclIni_lCons Fname Cname (Some(Some val))# inputs \<sigma>\<rparr>)"

definition declIni_lConsCons :: 
  "string \<Rightarrow>string \<Rightarrow> string \<Rightarrow> 'a statements" where
  "declIni_lConsCons Fname Cname Cname' = 
    (\<lambda>\<sigma>. \<sigma>\<lparr>lConsts  := (Fname, Cname)# lVars \<sigma>,
           gfunLVars:= (gfunLVars \<sigma>) (Fname:=  Some (Cname#the (gfunLVars \<sigma> Fname))),
           lConsVal := (lVarsVal \<sigma>)((Fname, Cname) := lVarsVal \<sigma> (Fname, Cname')),
           inputs   := DeclIni_lConsCons Fname Cname Cname'# inputs \<sigma>\<rparr>)"

definition declNone_lCons :: 
  "string \<Rightarrow>string \<Rightarrow>  'a statements" where 
  "declNone_lCons Fname Cname  = 
    (\<lambda>\<sigma>. \<sigma>\<lparr>lConsts  := (Fname, Cname)# lVars \<sigma>,
           gfunLVars:= (gfunLVars \<sigma>) (Fname:=  Some (Cname#the (gfunLVars \<sigma> Fname))),
           lConsVal := lVarsVal \<sigma>((Fname, Cname) \<mapsto> None),
           inputs   := DeclNone_lVar Fname Cname# inputs \<sigma>\<rparr>)"


subsection \<open>Statements for local variables declaration\<close>

definition declIni_lVar :: 
  "string \<Rightarrow>string \<Rightarrow> vals \<Rightarrow> 'a statements" where
  "declIni_lVar Fname Vname val = 
    (\<lambda>\<sigma>. \<sigma>\<lparr>lVars    := (Fname, Vname)# lVars \<sigma>,
           gfunLVars:= (gfunLVars \<sigma>) (Fname:=  Some (Vname#the (gfunLVars \<sigma> Fname))),
           lVarsVal := lVarsVal \<sigma>((Fname, Vname) \<mapsto> Some val),
           inputs   := DeclIni_lVar Fname Vname val# inputs \<sigma>\<rparr>)"

definition declIni_lVarVar :: 
  "string \<Rightarrow>string \<Rightarrow> string \<Rightarrow> 'a statements" where
  "declIni_lVarVar Fname Vname Vname' = 
    (\<lambda>\<sigma>. \<sigma>\<lparr>lVars    := (Fname, Vname)# lVars \<sigma>,
           gfunLVars:= (gfunLVars \<sigma>) (Fname:=  Some (Vname#the (gfunLVars \<sigma> Fname))),
           lVarsVal := (lVarsVal \<sigma>)((Fname, Vname) := lVarsVal \<sigma> (Fname, Vname')),
           inputs   := DeclIni_lVarVar Fname Vname Vname'# inputs \<sigma>\<rparr>)"

definition declNone_lVar :: 
  "string \<Rightarrow>string \<Rightarrow>  'a statements" where 
  "declNone_lVar Fname Vname  = 
    (\<lambda>\<sigma>. \<sigma>\<lparr>lVars    := (Fname, Vname)# lVars \<sigma>,
           gfunLVars:= (gfunLVars \<sigma>) (Fname:=  Some (Vname#the (gfunLVars \<sigma> Fname))),
           lVarsVal := lVarsVal \<sigma>((Fname, Vname) \<mapsto> None),
           inputs   := DeclNone_lVar Fname Vname# inputs \<sigma>\<rparr>)"

subsection \<open>The return, exit and break statements\<close>

definition return_c :: 
  "string \<Rightarrow>string \<Rightarrow>  'a statements" where 
  "return_c Fname Vname  = undefined"

definition exit_c :: 
  "string \<Rightarrow>string \<Rightarrow>  'a statements" where 
  "exit_c Fname Vname  = undefined"

definition break_c :: 
  "string \<Rightarrow>string \<Rightarrow>  'a statements" where 
  "break_c Fname Vname  = undefined"

subsection \<open>Assignment statement\<close>

definition assign_c :: 
  "string \<Rightarrow>string \<Rightarrow>  'a statements" where 
  "assign_c Fname Vname  = undefined"

subsection \<open>Conditional statement\<close>

definition if_c :: 
  "string \<Rightarrow>string \<Rightarrow>  'a statements" where 
  "if_c Fname Vname  = undefined"

subsection \<open>While statement\<close>

definition while :: 
  "string \<Rightarrow>string \<Rightarrow>  'a statements" where 
  "while Fname Vname  = undefined"


subsection \<open>Case switch statement\<close>

definition case_c :: 
  "string \<Rightarrow>string \<Rightarrow>  'a statements" where 
  "case_c Fname Vname  = undefined"

text "Donc pour toutes les variables SHARED entre les deux etats sigma et sigmaPrime
      sigma gagne (La valeurs du nouveau etats egal a la valeur de sigma).
      Pour les autres cas on ne change pas la valeur de l eta 
      (la valeur du nouveau etat egal a sigmaPrime) "

end