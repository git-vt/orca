theory Statements
imports "../symbolic-state/SymbolicStateInst"

begin
section \<open>C-statements\<close>
subsection \<open>Generic type\<close>
text \<open>Statements are functions that update the state. Since we opt for shallow embedding,
      statements are represented by constant definitions, function definitions with 
      well founded recursions etc. A statement takes \emph{arguments} and a state, 
      and it returns an updated state. The generic type of statements is:\<close>

type_synonym  'a statements = 
             "'a stateInst \<Rightarrow> 'a stateInst"

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
                    \item Since global variables name is specified by a pair @{term "(name, None)"}
                          we update the field @{term "allNames"} of the record 
                          by pre-pending the global variable name.
                    \item The field @{term "globalVars"} contains a list of the first element
                          of @{value "fst(name, None)"} representing the name of a global variable.
                    \item a state @{term "\<sigma>"} of type @{typ "'a stateInst"}
                 \end{itemize}
      \end{itemize}\<close>

definition declIni_gCons :: 
  "string \<Rightarrow> vals \<Rightarrow>  'a statements" where
  "declIni_gCons name val =  
    (\<lambda>\<sigma>. if name \<notin> set (gVars \<sigma>) 
         then
           \<sigma>\<lparr>gVars    := name#gVars \<sigma>,
             gVarsVal := gVarsVal \<sigma>(name \<mapsto> Some val),
             inputs   := DeclIni_gCons name (Some (Some val)) #inputs \<sigma>\<rparr>
         else \<sigma>\<lparr>bugs:= SameGlobalVarName name#bugs \<sigma>\<rparr>)"

definition declIni_gVar :: 
  "string \<Rightarrow> string \<Rightarrow>  'a statements" where
  "declIni_gVar name name' =  
    (\<lambda>\<sigma>. if name \<notin> set (gVars \<sigma>) 
         then
           if name' \<in> set (gVars \<sigma>)
           then
             \<sigma>\<lparr>gVars    := name#gVars \<sigma>,
               gVarsVal := (gVarsVal \<sigma>)(name := gVarsVal \<sigma> name'),
               inputs   := DeclIni_gVar name (gVarsVal \<sigma> name') #inputs \<sigma>\<rparr>
           else  \<sigma>\<lparr>bugs:= NoGlobalVarName name#bugs \<sigma>\<rparr>
         else \<sigma>\<lparr>bugs:= SameGlobalVarName name#bugs \<sigma>\<rparr>)"

text \<open>The constant definition @{term "declNone_gVar"} is a specification for global variables
      declaration \emph{without} value initialization.
      \begin{itemize}
         \item inputs: 
                 \begin{itemize}
                    \item  a variable name @{term "name"} of type @{typ "string"}.
                    \item  a state @{term "\<sigma>"} of type @{typ "'a stateInst"}
                  \end{itemize}
         \item output: a state @{term "\<sigma>'"} of type @{typ "'a stateInst"}
      \end{itemize}
      The of @{term "declNone_gVar"} is a good example of using our double lifting
      that characterise the return value of the field  in the 
      state. Actually when a variable is declared without an initialization the content
      of the variable is specified by @{value "Some None"}\<close>

definition declNone_gVar :: 
  "string \<Rightarrow> 'a statements" where 
  "declNone_gVar name = 
    (\<lambda>\<sigma>. if name \<notin> set (gVars \<sigma>) 
         then \<sigma>\<lparr>gVars    := name #gVars \<sigma>,
                gVarsVal := gVarsVal \<sigma>(name \<mapsto> None),
                inputs   := DeclNone_gVar name #inputs \<sigma>\<rparr>
         else \<sigma>\<lparr>bugs:= SameGlobalVarName#bugs \<sigma>\<rparr>)"

definition declArgs_fun :: 
  "string \<Rightarrow>string list \<Rightarrow> 'a stateInst \<Rightarrow>  'a statements" where
  "declArgs_fun Fname Vnames \<sigma> = 
   (\<lambda>\<sigma>'. if Fname \<notin> set (gFuns \<sigma>')
         then \<sigma>'\<lparr>gFuns    := Fname #gFuns \<sigma>',
                 gFunVal  := (gFunVal \<sigma>')((Fname, Some Vnames) := gFunVal \<sigma> (Fname, Some Vnames)),
                 gFunObs  := (gFunObs \<sigma>')(Fname := gFunObs \<sigma> Fname),
                 gfunLVars:= (gfunLVars \<sigma>') (Fname:=  Some (Vnames @ the (gfunLVars \<sigma> Fname))),
                 lVars    := lVars \<sigma> @ map (\<lambda>x. (Fname, x)) Vnames @ lVars \<sigma>',
                 inputs   := (inputs \<sigma>')@(inputs \<sigma>),
                 bugs     := (bugs \<sigma>)@(bugs \<sigma>')\<rparr>
         else \<sigma>'\<lparr>bugs:= SameFunName#bugs \<sigma> @ bugs \<sigma>'\<rparr>)"

definition declNoArgs_fun :: 
  "string \<Rightarrow> 'a stateInst \<Rightarrow>  'a statements" where
  "declNoArgs_fun Fname \<sigma> = 
   (\<lambda>\<sigma>'. if Fname \<notin> set (gFuns \<sigma>')
         then \<sigma>'\<lparr>gFuns    := Fname #gFuns \<sigma>',
                 gFunVal  := (gFunVal \<sigma>')((Fname, Some []) := gFunVal \<sigma> (Fname, Some [])),
                 gFunObs  := (gFunObs \<sigma>')(Fname := gFunObs \<sigma> Fname),
                 gfunLVars:= (gfunLVars \<sigma>') (Fname:=  Some (the (gfunLVars \<sigma> Fname))),
                 lVars    := lVars \<sigma> @ lVars \<sigma>',
                 inputs   := (inputs \<sigma>')@(inputs \<sigma>),
                 bugs     := (bugs \<sigma>)@(bugs \<sigma>')\<rparr>
         else \<sigma>'\<lparr>bugs:= SameFunName#bugs \<sigma> @ bugs \<sigma>'\<rparr>)"

definition declIni_lVar :: 
  "string \<Rightarrow>string \<Rightarrow> Dvals \<Rightarrow> 'a statements" where
  "declIni_lVar Fname Vname val = 
    (\<lambda>\<sigma>. if (Fname,  Vname) \<notin> set (lVars \<sigma>)
         then \<sigma>\<lparr>lVars := (Fname, Vname)# lVars \<sigma>,
                gfunLVars:= (gfunLVars \<sigma>) (Fname:=  Some (Vname#the (gfunLVars \<sigma> Fname))),
                lVarsVal := lVarsVal \<sigma>((Fname, Vname) \<mapsto> Some val),
                inputs   := DeclIni_lVar Fname Vname val# inputs \<sigma>\<rparr>
         else \<sigma>\<lparr>bugs   := SameLocalVarName#bugs \<sigma>\<rparr>)"

definition declNone_lVar :: 
  "string \<Rightarrow>string \<Rightarrow>  'a statements" where 
  "declNone_lVar Fname Vname  = 
    (\<lambda>\<sigma>. if (Fname,  Vname) \<notin> set (lVars \<sigma>)
         then \<sigma>\<lparr>lVars    := (Fname, Vname)# lVars \<sigma>,
                gfunLVars:= (gfunLVars \<sigma>) (Fname:=  Some (Vname#the (gfunLVars \<sigma> Fname))),
                lVarsVal := lVarsVal \<sigma>((Fname, Vname) \<mapsto> None),
                inputs   := DeclNone_lVar Fname Vname# inputs \<sigma>\<rparr>
         else \<sigma>\<lparr>bugs   := SameLocalVarName#bugs \<sigma>\<rparr>)"


text "Donc pour toutes les variables SHARED entre les deux etats sigma et sigmaPrime
      sigma gagne (La valeurs du nouveau etats egal a la valeur de sigma).
      Pour les autres cas on ne change pas la valeur de l eta 
      (la valeur du nouveau etat egal a sigmaPrime) "

end