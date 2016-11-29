theory Statements
imports "../symbolic-state/SymbolicStateInst"

begin
section \<open>C-statements\<close>
subsection \<open>Generic type\<close>
text \<open>Statements are functions that update the state. Since we opt for shallow embedding,
      statements are represented by constant definitions, well founded recursion etc.
      A statement takes \emph{arguments} and a state, and it returns an updated state 
      The generic type of statement is:  
     \<close>

type_synonym  'a statements = 
             "'a stateInst \<Rightarrow> 'a stateInst"

definition declIni_gVar :: 
  "string \<Rightarrow> vals \<Rightarrow>  'a statements" where
  "declIni_gVar name val =  
    (\<lambda>\<sigma>. if (name, None) \<notin> set (allNames \<sigma>) 
         then \<sigma>\<lparr>allNames   := (name, None)#allNames \<sigma>,
                globalVars := name #globalVars \<sigma>,
                values     := values \<sigma>((name, None) \<mapsto> Some val),
                inputs     := DeclIni_gVar name val #inputs \<sigma>\<rparr>
         else \<sigma>\<lparr>bugs:= SameGlobalVarName#bugs \<sigma>\<rparr>)"


definition declNone_gVar :: 
  "string \<Rightarrow> 'a statements" where 
  "declNone_gVar name = 
    (\<lambda>\<sigma>. if (name, None) \<notin> set (allNames \<sigma>) 
         then \<sigma>\<lparr>allNames   := (name, None)#allNames \<sigma>,
                globalVars := name #globalVars \<sigma>,
                values     := values \<sigma>((name, None) \<mapsto> None),
                inputs     := DeclNone_gVar name #inputs \<sigma>\<rparr>
         else \<sigma>\<lparr>bugs:= SameGlobalVarName#bugs \<sigma>\<rparr>)"

term "the(localVars \<sigma> Fname) "
(*TODO RE-Check definition*)
definition declArgs_fun :: 
  "string \<Rightarrow>string list \<Rightarrow> 'a stateInst \<Rightarrow>  'a statements" where
  "declArgs_fun Fname Vnames \<sigma> = 
   (\<lambda>\<sigma>'. if (Fname, Some Vnames)\<notin> set (allNames \<sigma>)
         then \<sigma>'\<lparr>allNames     := ((Fname, Some Vnames)#allNames \<sigma>'),
                 values       := (values \<sigma>')((Fname, Some Vnames) := values \<sigma> (Fname, Some Vnames)),
                 localVars    := (localVars \<sigma>') (Fname:=  Some Vnames),
                 inputs       := (inputs \<sigma>')@(inputs \<sigma>),
                 observations := (observations \<sigma>')((Fname, Some Vnames) := 
                                                   observations \<sigma> (Fname, Some Vnames)),
                 bugs         := (bugs \<sigma>)@(bugs \<sigma>')\<rparr>
         else \<sigma>\<lparr>bugs:= SameFunName#bugs \<sigma>\<rparr>)"

definition declIni_lVar :: 
  "string \<Rightarrow>string \<Rightarrow> vals \<Rightarrow> 'a statements" where
  "declIni_lVar Fname Vname val = 
    (\<lambda>\<sigma>. if (Fname, Some (Vname#get_locals \<sigma>)) \<notin> set (varNames \<sigma>)
         then \<sigma>\<lparr>varNames := (Fname, Some (Vname#get_locals \<sigma>))#varNames \<sigma>,
                values := values \<sigma>((Fname, Some [Vname]) \<mapsto> Some val)\<rparr>
         else \<sigma>\<lparr>bugs   := SameLocalVarName#bugs \<sigma>\<rparr>)"

definition declNone_localVar :: 
  "'name \<Rightarrow>'name \<Rightarrow> 'val \<Rightarrow> ('name, 'val, 'inputs, 'obs, 'bugs) statements" where 
  "declNone_localVar Fname Vname val = (\<lambda>\<sigma>. \<sigma>\<lparr>varNames := (Fname, None)#varNames \<sigma>,
                                              values := values \<sigma>((Fname, Some [Vname]) \<mapsto> None)\<rparr>)"


term "(\<lambda>Vnames'. if (Fname, Vnames') = (Fname, Vnames)  then values \<sigma> (Fname, Vnames) 
       else values \<sigma>' (Fname, Vnames'))"
term"if map snd (varNames \<sigma>') =  map snd ((Fname, Vnames)#varNames \<sigma>) then values \<sigma> else 
     values \<sigma>'"
text "Donc pour toutes les variables SHARED entre les deux etats sigma et sigmaPrime
      sigma gagne (La valeurs du nouveau etats egal a la valeur de sigma).
      Pour les autres cas on ne change pas la valeur de l eta 
      (la valeur du nouveau etat egal a sigmaPrime) "
term "(\<lambda>Vname'. case Vname' of (gVar', None) \<Rightarrow> 
                  if gVar' \<in> set (fold (\<lambda>xs ys. the(snd xs)@ys) (varNames \<sigma>) []) 
                  then values \<sigma> Vname' 
                  else values \<sigma>' (gVar', None)
                |(Fname', Vnames') \<Rightarrow>
                   if (Fname' =  Fname) \<and> (Vnames' =  Vnames) then values \<sigma> (Fname, lvars) 
                   else values \<sigma>' Vname')"

term "(varNames \<sigma>)"

term"fold (\<lambda>xs ys. the(snd xs)@ys) (varNames \<sigma>) []"
end