theory StatementSyntaxEval
imports "StatementsUpdates"

begin
(*TODO YAKOUB: implement a configuration, that specifies C-function by the following syntax:
 (funName, localesNames)\<tturnstile>\<langle>statement, state\<rangle> \<Rightarrow> state *)
section \<open>statements Syntax evaluation\<close>
subsection \<open>Inductive predicate for syntax errors\label{subsec:statementsSynEval}\<close>
(*TODO YAKOUB: Implement symbolic execution rules for is_SynEval*)
inductive 
  is_SynEval:: "'a statements \<Rightarrow> 'a stateInst \<Rightarrow> 'a stateInst \<Rightarrow> bool" ("\<langle>_,_\<rangle> \<Rightarrow> _"  [20,98] 89)
where
(*statements for Global Constant declaration *)
DeclIniGCons: "name \<notin> set(gConsts \<sigma>) \<Longrightarrow>
               \<langle>declIni_gCons name val, \<sigma>\<rangle> \<Rightarrow> ((declIni_gCons name val) \<sigma>)"|
DeclIniGCons_Bug: "name \<in> set(gConsts \<sigma>) \<Longrightarrow>
                   \<langle>declIni_gCons name val, \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>bugs := SameConstName name#bugs \<sigma>\<rparr>"|
   (*declIni_gConsCons always provides a syntactic bug state*)
DeclIniGConsCons_Bug1: "name' \<in> set(gConsts \<sigma>) \<Longrightarrow> name \<in> set(gConsts \<sigma>) \<Longrightarrow>
                        \<langle>declIni_gConsCons name name', \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>bugs := InitIsNotConst name'#bugs \<sigma>\<rparr>"|
DeclIniGConsCons_Bug2: "name' \<in> set(gConsts \<sigma>) \<Longrightarrow> name \<notin> set(gConsts \<sigma>) \<Longrightarrow>
                        \<langle>declIni_gConsCons name name', \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>bugs := InitIsNotConst name'#bugs \<sigma>\<rparr>"|
DeclIniGConsCons_Bug3: "name' \<notin> set(gConsts \<sigma>) \<Longrightarrow>
                        \<langle>declIni_gConsCons name name', \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>bugs := UndeclGConstName name'#bugs \<sigma>\<rparr>"|

(*statements for Local Constant declaration *)
DeclIniLCons: "name \<notin> set(gConsts \<sigma>) \<Longrightarrow>
               \<langle>declIni_gCons name val, \<sigma>\<rangle> \<Rightarrow> ((declIni_gCons name val) \<sigma>)"|
DeclIniLCons_Bug: "name \<in> set(gConsts \<sigma>) \<Longrightarrow>
                   \<langle>declIni_gCons name val, \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>bugs := SameConstName name#bugs \<sigma>\<rparr>"|
DeclIniLConsCons_Bug1: "name' \<in> set(gConsts \<sigma>) \<Longrightarrow> name \<in> set(gConsts \<sigma>) \<Longrightarrow>
                        \<langle>declIni_gConsCons name name', \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>bugs := InitIsNotConst name'#bugs \<sigma>\<rparr>"|
DeclIniLConsCons_Bug2: "name' \<in> set(gConsts \<sigma>) \<Longrightarrow> name \<notin> set(gConsts \<sigma>) \<Longrightarrow>
                        \<langle>declIni_gConsCons name name', \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>bugs := InitIsNotConst name'#bugs \<sigma>\<rparr>"|
DeclIniLConsCons_Bug3: "name' \<notin> set(gConsts \<sigma>) \<Longrightarrow>
                        \<langle>declIni_gConsCons name name', \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>bugs := UndeclGConstName name'#bugs \<sigma>\<rparr>"
(*DeclIniGConsCons_Bug2: "name \<in> set(gConsts \<sigma>) \<Longrightarrow>
                        \<langle>declIni_gConsCons name name', \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>bugs := SameGConstName name#bugs \<sigma>\<rparr>"|
DeclIniGConsCons_Bug3: "name \<notin> set(gConsts \<sigma>) \<Longrightarrow> name' \<notin> set(gConsts \<sigma>) \<Longrightarrow>
                        \<langle>declIni_gConsCons name name', \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>bugs := NoGConstName name'#bugs \<sigma>\<rparr>"
*)
end