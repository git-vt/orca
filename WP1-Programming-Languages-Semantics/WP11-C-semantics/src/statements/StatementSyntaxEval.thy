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
Purge:"synBugs \<sigma> \<noteq> []\<Longrightarrow> \<langle>prog, \<sigma>\<rangle> \<Rightarrow>  \<sigma>"|
(*statements for Global Constant declaration *)
DeclIniGCons: "name \<notin> set(gConsts \<sigma>) \<Longrightarrow>  synBugs \<sigma> = [] \<Longrightarrow> 
               \<langle>declIni_gCons name val, \<sigma>\<rangle> \<Rightarrow> ((declIni_gCons name val) \<sigma>)"|
DeclIniGCons_Bug: "name \<in> set(gConsts \<sigma>) \<Longrightarrow>  synBugs \<sigma> = [] \<Longrightarrow>
                   \<langle>declIni_gCons name val, \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>synBugs := SameGlobalConsName name#synBugs \<sigma>\<rparr>"|
   (*declIni_gConsCons always provides a syntactic bug state*)
DeclIniGConsCons_Bug1: 
  "name' \<in> set(gConsts \<sigma>) \<Longrightarrow> name \<in> set(gConsts \<sigma>) \<Longrightarrow>
   synBugs \<sigma> = [] \<Longrightarrow>
   \<langle>declIni_gConsCons name name', \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>synBugs := InitIsNotConst name'#synBugs \<sigma>\<rparr>"|
DeclIniGConsCons_Bug2: 
  "name' \<in> set(gConsts \<sigma>) \<Longrightarrow> name \<notin> set(gConsts \<sigma>) \<Longrightarrow>
   synBugs \<sigma> = [] \<Longrightarrow>
   \<langle>declIni_gConsCons name name', \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>synBugs := InitIsNotConst name'#synBugs \<sigma>\<rparr>"|
DeclIniGConsCons_Bug3: 
  "name' \<notin> set(gConsts \<sigma>) \<Longrightarrow>  synBugs \<sigma> = [] \<Longrightarrow>
   \<langle>declIni_gConsCons name name', \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>synBugs := UndeclGConstName name'#synBugs \<sigma>\<rparr>"|
(*statements for Local Constant declaration *)
DeclIniLCons: "(Fname, Cname) \<notin> set(lConsts \<sigma>) \<Longrightarrow>  synBugs \<sigma> = [] \<Longrightarrow>
               \<langle>declIni_lCons Fname Cname val, \<sigma>\<rangle> \<Rightarrow> ((declIni_gCons name val) \<sigma>)"|
DeclIniLCons_Bug: "(Fname, Cname) \<in> set(lConsts \<sigma>) \<Longrightarrow>  synBugs \<sigma> = [] \<Longrightarrow>
                   \<langle>declIni_lCons Fname Cname val, \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>synBugs := SamelocalConsName Cname#synBugs \<sigma>\<rparr>"|
DeclIniLConsCons_Bug1: 
  "(Fname, Cname') \<in> set(lConsts \<sigma>) \<Longrightarrow> (Fname, Cname) \<in> set(lConsts \<sigma>) \<Longrightarrow> synBugs \<sigma> = [] \<Longrightarrow>
   \<langle>declIni_lConsCons Fname Cname Cname', \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>synBugs := SamelocalConsName name#synBugs \<sigma>\<rparr>"|
DeclIniLConsCons_Bug2: 
  "(Fname, Cname') \<notin> set(lConsts \<sigma>) \<Longrightarrow> synBugs \<sigma> = [] \<Longrightarrow>
   \<langle>declIni_lConsCons Fname name name', \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>synBugs := UndeclLConstName name'#synBugs \<sigma>\<rparr>"|
DeclIniLConsCons_Bug3: 
  " Cname' \<notin> set(gConsts \<sigma>) \<Longrightarrow> synBugs \<sigma> = [] \<Longrightarrow>
   \<langle>declIni_lConsCons Fname name name', \<sigma>\<rangle> \<Rightarrow> \<sigma>\<lparr>synBugs := UndeclGConstName name'#synBugs \<sigma>\<rparr>"|
DeclIniLConsCons1: 
  "(Fname, Cname') \<in> set(lConsts \<sigma>) \<Longrightarrow> (Fname, Cname) \<notin> set(lConsts \<sigma>) \<Longrightarrow> synBugs \<sigma> = [] \<Longrightarrow>
   \<langle>declIni_lConsCons Fname name name', \<sigma>\<rangle> \<Rightarrow> declIni_lConsCons Fname name name' \<sigma>"|
DeclIniLConsCons2: 
  "Cname' \<in> set(gConsts \<sigma>) \<Longrightarrow> (Fname, Cname) \<notin> set(lConsts \<sigma>) \<Longrightarrow> synBugs \<sigma> = [] \<Longrightarrow>
   \<langle>declIni_lConsCons Fname name name', \<sigma>\<rangle> \<Rightarrow> declIni_lConsCons Fname name name' \<sigma>"
find_theorems name: is_SynEval.simps
end