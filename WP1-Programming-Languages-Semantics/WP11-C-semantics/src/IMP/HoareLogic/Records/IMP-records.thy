chapter {*Types and Core Definitions of C*}
theory IMP

imports Main
          "$ISABELLE_HOME/src/HOL/Library/Numeral_Type"
             "../../HOL-TestGen-2016/src/Testing"
                                                
begin 

section \<open>IMP state\<close>

text \<open>In IMP language the state is a partial map going from locations, \ie, variables names
      to their values. We assume that we can only have HOL integers for IMP variables.\<close>
(*TODO Yakoub:  adapt IMP arithmetic expressions to other C arithmetic  expressions, 
  \eg,IMP does not support int32, float, double, signed int, unsigned int etc.
  TASK Yakoub: add the above types on a top of Isabelle/HOL + add their algebraic rules etc.*)

type_synonym state = "string \<Rightarrow> int option"

section \<open>IMP expressions\<close>

subsection \<open>Arithmetic expressions\<close>
text \<open>In shallow embedding, since the arithmetic expressions already exist on top of HOL.
      Since arithmetic operations are overloaded on HOL, \ie, they can instantiated for different
      types, so   
      we don't need to explicitly model their syntax.\<close>

subsubsection\<open>Aexp configuration\<close>

text\<open>For each type of expressions supported by the language, we need a \emph{configuration}.
     A configuration is a partial function that takes an expression and a state and returns
     an evaluation of the expression in that state. For abbreviation purposes,
     we first create a type synonym for each expression's configuration,
     and then implement a semantics for the evaluation function based on that type.\<close>

type_synonym Aconfig = "int \<times> state \<Rightarrow> int option"

fun Aeval ::"Aconfig"
where 
"Aeval (n, \<sigma>) =   Some (id n)"

type_synonym Sconfig = "string \<times> state \<Rightarrow> int option"

fun Seval ::"Sconfig"
where "Seval (s, \<sigma>) =  \<sigma> s"

lemma sums_Eval:
  assumes 1:"Aeval (a0, \<sigma>) = Some n0"
  and     2:"Aeval (a1, \<sigma>) = Some n1"
  and     3: "n = n0 + n1"
  shows"Aeval (a0 + a1, \<sigma>) = Some n"
  using assms
  by auto

lemma minus_Eval:
  assumes 1:"Aeval (a0, \<sigma>) = Some n0"
  and     2:"Aeval (a1, \<sigma>) = Some n1"
  and     3: "n = n0 - n1"
  shows"Aeval (a0 - a1, \<sigma>) = Some n"
  using assms
  by auto

lemma multi_Eval:
  assumes 1:"Aeval (a0, \<sigma>) = Some n0"
  and     2:"Aeval (a1, \<sigma>) = Some n1"
  and     3: "n = n0 * n1"
  shows"Aeval (a0 * a1, \<sigma>) = Some n"
  using assms
  by auto

text\<open>All the rules above are used to simplify .\<close>
lemma "Aeval (a0, \<sigma>) = Some a0"
 by auto

subsection\<open>IMP boolean expressions\<close>

text\<open>Since we opt for shallow embedding, and since the type bool already exists on a top 
     of HOL we don't need to model the syntax for bool expressions.\<close>

subsubsection\<open>Bexp configuration\<close>

type_synonym  Bconfig = "bool \<times> state \<Rightarrow> bool"

fun Beval ::"Bconfig"
where 
 "Beval (True, \<sigma>) = True"
|"Beval (False, \<sigma>) = False"

lemma equ_Eval:
  assumes 1: "Aeval (a0, \<sigma>) = Some n0"
  and     2: "Aeval (a1, \<sigma>) = Some n1"
  and     3: "n0 = n1"
  shows      "Beval (a0 = a1, \<sigma>)"
  using assms
  by auto

lemma equ_EvalN:
  assumes 1: "Aeval (a0, \<sigma>) = Some n0"
  and     2: "Aeval (a1, \<sigma>) = Some n1"
  and     3: "n0 \<noteq> n1"
  shows      "\<not> Beval (a0 = a1, \<sigma>)"
  using assms
  by auto

lemma lessEqu_Eval:
  assumes 1: "Aeval (a0, \<sigma>) = Some n0"
  and     2: "Aeval (a1, \<sigma>) = Some n1"
  and     3: "n0 \<le> n1"
  shows      "Beval (a0 \<le> a1, \<sigma>)"
  using assms
  by auto

lemma lessEqu_EvalN:
  assumes 1: "Aeval (a0, \<sigma>) = Some n0"
  and     2: "Aeval (a1, \<sigma>) = Some n1"
  and     3: "\<not>(n0 \<le> n1)"
  shows      "\<not> Beval (a0 \<le> a1, \<sigma>)"
  using assms
  by auto

lemma not_Eval:
  assumes 1: "b"
  shows    "\<not> Beval (\<not>b, \<sigma>)"
  using assms
  by auto

lemma not_EvalN:
  assumes 1: "\<not>b"
  shows    "Beval (\<not>b, \<sigma>)"
  using assms
  by auto

lemma and_Eval:
  assumes 1: "Beval (b0, \<sigma>) = t0"
  and     2: "Beval (b1, \<sigma>) = t1"
  and     3: "t0"
  and     4: "t1"
  shows    "Beval (b0 \<and> b1, \<sigma>)"
  using assms
proof -
  have f1: "Beval (b0, \<sigma>)"
    by (metis "1" "3") 
  have f2: "Beval (b1, \<sigma>)"
    by (metis "2" "4") 
  have "Beval (b0 \<and> b1, \<sigma>) \<or> \<not> b0 \<or> \<not> b1"
    by fastforce
  then show ?thesis
    using f2 f1 by fastforce
qed

lemma and_EvalN1:
  assumes 1: "Beval (b0, \<sigma>) = t0"
  and     2: "Beval (b1, \<sigma>) = t1"
  and     3: "\<not>t0"
  shows    "\<not> Beval (b0 \<and> b1, \<sigma>)"
  using assms
  by (metis (full_types) Beval.simps(2))

lemma and_EvalN2:
  assumes 1: "Beval (b0, \<sigma>) = t0"
  and     2: "Beval (b1, \<sigma>) = t1"
  and     3: "t0"
  and     4: "\<not>t1"
  shows    "\<not>Beval (b0 \<and> b1, \<sigma>)"
  using assms
  by (metis (full_types) Beval.simps(2))

lemma or_Eval:
  assumes 1: "Beval (b0, \<sigma>) = t0"
  and     2: "Beval (b1, \<sigma>) = t1"
  and     3: "t0"
  and     4: "t1"
  shows    "Beval (b0 \<or> b1, \<sigma>)"
  using assms
proof -
  have "(b0 \<or> b1) \<or> Beval (b0 \<or> b1, \<sigma>)"
    using "2" "4" by auto 
  then show ?thesis
    using Beval.simps(1) by presburger
qed

lemma or_EvalN1:
  assumes 1: "Beval (b0, \<sigma>) = t0"
  and     2: "Beval (b1, \<sigma>) = t1"
  and     3: "t0"
  shows    "Beval (b0 \<or> b1, \<sigma>)"
  using assms
proof -
  have "(b0 \<or> b1) \<or> Beval (b0 \<or> b1, \<sigma>)"
    using "1" "3" by auto 
  then show ?thesis
    using Beval.simps(1) by presburger
qed

lemma or_EvalN2:
  assumes 1: "Beval (b0, \<sigma>) = t0"
  and     2: "Beval (b1, \<sigma>) = t1"
  and     3: "t1"
  shows    "Beval (b0 \<or> b1, \<sigma>)"
  using assms
proof -
  have "(b0 \<or> b1) \<or> Beval (b0 \<or> b1, \<sigma>)"
    using "2" "3" by auto 
  then show ?thesis
    using Beval.simps(1) by presburger
qed

lemma "Beval (b, \<sigma>) =  b"
  using id_apply 
  by fastforce
 
subsection\<open>IMP commands expressions\<close>
text\<open>Commands are expressions that take as inputs other IMP expressions and a state and returns
     a new state. The new updated state will contain new evaluations for the locations.
     The commands are the only way to give a semantics to a location.\<close>

datatype Com = skip |assign "string" "int"| "if" "bool" "Com" "Com" | 
               seq "Com" "Com" | while "bool" "Com"

subsection\<open>IMP Semantics\<close>

type_synonym Comconfig = "Com \<times> state \<Rightarrow> state"

fun unfold :: "nat \<times> Com \<Rightarrow> Com"
where
  uf_skip : "unfold(n, skip)     = skip"
| uf_ass  : "unfold(n, assign a  E)  = (assign a  E)"
| uf_If   : "unfold(n, Com.if b  c1  c2) = 
             Com.if b  (unfold(n, c1))  (unfold(n, c2))"
| uf_while: "unfold(n, while b  c ) = 
            (if 0 < n 
             then Com.if b  (seq (unfold(n,c)) (unfold(n- 1, while b  c )))  skip
             else while b  (unfold(0, c)) )"


inductive Ceval ::"Com \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" ("\<langle>_,_\<rangle> \<Rightarrow> _"  [20,98] 89)
where 
 Skip:"\<langle>skip, \<sigma> \<rangle> \<Rightarrow> \<sigma>"|
 Assign:"\<langle>assign LOC a, \<sigma> \<rangle> \<Rightarrow> \<sigma>(LOC := (Some a))"|
 IfT:"b \<Longrightarrow>  \<langle>c0 , \<sigma> \<rangle> \<Rightarrow> \<sigma>' \<Longrightarrow> \<langle>Com.if b c0 c1, \<sigma> \<rangle> \<Rightarrow> \<sigma>'"|
 IfF:"\<not> b \<Longrightarrow>  \<langle>c1 , \<sigma> \<rangle> \<Rightarrow> \<sigma>' \<Longrightarrow> \<langle>Com.if b c0 c1, \<sigma> \<rangle> \<Rightarrow> \<sigma>'"|
 WhileT:"b \<Longrightarrow>  \<langle>c , \<sigma> \<rangle> \<Rightarrow> \<sigma>'  \<Longrightarrow> \<langle>while b c, \<sigma>' \<rangle> \<Rightarrow> \<sigma>''\<Longrightarrow> \<langle>while b c, \<sigma> \<rangle> \<Rightarrow> \<sigma>''"|
 WhileF:"\<not> b \<Longrightarrow>  \<langle>while b c, \<sigma> \<rangle> \<Rightarrow> \<sigma>"|
 Seq:" \<langle>c0, \<sigma> \<rangle> \<Rightarrow> \<sigma>' \<Longrightarrow>  \<langle>c1, \<sigma>' \<rangle> \<Rightarrow> \<sigma>'' \<Longrightarrow>\<langle>seq c0 c1, \<sigma> \<rangle> \<Rightarrow> \<sigma>''"

inductive_cases Ceval_elim [cases set]:
"\<langle>skip, \<sigma> \<rangle> \<Rightarrow> \<sigma>'" "\<langle>assign LOC a, \<sigma> \<rangle> \<Rightarrow> \<sigma>'" "\<langle>Com.if b c0 c1, \<sigma> \<rangle> \<Rightarrow> \<sigma>'"
"\<langle>while b c, \<sigma> \<rangle> \<Rightarrow> \<sigma>'" "\<langle>seq c0 c1, \<sigma> \<rangle> \<Rightarrow> \<sigma>'"

thm Ceval_elim

fun Ceval1 ::"Comconfig"
where 
 "Ceval1 (skip, \<sigma>) = \<sigma>"
|"Ceval1 (assign LOC a, \<sigma>) = fun_upd \<sigma> LOC (Some a)"
|"Ceval1 (Com.if b c0 c1, \<sigma>) = (if Beval (b, \<sigma>) then Ceval1 (c0, \<sigma>) else Ceval1 (c1, \<sigma>))"
|"Ceval11 (while b c0, \<sigma>) =(if Beval (b, \<sigma>) then Ceval1 (while b c0, Ceval1 (c0, \<sigma>))  else \<sigma>)"


text {*@{const Ceval}}*}


lemma skip_Eval:"\<langle>skip, \<sigma> \<rangle> \<Rightarrow> \<sigma>"
  using Skip
  by simp

lemma assign_Eval:
  assumes 1:"Aeval (a, \<sigma>) = m"
  shows  "\<langle>assign LOC a, \<sigma> \<rangle> \<Rightarrow> \<sigma>(LOC :=  m)"
  using 1 Assign 
  by auto

lemma if_Eval1:
  assumes 1:"b"
  and     2:" \<langle>c0 , \<sigma> \<rangle> \<Rightarrow> \<sigma>'"
  shows  "\<langle>Com.if b c0 c1, \<sigma> \<rangle> \<Rightarrow> \<sigma>'"
  using 1 2 IfT
  by simp

lemma if_Eval2:
  assumes 1:"\<not>b"
  and     2:" \<langle>c1 , \<sigma> \<rangle> \<Rightarrow> \<sigma>'"
  shows  "\<langle>Com.if b c0 c1, \<sigma> \<rangle> \<Rightarrow> \<sigma>'"
  using 1 2 IfF
  by simp

lemma while_Eval1:
  assumes 1:"\<not>b"
  shows  "\<langle>while b c, \<sigma> \<rangle> \<Rightarrow> \<sigma>"
  using 1 WhileF
  by simp

lemma while_Eval2:
  assumes 1:"b"
  and     2:"\<langle>c , \<sigma> \<rangle> \<Rightarrow> \<sigma>'"
  and     3: "\<langle>while b c, \<sigma>' \<rangle> \<Rightarrow> \<sigma>''"
  shows  "\<langle>while b c, \<sigma>\<rangle> \<Rightarrow> \<sigma>''"
  using 1 2 3 WhileT
  by simp

section\<open>Conclusion\<close>
text\<open>Shallow embedding allows for the reuse of the existing HOL rules for the evaluation of expressions.
     In IMP, commands can update the state by updating location's values.
     The role of an operational semantics is to reduce commands to expressions and then reduce
     expressions to their evaluation.
     A syntax-directed specification with operational semantics allows for a powerful 
     expressions and powerful evaluation process\<close>


section\<open>Test Generation for IMP\<close>
text\<open>The IMP semantics is implemented using an inductive predicate which is not suited for 
     test generation. In order to generate test for IMP language two solutions are possible:
     \begin{itemize}
       \item option 1: Proposing another semantics for IMP which is suited for test generation 
             and proving that it is equivalent to the actual non testable semantics.
       \item  option 2: 
              Developing symbolic execution rules that helps in unfolding the IMP semantics
     \end {itemize}
Option 1 is time consuming. Option 2 is better.
\<close>

subsection \<open>Example\<close>
text\<open>In the following Example we show why the semantic of IMP expressed with and
     inductive predicate is not suited for test case generation\<close>

declare [[goals_limit = 100]]
consts PUT:: "Com \<Rightarrow> (char list \<Rightarrow> int option) \<Rightarrow> char list \<Rightarrow> int option"
lemma Example1:
shows "\<langle>c , \<sigma> \<rangle> \<Rightarrow> PUT c \<sigma> "
apply (gen_test_cases 0 3 PUT auto elim!: Ceval_elim)
mk_test_suite "Example1_result"
thm Example1_result.test_thm
find_theorems "( _ \<Longrightarrow>  _) \<Longrightarrow> ( _ \<Longrightarrow> _) \<Longrightarrow> _"
thm iffI
thm conjI

thm disjI1
ML {*
(*fun gen_test_data name context =
    let val ctxt = Context.proof_of context
        val te = TestEnv.get_testenv ctxt
        val bound = Config.get ctxt TestEnv.type_range_bound
        val candTs= #type_candicates(TestEnv.rep_testenv te)
        val type_grounds = groundT_thm context bound candTs
        val testthm  = (the(Symtab.lookup(TestEnv.get_test_thm_tab te)name)
                            handle Option.Option => error("No test theorem: "^name^" available!"))
        val atdata = (the(Symtab.lookup(TestEnv.get_absdata_tab te)name)
                      handle Option.Option => [])
        val jdmts = map (solve_all ctxt atdata) (type_grounds testthm)
        val te1 = TestEnv.test_thm_inst_tab_update  (Symtab.update(name,jdmts)(TestEnv.get_test_thm_inst_tab te)) te
        val prems = List.concat (map Thm.prems_of jdmts)
        val data = map (Thm.cterm_of ctxt) (filter is_test_data prems)
        val te2 = TestEnv.set_test_data_tab (name,data) te1
        val hyps = map (Thm.cterm_of ctxt) (filter is_thyp prems)
        val te3 = TestEnv.set_test_thyps_tab (name,hyps) te2
        val pos = map (Thm.cterm_of ctxt) (filter is_po prems)
        val te4 = TestEnv.set_unsolved_PO_tab (name,pos) te3

        val t = LogThy.get_td_delta ()
        val _ = writeln (String.concat ["Test theorem (gen_test_data) '",name,"': ",
					                               Int.toString (List.length data)," test cases in ",
                                         Time.toString t, " seconds"])
         val _ = if not (null pos) 
                 then  writeln (String.concat ["Warning: There were ", Int.toString (List.length pos) , " unsolved POs."])
                 else  ()
         val _ = LogThy.append (String.concat [
                              Context.theory_name (Proof_Context.theory_of ctxt), ", " ,name, ", ",
					                     "test data, " ,Int.toString (List.length data),
                              ", " ,Time.toString t,"\n"])
			   
    in TestEnv.map_data (K te4) context end;

fun select_goals pred thy name = let
    val te = TestEnv.get_testenv_global thy
in
    maps (convert_goals_to_metahyps pred) 
             (the(Symtab.lookup(TestEnv.get_test_thm_inst_tab te)name)
              handle Option.Option => error("No data statement: "^name^" available!"))
end
*)
(*val thy = Context.theory_map (TestGen.gen_test_data "Example1_result") @{theory}*)

(* Option 1: check TestGen.gen_test_data*) 

val option1 = TestGen.gen_test_data "Example1_result" 

val option12 = (Context.Theory @{theory}) (*when using option12 as argument for TestGen.gen_test_data we trigger the bug*)  

(* There is 3 functions that use option12 in TestGen.gen_test_data, 
   the bug is coming from one of these function:
   option131  Context.proof_of is behaving correctly
   option132 groundT_thm we need to check
   option133 TestEnv.map_data

*)

fun groundT_thm context bound candTs thm =
    let val ctxt  = Context.proof_of context
        val thy   = Proof_Context.theory_of ctxt
        val thm   = Thm.varifyT_global thm
        val tvars = Term.add_tvars (list_comb(Thm.concl_of thm,Thm.prems_of thm)) []
        fun ctyp_of_sort x so t = if Sign.of_sort thy (t,so)
                                  then (SOME((x,so), Thm.ctyp_of ctxt t)
                                       handle _ => NONE)  (* FIXME avoid handle _ *)
                                  else NONE 
        fun prodS [] _ = []
           |prodS (a::R) B =  (map(fn x => a::x) B) @ (prodS R B)

        fun compute_instsT [] = [[]]
           |compute_instsT ((x,so)::R) = prodS (List.mapPartial (ctyp_of_sort x so) candTs)
                                               (compute_instsT R)
    in
        map (fn x => Drule.instantiate_normalize (x,[]) thm)
            (Library.take bound (compute_instsT tvars))
    end;

 val ctxt = Context.proof_of option12
 val te = TestEnv.get_testenv ctxt
 val bound = Config.get ctxt TestEnv.type_range_bound
 val candTs= #type_candicates(TestEnv.rep_testenv te)
 val context = option12
 
 val type_grounds = groundT_thm context bound candTs
        val testthm  = (the(Symtab.lookup(TestEnv.get_test_thm_tab te) "Example1_result")
                            handle Option.Option => error("No test theorem: "^"Example1_result"^" available!"))
        val atdata = (the(Symtab.lookup(TestEnv.get_absdata_tab te) "Example1_result")
                      handle Option.Option => [])




val testthm = @{thm Example1_result.test_thm}

val option132= groundT_thm option12 bound candTs testthm
(* There is 3 functions that use option12 in TestGen.gen_test_data, 
   the bug is coming from one of these function:
   option131  Context.proof_of is behaving correctly
   option132 groundT_thm  is behaving correctly
   option133  jdmts   we need to check

*)

fun is_po (Const (@{const_name Trueprop},_) $ (Const (@{const_name PO},_) $ _)) = true
   |is_po _   = false;

fun PARALLEL_TRYSOLVE_POs ctxt test_solve_tac st =
  let
    val pon = Config.get ctxt TestEnv.pon
    fun filter_pos filter S =
        let fun  h _ _ [] = []
               | h f n (a::S) = if f a then (n,a)::(h f (n+1) S) else (h f (n+1) S)
            fun  h_pon _ _ _ [] = []
               | h_pon f n k (a::S) = if f a then (if k = pon then (n,a):: nil 
                                                              else (h_pon f (n+1) (k+1) S)) 
                                             else (h_pon f (n+1) k S)
        in if pon = 0 then h filter 1 S else h_pon filter 1 1 S end;
    fun try_solve ct = ((Option.map (Goal.finish ctxt)) o
                         (SINGLE (test_solve_tac ctxt))) 
                        (Goal.init ct);
    val goals = Drule.strip_imp_prems (Thm.cprop_of st);
    val po_trms = (filter_pos (is_po o Thm.term_of) goals);
    val jdmts =  Par_List.map (fn(n,ct) => (n, try_solve ct)) po_trms
    
  in Seq.succeed(foldr (fn ((k, SOME a),thm) => (a RSN (k, thm))
                          |((_, NONE),thm) => thm) st jdmts)
  end

fun EXEC ctxt tac str = EVERY[if Config.get ctxt TestGen.profiling 
                                 then Clocks.start_clock_tac str 
                                 else all_tac,
                              if Config.get ctxt TestGen.trace 
                                 then print_tac ctxt ("\n:"^str^"\n") 
                                 else all_tac,
                              tac,
	                            if Config.get ctxt TestGen.profiling 
                                 then Clocks.stop_clock_tac str 
                                 else all_tac]

fun EXEC' ctxt tac str n = EXEC ctxt (tac n) str

fun PRINT_THM ctxt no = 
               (fn state => (if Config.get ctxt TestGen.trace 
                             then let val prem = Logic.nth_prem(no, Thm.prop_of state)
                                      val str  = (Pretty.string_of o (Syntax.pretty_term ctxt)) prem
                                  in  print_tac ctxt ("\n goal "^Int.toString(no)^"::"^str^"\n") end
                             else all_tac) state)

fun test_solve_tac ctxt atdata = 
    let val thy = Proof_Context.theory_of ctxt
        val remove_po = EqSubst.eqsubst_tac ctxt [0] [@{thm PO_def}]
        val total_iterations = Config.get ctxt TestEnv.iterations
        val max_simple_iterations = 50
        val simple_iterations  = Int.min(total_iterations, max_simple_iterations)
        val further_iterations = Int.max(total_iterations - max_simple_iterations,0)
    in
              remove_po 
        THEN' PRINT_THM ctxt 
        THEN' (FIRST'[EXEC' ctxt (TestGen.abs_data_tac ctxt atdata) "abs_data",
                      EXEC' ctxt (RandomBackend.random_inst_tac ctxt simple_iterations) "random_inst",
                      EXEC' ctxt (QuickCheckBackend.quickcheck_tac ctxt further_iterations) "quickcheck",
                      EXEC' ctxt (SMTBackend.testgen_smt_tac ctxt) "smt"])
    end

fun is_solved n thm = 
    let  fun is_unsolved_po i =  not (null (inter (op =) (BackendUtils.premvars n thm) (BackendUtils.premvars i thm))) 
                                 andalso i <> n
    in    not (exists is_unsolved_po (1 upto (Thm.nprems_of thm)))
    end

fun finalize_test_tac ctxt n thm = let
in
    (COND (is_solved n) (RandomBackend.single_rand_inst_tac ctxt (BackendUtils.premvars n thm)) all_tac) thm
end

fun thm |$> tac =
    case Seq.pull (tac thm) of
         SOME (m,_) => m
        |_ => error"|$> : TACTIC FAILED"

fun solve_all ctxt atdata state =
   let (* adding a let expression.. in order to check if all free vars were instatiated by smt.. 
          if true then error code else solve_all*)
    val PARALLEL_TRYSOLVE = PARALLEL_TRYSOLVE_POs ctxt (fn ctxt => test_solve_tac ctxt atdata 1) state
                             
    val term =  PARALLEL_TRYSOLVE |>  Seq.list_of |> 
               (List.map Thm.prop_of) |> HOLogic.mk_list @{typ "term"}
    val use_smt = Config.get ctxt TestEnv.use_smt;
in
   if (use_smt andalso (Term.exists_subterm (Term.is_Var) term))
   then  error("One or more free variables were not instantiated by the solver!")
          
   else  state |$> PARALLEL_TRYSOLVE_POs ctxt (fn ctxt => test_solve_tac ctxt atdata 1)
          |$> TestGen.ALLCASES (finalize_test_tac ctxt) (* cannot parallelize here *)

end



val res1=testthm |$> PARALLEL_TRYSOLVE_POs ctxt (fn ctxt => test_solve_tac ctxt atdata 1) 

val res2= TestGen.ALLCASES (finalize_test_tac @{context})

val fin1 = finalize_test_tac ctxt 1 @{thm HOL.notI2}

 
val sin1 = RandomBackend.single_rand_inst_tac ctxt (BackendUtils.premvars 1 @{thm iffI})  
val Cond1 =  (COND (is_solved 1) sin1 all_tac)  @{thm iffI};
val prem1 =  (BackendUtils.premvars 1 @{thm iffI}) 
val term1 = [Var (("P", 0), @{typ bool})]
val term2 = [Var (("Q", 0), @{typ bool}), Var (("P", 0), @{typ bool})]

val sin2 = RandomBackend.single_rand_inst_tac ctxt term2 (* This function is BUGUS it never works*)  
val solv1 = (is_solved 1)  @{thm iffI}

*}

ML {*
(* Investigation on the different parts of RandomBackend.single_rand_inst_tac*)

fun calc_constr_list tgt descr =
let fun DtTFree_tvar x = (Old_Datatype_Aux.dest_DtTFree x, @{sort type} )
    val sorts          = maps (fn (_,(_,s,_)) => map DtTFree_tvar s) descr
    val recTs          = Old_Datatype_Aux.get_rec_types descr;
    val newTs          = Library.take (length descr) recTs;
    val (_,(_,insts,tgt_constrs)) = hd(filter (fn (_,(n,_,_)) => n = tgt) descr)
    val T              = hd(filter (fn (Type(n,_)) => n = tgt) newTs)
    val typ_of_dtyp    = Old_Datatype_Aux.typ_of_dtyp descr
    val constr_decls   = map (fn (cname, cargs) =>
                                 Const(cname, map typ_of_dtyp cargs ---> T))
                             (tgt_constrs)
in  (map Old_Datatype_Aux.dest_DtTFree insts, constr_decls) end;

fun random_term' w n max ctxt cod_term_tab (Type(s,S)) =
(* w => the weight on the actual level, initial value 1
   n => level counter, inital value 0
   max => maximal allowed number of levels
*)
    let val thy = Proof_Context.theory_of ctxt
    in 
       (case Symtab.lookup cod_term_tab s of
         NONE   => (* default random term generator ...
                      TODO : should do also something for functions ... *)
                   (case Type(s,S) of
                      Type(@{type_name int},_) => HOLogic.mk_number HOLogic.intT (IntInf.fromInt((Random.random_range 0 20) - 10))
                    | Type(@{type_name nat},_) => HOLogic.mk_nat (IntInf.fromInt((Random.random_range 0 40)))
                    | Type(@{type_name set},_) => Const(@{const_name set},dummyT) $
                                       (random_term' w n max ctxt cod_term_tab (Type(@{type_name list},S)))
                    | Type(@{type_name fun},[T, Type(@{type_name bool}, [])]) =>
                      Const(@{const_name set}, Type(@{type_name fun}, [Type(@{type_name list}, [T]), Type(s,S)])) $
                           (random_term' w n max ctxt cod_term_tab (Type(@{type_name list},[T])))
                    | Type(@{type_name fun},[T,U]) => absdummy T (random_term' w n max ctxt cod_term_tab U)
                     | Type(_,_) => error"Josh"
                    | _     => let
                                   val descr = #descr(BNF_LFP_Compat.the_info thy [] s)

                                   val (insts,constrs) = calc_constr_list s descr

                                   val weighed_constrs = let
                                       fun ar args = (length
                                                              (filter (fn t =>
                                                                          case t of
                                                                              Old_Datatype_Aux.DtRec _ => true
                                                                            | _ => false ) args) )
                                       val constr_arity_list =  map (fn (f,args) => (f,(ar args)))
                                                                  (maps (#3 o snd) descr)
                                   in
                                       map (fn (f,a) => if a = 0 then (1,f) else (a * w,f))
                                           constr_arity_list
                                   end

                                   val  weighed_constrs = if (n >= max)
                                                          then filter (fn (w,f) => w =1) weighed_constrs
                                                          else weighed_constrs
                                   fun weight_of t = fst(hd ((filter (fn (w,ty) => ty=t)) weighed_constrs))

                                   fun frequency' xs = let
                                       val max = List.foldl Int.max 0 (map fst xs);
                                       val xs' = map (fn (x,a) => (max-x+1,a)) xs
                                   in
                                       frequency' xs'
                                   end
                                   (* the default is a random bias towards constants *)
                                   val constr = frequency' weighed_constrs
                                   val Const(h,ty) = hd (filter (fn Const(h,ty) => h = constr) constrs)
                                   val w          = weight_of h
                                   val ty_binds   = insts ~~ S
                                   fun ty_inst s = the (AList.lookup (op =) ty_binds s)
                                   val instantiated_ty = map_type_tfree ty_inst ty
                                   val const_head = Const(h,instantiated_ty)
                                   val arg_ty = binder_types instantiated_ty
                               in  list_comb(const_head,
                                             (map(random_term' w (n+1) max ctxt cod_term_tab)(arg_ty)))
                               end (* FIXME avoid handle _ *)
                               handle _=>error("Cannot generate random value for type:" ^s))
       | SOME R => R S)
       end
   |random_term' _ _ _ _ _ _ = error "Internal error in random_term: type not ground";
 

fun random_term thy cod_term_tab typ = random_term' 1 0 10000 thy cod_term_tab typ

fun random_insts ctxt cod_tab vars () = 
       map(fn(x as Var(s,t))=>
           (Thm.cterm_of ctxt x,Thm.cterm_of ctxt (random_term ctxt cod_tab t))) vars
    
val cod_tab = #cod_term_tab(TestEnv.rep_testenv te)
val to_var_index   = (fn  Var(s,t) => (s,t)) o Thm.term_of
(*val insts = map (fn(x,y)=> (to_var_index x,y)) (random_insts ctxt cod_tab vars ())*)
*}

ML {* (*Investigation on random_insts*)


val  rand1= random_insts  ctxt cod_tab term1

val rand2 = (random_term ctxt cod_tab )
                      
val rand4 = random_term' 1 0 10000 ctxt cod_tab @{typ "bool"}
*}


(*declare [[testgen_iterations=0]]
declare [[testgen_SMT]]          (* switch on Z3 *)
gen_test_data "Example1_result" 
thm Example1_result.test_thm_inst  
declare [[testgen_iterations=0]] (* switch off random-solver *)
declare [[testgen_SMT]]          (* switch on Z3 *)

declare [[smt_trace]]
declare [[testgen_pon = 4]]
declare [[testgen_smt_model]]
declare [[show_brackets]]
gen_test_data "Example1_result"*)

end