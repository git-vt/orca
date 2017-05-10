section \<open>Verification Condition Testing\<close>

theory VCG
  imports "../hoare/utp_hoare"
begin

subsection \<open>Tactics for Theorem Proving\<close>
text \<open>The tactics below are used to prove the validity of complex Hoare triples/expressions
semi-automatically in a more efficient manner than using @{method rel_auto} by itself.\<close>

subsection \<open>Using Eisbach methods\<close>
(* apparently `|` has lower precedence than `,` , so method `a, b|c` is equivalent to `(a, b)|c` *)

text \<open>Some proof subgoals require extra cleanup beyond plain simp/auto, so we need a simpset for
those.\<close>
named_theorems last_simps
declare lens_indep_sym[last_simps]
declare mod_pos_pos_trivial[last_simps]

text \<open>Some proof subgoals require theorem unfolding.\<close>
named_theorems unfolds
declare lens_indep_def[unfolds]

method assume_steps =
  rule seq_hoare_r,
  rule assume_hoare_r,
  rule skip_hoare_r

(* trying with other while loops to find the right patterns *)
method even_count declares unfolds last_simps =
  rule seq_hoare_r;
  (rule seq_hoare_r[of _ _ true])?,
  (rule assigns_hoare_r'|rule assigns_hoare_r),
  (* ? needed as it attempts application of the rule to the first subgoal as well *)
  assume_steps?;
  (rule while_invr_hoare_r)?, (* ? needed again to avoid error *)
  (rule seq_hoare_r)?;
  (rule assigns_hoare_r')?,
  (rule cond_hoare_r)?,
  (unfold unfolds)?,
  insert last_simps;
  rel_auto

method increment declares unfolds =
  rule seq_hoare_r[of _ _ true];
  (rule assigns_hoare_r'|rule assigns_hoare_r)?,
  assume_steps?;
  (rule while_invr_hoare_r)?,
  unfold unfolds,
  rel_auto+

method double_increment declares unfolds =
  rule seq_hoare_r[of _ _ true],
  rule while_invr_hoare_r,
  unfold unfolds,
  rel_auto+,
  assume_steps,
  rel_auto,
  rule while_invr_hoare_r,
  rel_auto+

method if_increment declares unfolds =
  unfold unfolds,
  rule cond_hoare_r;
  rule while_invr_hoare_r, rel_auto+

method rules_x =
  (rule seq_hoare_r|
    rule skip_hoare_r|
    rule while_invr_hoare_r|
    (rule cond_hoare_r; simp?, (rule hoare_false)?)| (* not sure if s/,/;/ is needed *)
    rule assigns_hoare_r'| (* infixr seqr means this is not useful chained with seq rule *)
    rule assert_hoare_r|
    rule assume_hoare_r
  )+

method rules =
  rule seq_hoare_r|
  rule skip_hoare_r|
  rule cond_hoare_r|
  rule assigns_hoare_r'| (* merges two subgoals? *)
  rule assigns_hoare_r|  (* may not be useful *)
  rule assert_hoare_r|
  rule assume_hoare_r|
  rule while_hoare_r|
  rule while_hoare_r'|
  rule while_invr_hoare_r

(* also have simp versions *)
method utp_methods = rel_auto|rel_blast|pred_auto|pred_blast

method vcg declares last_simps unfolds =
  if_increment unfolds: unfolds|
  even_count last_simps: last_simps unfolds: unfolds|
  double_increment unfolds: unfolds|
  increment unfolds: unfolds|
(*   (intro hoare_r_conj)?; (* intro rather than rule means it will be repeatedly applied; this may
not actually be useful (it's certainly not necessary) and so is currently commented out *) *)
    rules_x?;
    utp_methods,
    (auto simp: last_simps)?

text \<open>VCG for partial solving; applies a Hoare rule to the first subgoal (possibly generating more
subgoals) and then attempts to solve it and any simply-solvable immediately-succeeding goals.
For now, \texttt{rule seq_hoare_r[of _ _ true]}, which must precede the seq-assume-skip, will be
applied manually. For certain programs, we need to do utp_methods first (in fact, for some it's all
that's needed), but this results in slowdowns for other programs that do not require it first and in
fact some rules are not properly applied if the application does not come before utp_methods usage.\<close>
method vcg_step = utp_methods|rules, utp_methods?

(* Need weakest precondition reasoning? *)

end
