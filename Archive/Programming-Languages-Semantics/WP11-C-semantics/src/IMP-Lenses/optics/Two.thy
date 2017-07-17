section {* Types of cardinality 2 or greater *}

theory Two
imports Real
begin

class two =
  assumes card_two: "infinite (UNIV :: 'a set) \<or> card (UNIV :: 'a set) \<ge> 2"
begin
lemma two_diff: "\<exists> x y :: 'a. x \<noteq> y"
proof -
  obtain A where "finite A" "card A = 2" "A \<subseteq> (UNIV :: 'a set)"
  proof (cases "infinite (UNIV :: 'a set)")
    case True
    with infinite_arbitrarily_large[of "UNIV :: 'a set" 2] that
    show ?thesis by auto
  next
    case False
    with card_two that
    show ?thesis
      by (metis UNIV_bool card_UNIV_bool card_image card_le_inj finite.intros(1) finite_insert finite_subset)
  qed
  thus ?thesis
    by (metis (full_types) One_nat_def Suc_1 UNIV_eq_I card.empty card.insert finite.intros(1) insertCI nat.inject nat.simps(3))
qed
end

instance bool :: two
  by (intro_classes, auto)

instance nat :: two
  by (intro_classes, auto)

instance int :: two
  by (intro_classes, auto simp add: infinite_UNIV_int)

instance rat :: two
  by (intro_classes, auto simp add: infinite_UNIV_char_0)

instance real :: two
  by (intro_classes, auto simp add: infinite_UNIV_char_0)

instance list :: (type) two
  by (intro_classes, auto simp add: infinite_UNIV_listI)

end