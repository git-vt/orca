
section "Algebraic laws for designs"
theory algebraic_laws_designs
imports "../theories/utp_fault_designs"

begin

subsection"Throw"

lemma throw_left_zero[simp]: 
  "(THROW ;; Simpl P) = THROW" 
  by rel_auto

lemma throw_right_zero_skip[simp]: 
  "(SKIP ;; THROW) = THROW " 
  by rel_auto

subsection"Skip"

lemma skip_c_left_unit[simp]: 
  "(SKIP ;;  Simpl P) =  Simpl P"
  by rel_auto

lemma skip_c_right_unit[simp]: 
  "(Simpl P  ;;  SKIP) =  Simpl P"  
  by rel_auto (metis option.exhaust_sel)


end