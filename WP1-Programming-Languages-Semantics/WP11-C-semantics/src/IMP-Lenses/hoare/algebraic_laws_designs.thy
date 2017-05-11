
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

lemma throw_right_zero:
  fixes P::"('f,'\<alpha>) hrel_cp"
  assumes "$ok\<acute> \<sharp> P" "$ok \<sharp> P" "$abrupt\<acute> \<sharp> P" "$abrupt \<sharp> P"
          "$fault\<acute> \<sharp> P" "$fault \<sharp> P"
  shows "(Simpl P  ;; THROW) = THROW"
oops
 
subsection"Skip"

lemma skip_c_left_unit[simp]: 
  "(SKIP ;;  Simpl P) =  Simpl P"
  by rel_auto

lemma skip_c_right_unit[simp]: 
  "(Simpl P  ;;  SKIP) =  Simpl P"  
  by rel_auto (metis option.exhaust_sel)


end