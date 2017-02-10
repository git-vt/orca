section \<open>Verification Condition Testing\<close>

theory VCG_Tests
  imports Hoare
begin

lemma
  assumes "weak_lens X"  
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0::int\<guillemotright>\<rbrace> X :== ((VAR X) +\<^sub>e \<guillemotleft>1\<guillemotright>) \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>1\<guillemotright>\<rbrace>"
  by (tactic \<open>vcg_tac @{context}\<close>)

end
