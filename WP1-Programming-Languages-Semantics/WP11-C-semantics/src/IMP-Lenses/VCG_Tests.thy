section \<open>Verification Condition Testing\<close>

theory VCG_Tests
  imports Hoare
begin

lemma
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0::int\<guillemotright>\<rbrace> X :== ((VAR X) +\<^sub>e \<guillemotleft>1\<guillemotright>) \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>1\<guillemotright>\<rbrace>"
  by (tactic \<open>vcg_tac @{context}\<close>)

lemma if_true:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0::int\<guillemotright>\<rbrace>
         IF TRUE THEN SKIP ELSE (X :== ((VAR X) +\<^sub>e \<guillemotleft>1\<guillemotright>))
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0\<guillemotright>\<rbrace>"
  by (tactic \<open>vcg_tac @{context}\<close>)

lemma if_false:
  assumes "weak_lens X"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0::int\<guillemotright>\<rbrace>
         IF TRUE THEN SKIP ELSE (X :== ((VAR X) +\<^sub>e \<guillemotleft>1\<guillemotright>))
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0\<guillemotright>\<rbrace>"
  by (tactic \<open>vcg_tac @{context}\<close>)

lemma swap_test:
  assumes "weak_lens X" and "weak_lens Y" and "weak_lens T"
  and "X \<bowtie> Y" and "X \<bowtie> T" and "Y \<bowtie> T"
  shows "\<lbrace>(VAR X) =\<^sub>e \<guillemotleft>0::int\<guillemotright> \<and>\<^sub>e (VAR Y) =\<^sub>e \<guillemotleft>1::int\<guillemotright>\<rbrace>
         T :== (VAR X);
         X :== (VAR Y);
         Y :== (VAR T)
         \<lbrace>(VAR X) =\<^sub>e \<guillemotleft>1::int\<guillemotright> \<and>\<^sub>e (VAR Y) =\<^sub>e \<guillemotleft>0::int\<guillemotright>\<rbrace>"
  apply (tactic \<open>vcg_tacx @{context}\<close>)
oops (* The sequential rule needs intermediate condition specifications for the generated schematic
variables; seL4 examples do this manually, as shown in
seL4/verification/l4v/tools/c-parser/testfiles/breakcontinue.thy *)

end
