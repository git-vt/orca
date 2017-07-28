subsection \<open>File descriptor control\<close>

theory fcntl
imports
  "../../../../../../../hoare/AlgebraicLaws/Abrupt/algebraic_laws_abrupt"
begin

abbreviation "F_UNLOCK \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "F_LOCK \<equiv> \<guillemotleft>1::nat\<guillemotright>"
abbreviation "F_TLOCK \<equiv> \<guillemotleft>2::nat\<guillemotright>"
abbreviation "F_TEST \<equiv> \<guillemotleft>3::nat\<guillemotright>"

end
