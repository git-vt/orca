section \<open>Verification Condition Testing\<close>

theory utp_hoare_total
  imports "theories/utp_fault_designs"
begin
definition hoare_rd :: "'\<alpha> cond \<Rightarrow> ('f,'\<alpha>) hrel_cp \<Rightarrow> '\<alpha> cond \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>\<^sub>D") where
[upred_defs]:"\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>D = ((\<lceil>p\<rceil>\<^sub>C\<^sub>< \<and> $ok \<and> \<not>$abrupt \<and> $fault =\<^sub>u \<guillemotleft>None\<guillemotright> \<Rightarrow> 
                          \<lceil>r\<rceil>\<^sub>C\<^sub>> \<and> $ok\<acute> \<and> \<not>$abrupt\<acute> \<and> $fault\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright>) \<sqsubseteq> Q)"
end