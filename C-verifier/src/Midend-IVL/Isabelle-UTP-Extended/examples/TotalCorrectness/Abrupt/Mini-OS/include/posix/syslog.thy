subsection \<open>System logging\<close>

theory syslog
imports
  "../../../../../../../hoare/AlgebraicLaws/Abrupt/algebraic_laws_abrupt"
begin

abbreviation "LOG_PID \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "LOG_CONS \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "LOG_NDELAY \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "LOG_ODELAY \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "LOG_NOWAIT \<equiv> \<guillemotleft>0::nat\<guillemotright>"

abbreviation "LOG_KERN \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "LOG_USER \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "LOG_MAIL \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "LOG_NEWS \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "LOG_UUCP \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "LOG_DAEMON \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "LOG_AUTH \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "LOG_CRON \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "LOG_LPR \<equiv> \<guillemotleft>0::nat\<guillemotright>"

text \<open>Apparently not yet supported by Mini-OS\<close>
abbreviation "LOG_EMERG \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "LOG_ALERT \<equiv> \<guillemotleft>1::nat\<guillemotright>"
abbreviation "LOG_CRIT \<equiv> \<guillemotleft>2::nat\<guillemotright>"
abbreviation "LOG_ERR \<equiv> \<guillemotleft>3::nat\<guillemotright>"
abbreviation "LOG_WARNING \<equiv> \<guillemotleft>4::nat\<guillemotright>"
abbreviation "LOG_NOTICE \<equiv> \<guillemotleft>5::nat\<guillemotright>"
abbreviation "LOG_INFO \<equiv> \<guillemotleft>6::nat\<guillemotright>"
abbreviation "LOG_DEBUG \<equiv> \<guillemotleft>7::nat\<guillemotright>"

end
