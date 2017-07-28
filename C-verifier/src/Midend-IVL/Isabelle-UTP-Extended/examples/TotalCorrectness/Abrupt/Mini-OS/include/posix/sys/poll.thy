subsection \<open>Polling\<close>

theory poll
imports
  "../../../../../../../hoare/AlgebraicLaws/Abrupt/algebraic_laws_abrupt"
begin

text \<open>Based on FreeBSD's \texttt{sys/sys/poll.h}; \texttt{nfds\_t} == \texttt{unsigned int}\<close>

(* need pollfd struct *)

text \<open>Requestable events.\<close>
abbreviation "POLLIN \<equiv> \<guillemotleft>1::nat\<guillemotright>" -- \<open>any readable data available\<close>
abbreviation "POLLPRI \<equiv> \<guillemotleft>2::nat\<guillemotright>" -- \<open>OOB/Urgent readable data\<close>
abbreviation "POLLOUT \<equiv> \<guillemotleft>4::nat\<guillemotright>" -- \<open>file descriptor is writeable\<close>
abbreviation "POLLRDNORM \<equiv> \<guillemotleft>64::nat\<guillemotright>" -- \<open>0x40, non-OOB/URG data available\<close>
abbreviation "POLLWRNORM \<equiv> POLLOUT" -- \<open>no write type differentiation\<close>
abbreviation "POLLRDBAND \<equiv> \<guillemotleft>128::nat\<guillemotright>" -- \<open>0x80, OOB/Urgent readable data\<close>
abbreviation "POLLWRBAND \<equiv> \<guillemotleft>256::nat\<guillemotright>" -- \<open>0x100, OOB/Urgent data can be written\<close>

text \<open>Events that are always set whenever they occur, no request needed.\<close>
abbreviation "POLLERR \<equiv> \<guillemotleft>8::nat\<guillemotright>" -- \<open>some poll error occurred\<close>
abbreviation "POLLHUP \<equiv> \<guillemotleft>16::nat\<guillemotright>" -- \<open>0x10, file descriptor was "hung up"\<close>
abbreviation "POLLNVAL \<equiv> \<guillemotleft>32::nat\<guillemotright>" -- \<open>requested events "invalid"\<close>

end
