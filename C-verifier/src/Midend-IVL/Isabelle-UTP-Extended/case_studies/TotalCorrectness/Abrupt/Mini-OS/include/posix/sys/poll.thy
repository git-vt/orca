subsection \<open>Polling\<close>

theory poll
imports
  "../../../../../../../hoare/AlgebraicLaws/Abrupt/algebraic_laws_abrupt"
begin

text \<open>Based on FreeBSD's \texttt{sys/sys/poll.h}; \texttt{nfds\_t} == \texttt{unsigned int}\<close>

(* need pollfd struct *)

text \<open>Requestable events.\<close>
abbreviation "POLLIN \<equiv> \<guillemotleft>0x01::nat\<guillemotright>" -- \<open>any readable data available\<close>
abbreviation "POLLPRI \<equiv> \<guillemotleft>0x02::nat\<guillemotright>" -- \<open>OOB/Urgent readable data\<close>
abbreviation "POLLOUT \<equiv> \<guillemotleft>0x04::nat\<guillemotright>" -- \<open>file descriptor is writeable\<close>
abbreviation "POLLRDNORM \<equiv> \<guillemotleft>0x40::nat\<guillemotright>" -- \<open>non-OOB/URG data available\<close>
abbreviation "POLLWRNORM \<equiv> POLLOUT" -- \<open>no write type differentiation\<close>
abbreviation "POLLRDBAND \<equiv> \<guillemotleft>0x80::nat\<guillemotright>" -- \<open>OOB/Urgent readable data\<close>
abbreviation "POLLWRBAND \<equiv> \<guillemotleft>0x100::nat\<guillemotright>" -- \<open>OOB/Urgent data can be written\<close>

text \<open>Events that are always set whenever they occur, no request needed.\<close>
abbreviation "POLLERR \<equiv> \<guillemotleft>0x08::nat\<guillemotright>" -- \<open>some poll error occurred\<close>
abbreviation "POLLHUP \<equiv> \<guillemotleft>0x10::nat\<guillemotright>" -- \<open>file descriptor was "hung up"\<close>
abbreviation "POLLNVAL \<equiv> \<guillemotleft>0x20::nat\<guillemotright>" -- \<open>requested events "invalid"\<close>

end
