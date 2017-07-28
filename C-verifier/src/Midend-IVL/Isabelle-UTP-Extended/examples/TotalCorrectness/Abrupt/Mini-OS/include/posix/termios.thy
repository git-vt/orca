 subsection \<open>Terminal I/O\<close>

theory termios
imports
  "../../../../../../hoare/AlgebraicLaws/Abrupt/algebraic_laws_abrupt"
begin

abbreviation "NCC \<equiv> \<guillemotleft>32::nat\<guillemotright>" -- \<open>Used for length of \texttt{c\_cc} array in \texttt{termios}
struct.\<close>

(* TODO: termios struct *)

subsubsection \<open>modem lines\<close>
abbreviation "TIOCM_DTR	\<equiv> \<guillemotleft>0x002::nat\<guillemotright>"
abbreviation "TIOCM_RTS	\<equiv> \<guillemotleft>0x004::nat\<guillemotright>"
abbreviation "TIOCM_CTS \<equiv> \<guillemotleft>0x020::nat\<guillemotright>"
abbreviation "TIOCM_CAR	\<equiv> \<guillemotleft>0x040::nat\<guillemotright>"
abbreviation "TIOCM_RI	\<equiv> \<guillemotleft>0x080::nat\<guillemotright>"
abbreviation "TIOCM_DSR	\<equiv> \<guillemotleft>0x100::nat\<guillemotright>"

subsubsection c_iflag

subsubsection c_oflag

subsubsection c_lflag

subsubsection c_cflag

subsubsection c_cc

end
