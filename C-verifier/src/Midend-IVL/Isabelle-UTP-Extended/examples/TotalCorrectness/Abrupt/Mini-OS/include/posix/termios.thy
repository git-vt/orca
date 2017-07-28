 subsection \<open>Terminal I/O\<close>

theory termios
imports
  "../../../../../../hoare/AlgebraicLaws/Abrupt/algebraic_laws_abrupt"
begin

abbreviation "NCC \<equiv> \<guillemotleft>32::nat\<guillemotright>" -- \<open>Used for length of \texttt{c\_cc} array in \texttt{termios}
struct.\<close>

(* TODO: termios struct *)

subsubsection \<open>modem lines\<close>
abbreviation "TIOCM_DTR \<equiv> \<guillemotleft>0x002::nat\<guillemotright>"
abbreviation "TIOCM_RTS \<equiv> \<guillemotleft>0x004::nat\<guillemotright>"
abbreviation "TIOCM_CTS \<equiv> \<guillemotleft>0x020::nat\<guillemotright>"
abbreviation "TIOCM_CAR \<equiv> \<guillemotleft>0x040::nat\<guillemotright>"
abbreviation "TIOCM_RI  \<equiv> \<guillemotleft>0x080::nat\<guillemotright>"
abbreviation "TIOCM_DSR \<equiv> \<guillemotleft>0x100::nat\<guillemotright>"

subsubsection c_iflag
abbreviation "IGNBRK  \<equiv> 0x00000001"
abbreviation "BRKINT  \<equiv> 0x00000002"
abbreviation "IGNPAR  \<equiv> 0x00000004"
abbreviation "PARMRK  \<equiv> 0x00000008"
abbreviation "INPCK   \<equiv> 0x00000010"
abbreviation "ISTRIP  \<equiv> 0x00000020"
abbreviation "INLCR   \<equiv> 0x00000040"
abbreviation "IGNCR   \<equiv> 0x00000080"
abbreviation "ICRNL   \<equiv> 0x00000100"
abbreviation "IUCLC   \<equiv> 0x00000200"
abbreviation "IXON    \<equiv> 0x00000400"
abbreviation "IXANY   \<equiv> 0x00000800"
abbreviation "IXOFF   \<equiv> 0x00001000"
abbreviation "IMAXBEL \<equiv> 0x00002000"
abbreviation "IUTF8   \<equiv> 0x00004000"

subsubsection c_oflag
abbreviation "OPOST  \<equiv> 0x00000001"
abbreviation "OLCUC  \<equiv> 0x00000002"
abbreviation "ONLCR  \<equiv> 0x00000004"
abbreviation "OCRNL  \<equiv> 0x00000008"
abbreviation "ONOCR  \<equiv> 0x00000010"
abbreviation "ONLRET \<equiv> 0x00000020"
abbreviation "OFILL  \<equiv> 0x00000040"
abbreviation "OFDEL  \<equiv> 0x00000080"
  
subsubsection c_lflag
abbreviation "ISIG    \<equiv> 0x00000001"
abbreviation "ICANON  \<equiv> 0x00000002"
abbreviation "XCASE   \<equiv> 0x00000004"
abbreviation "ECHO    \<equiv> 0x00000008"
abbreviation "ECHOE   \<equiv> 0x00000010"
abbreviation "ECHOK   \<equiv> 0x00000020"
abbreviation "ECHONL  \<equiv> 0x00000040"
abbreviation "NOFLSH  \<equiv> 0x00000080"
abbreviation "TOSTOP  \<equiv> 0x00000100"
abbreviation "ECHOCTL \<equiv> 0x00000200"
abbreviation "ECHOPRT \<equiv> 0x00000400"
abbreviation "ECHOKE  \<equiv> 0x00000800"
abbreviation "FLUSHO  \<equiv> 0x00002000"
abbreviation "PENDIN  \<equiv> 0x00004000"
abbreviation "IEXTEN  \<equiv> 0x00008000"

subsubsection c_cflag
abbreviation "CSIZE  \<equiv> 0x00000030"
abbreviation "CS8    \<equiv> 0x00000030"
abbreviation "CSTOPB \<equiv> 0x00000040"
abbreviation "CREAD  \<equiv> 0x00000080"
abbreviation "PARENB \<equiv> 0x00000100"
abbreviation "PARODD \<equiv> 0x00000200"
abbreviation "HUPCL  \<equiv> 0x00000400"
abbreviation "CLOCAL \<equiv> 0x00000800"

subsubsection c_cc
abbreviation "VTIME \<equiv> 5"
abbreviation "VMIN  \<equiv> 6"

abbreviation "TCSANOW   \<equiv> 0"
abbreviation "TCSADRAIN \<equiv> 1"
abbreviation "TCSAFLUSH \<equiv> 2"

end
