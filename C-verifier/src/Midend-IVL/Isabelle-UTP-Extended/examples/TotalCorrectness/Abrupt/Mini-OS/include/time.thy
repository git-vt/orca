subsection \<open>Time\<close>

theory time
imports
  "../helpers"
begin

subsubsection \<open>System time\<close>

abbreviation "NOW \<equiv> monotonic_clock" (* TODO: need nondeterministic function results/etc.; we know
monotonic_clock always increases, though. *)
text \<open>While the multipliers/divisors are unsigned in the source header, the times are of type
\texttt{s\_time\_t}, which is signed, and as such the multipliers/divisors must be signed for
type-correctness. Technically that type should be unsigned as the result of
\texttt{monotonic\_clock} is unsigned (\texttt{uint64_t}), so that's confusing.\<close>
abbreviation "SECONDS s     \<equiv> s  * \<guillemotleft>1000000000::int\<guillemotright>"
abbreviation "TENTHS ts     \<equiv> ts * \<guillemotleft>100000000::int\<guillemotright>"
abbreviation "HUNDREDTHS hs \<equiv> hs * \<guillemotleft>10000000::int\<guillemotright>"
abbreviation "MILLISECS ms  \<equiv> ms * \<guillemotleft>1000000::int\<guillemotright>"
abbreviation "MICROSECS us  \<equiv> us * \<guillemotleft>1000::int\<guillemotright>"
abbreviation "Time_Max \<equiv> \<guillemotleft>0x7fffffffffffffff::int\<guillemotright>"
abbreviation "FOREVER \<equiv> Time_Max"
abbreviation "NSEC_TO_USEC nsec \<equiv> nsec div \<guillemotleft>1000::int\<guillemotright>"
abbreviation "NSEC_TO_MSEC nsec \<equiv> nsec div \<guillemotleft>1000000::int\<guillemotright>"
abbreviation "NSEC_TO_SEC nsec \<equiv> nsec div \<guillemotleft>1000000000::int\<guillemotright>"

subsubsection \<open>Wall time\<close>

text \<open>Mostly from \texttt{sys/time.h}; in this context, timespec is only used for wall time, but in
other setups (C99 or later?) timespec can also be used for system time measured by a monotonic
clock.\<close>
record timespec =
  tv_sec :: int -- \<open>\texttt{time\_t} (\texttt{long})\<close>
  tv_nsec :: int -- \<open>\texttt{long}\<close>

(* TODO: struct timezone is empty, meaning it's invalid according to the C standard (though gcc
allows empty structs *)

record timeval =
  tv_sec :: int -- \<open>\texttt{time\_t} (\texttt{long})\<close>
  tv_usec :: int -- \<open>\texttt{suseconds\_t} ({long}), microseconds\<close>

(* TODO: Use gettimeofday function somehow? Note that it's technically monotonic time on ARM as
ARM apparently doesn't support wall-clock time directly. (Usually the OS provides wall-clock time
somehow.) *)

end
