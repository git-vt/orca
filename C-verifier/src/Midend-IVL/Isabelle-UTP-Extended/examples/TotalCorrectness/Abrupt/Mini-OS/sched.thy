subsection \<open>Thread scheduling\<close>

theory sched
imports
  "include/time"
begin

subsubsection \<open>From header file \texttt{sched.h}\<close>

record thread =
  name :: "char list" -- \<open>\texttt{char*} in source\<close>
  stack :: "char list" -- \<open>\texttt{char*} in source\<close>
  sp :: nat -- \<open>unsigned long, stack pointer\<close>
  ip :: nat -- \<open>unsigned long, instruction pointer\<close>
  (* MINIOS_TAILQ_ENTRY(struct thread) thread_list; needs recursion *)
  flags :: nat -- uint32
  wakeup_time :: s_time_t
  (* struct _reent reent; if HAVE_LIBC is set *)

(* TODO: extern struct thread *idle_thread;? *)

abbreviation "RUNNABLE_FLAG \<equiv> \<guillemotleft>1::nat\<guillemotright>"

abbreviation "is_runnable thread \<equiv> &thread\<lparr>flags\<rparr>\<^sub>r \<and>\<^sub>b\<^sub>u RUNNABLE_FLAG"
abbreviation "set_runnable thread \<equiv>
  thread \<Midarrow> &thread(flags_update \<mapsto> &thread\<lparr>flags\<rparr>\<^sub>r \<or>\<^sub>b\<^sub>u RUNNABLE_FLAG)\<^sub>r"
abbreviation "clear_runnable thread \<equiv>
  thread \<Midarrow> &thread(flags_update \<mapsto> &thread\<lparr>flags\<rparr>\<^sub>r \<and>\<^sub>b\<^sub>u \<not>\<^bsub>u/SIZEOF_INT\<^esub> RUNNABLE_FLAG)\<^sub>r"

(* TODO: architecture-specific #define switch_threads(prev, next) arch_switch_threads(prev, next) *)

subsubsection \<open>From source file \texttt{sched.c}\<close>

(* TODO:
struct thread *idle_thread = NULL; // should start as null anyway
MINIOS_TAILQ_HEAD(thread_list, struct thread);
static struct thread_list exited_threads = MINIOS_TAILQ_HEAD_INITIALIZER(exited_threads);
static struct thread_list thread_list = MINIOS_TAILQ_HEAD_INITIALIZER(thread_list);
static int threads_started; // starts as 0


all the rest
*)

end
