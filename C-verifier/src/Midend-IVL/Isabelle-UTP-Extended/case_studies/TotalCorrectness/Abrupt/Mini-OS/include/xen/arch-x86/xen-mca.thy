subsection \<open>Machine Check Architecture Functionality for x86-64\<close>

theory "xen-mca"
imports
  "../xen"
begin

abbreviation "HYPERVISOR_mca'' \<equiv> HYPERVISOR_arch_0''"

abbreviation "XEN_MCA_INTERFACE_VERSION \<equiv> \<guillemotleft>0x01ecc003::nat\<guillemotright>"

text \<open>IN: Dom0 calls hypercall to retrieve nonurgent telemetry\<close>
abbreviation "XEN_MC_NONURGENT \<equiv> \<guillemotleft>0x0001::nat\<guillemotright>"
text \<open>IN: Dom0/DomU calls hypercall to retrieve urgent telemetry\<close>
abbreviation "XEN_MC_URGENT \<equiv> \<guillemotleft>0x0002::nat\<guillemotright>"
text \<open>IN: Dom0 acknowledges previosly-fetched telemetry\<close>
abbreviation "XEN_MC_ACK \<equiv> \<guillemotleft>0x0004::nat\<guillemotright>"

text \<open>OUT: All is ok\<close>
abbreviation "XEN_MC_OK \<equiv> \<guillemotleft>0x0::nat\<guillemotright>"
text \<open>OUT: Domain could not fetch data.\<close>
abbreviation "XEN_MC_FETCHFAILED \<equiv> \<guillemotleft>0x1::nat\<guillemotright>"
text \<open>OUT: There was no machine check data to fetch.\<close>
abbreviation "XEN_MC_NODATA \<equiv> \<guillemotleft>0x2::nat\<guillemotright>"
text \<open>OUT: Between notification time and this hypercall an other (most likely) correctable error
happened. The fetched data does not match the original machine check data.\<close>
abbreviation "XEN_MC_NOMATCH \<equiv> \<guillemotleft>0x4::nat\<guillemotright>"

text \<open>OUT: DomU did not register MC NMI handler. Try something else.\<close>
abbreviation "XEN_MC_CANNOTHANDLE \<equiv> \<guillemotleft>0x8::nat\<guillemotright>"
text \<open>OUT: Notifying DomU failed. Retry later or try something else.\<close>
abbreviation "XEN_MC_NOTDELIVERED \<equiv> \<guillemotleft>0x10::nat\<guillemotright>"
text \<open>Note, XEN_MC_CANNOTHANDLE and XEN_MC_NOTDELIVERED are mutually exclusive.\<close>

abbreviation "VIRQ_MCA \<equiv> VIRQ_ARCH_0" -- \<open>G. (DOM0) Machine Check Architecture\<close>

text \<open>Machine Check Architecture:
structs are read-only and used to report all kinds of
correctable and uncorrectable errors detected by the HW.
\<^item> Dom0 and DomU: register a handler to get notified.
\<^item> Dom0 only: Correctable errors are reported via VIRQ_MCA
\<^item> Dom0 and DomU: Uncorrectable errors are reported via nmi handlers\<close>
abbreviation "MC_TYPE_GLOBAL   \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "MC_TYPE_BANK     \<equiv> \<guillemotleft>1::nat\<guillemotright>"
abbreviation "MC_TYPE_EXTENDED \<equiv> \<guillemotleft>2::nat\<guillemotright>"
abbreviation "MC_TYPE_RECOVERY \<equiv> \<guillemotleft>3::nat\<guillemotright>"

record mcinfo_common =
  type :: nat -- \<open>16, structure type\<close>
  size :: nat -- \<open>16, size of this struct in bytes\<close>

abbreviation "MC_FLAG_CORRECTABLE   \<equiv> \<guillemotleft>0b0000001::nat\<guillemotright>"
abbreviation "MC_FLAG_UNCORRECTABLE \<equiv> \<guillemotleft>0b0000010::nat\<guillemotright>"
abbreviation "MC_FLAG_RECOVERABLE   \<equiv> \<guillemotleft>0b0000100::nat\<guillemotright>"
abbreviation "MC_FLAG_POLLED        \<equiv> \<guillemotleft>0b0001000::nat\<guillemotright>"
abbreviation "MC_FLAG_RESET         \<equiv> \<guillemotleft>0b0010000::nat\<guillemotright>"
abbreviation "MC_FLAG_CMCI          \<equiv> \<guillemotleft>0b0100000::nat\<guillemotright>"
abbreviation "MC_FLAG_MCE           \<equiv> \<guillemotleft>0b1000000::nat\<guillemotright>"

text \<open>Global x86 MC information\<close>
record mcinfo_global =
  common :: mcinfo_common
  mc_domid :: nat -- \<open>16, running domain at the time in error (most likely the impacted one)\<close>
  mc_vcpuid :: nat -- \<open>16, virtual cpu scheduled for mc_domid\<close>
  mc_socketid :: nat -- \<open>32, physical socket of the physical core\<close>
  mc_coreid :: nat -- \<open>16, physical impacted core\<close>
  mc_core_threadid :: nat -- \<open>16, core thread of physical core\<close>
  mc_apicid :: nat -- 32
  mc_flags :: nat -- 32
  mc_gstatus :: nat -- \<open>64, global status\<close>

text \<open>Global bank-local x86 MC information\<close>
record mcinfo_bank =
  common :: mcinfo_common
  mc_bank :: nat -- \<open>16, bank number\<close>
  mc_domid :: nat -- \<open>16, Usecase 5: domain referenced by \texttt{mc\_addr} on dom0 and if \texttt{mc\_addr} is valid. Never valid on DomU.\<close>
  mc_status :: nat -- \<open>64, bank status\<close>
  mc_addr :: nat -- \<open>64, bank address, only valid if addr bit is set in \texttt{mc\_status}\<close>
  mc_misc :: nat -- 64
  mc_ctrl2 :: nat -- 64
  mc_tsc :: nat -- 64

record mcinfo_msr =
  reg :: nat -- \<open>64, MSR\<close>
  "value" :: nat -- \<open>64, MSR value\<close>

text \<open>Contains MC information from other or additional MC MSRs. You can fill up to five registers;
if you need more, then use this structure multiple times. Currently, Intel extended MSRs (32/64)
include all GP registers and E(R)FLAGS, E(R)IP, E(R)MISC; up to 11/19 of them might be useful at
present, so expand the array to 16/32 to leave room. (Verification is assuming 64-bit, so 32.)\<close>
record mcinfo_extended =
  common :: mcinfo_common
  mc_msrs :: nat -- \<open>32, Number of MSRs with valid values.\<close>
  mc_msr :: "mcinfo_msr list" -- 32

text \<open>Recovery Action flags. Giving recovery result information to DOM0\<close>

text \<open>Xen takes successful recovery action, the error is recovered\<close>
abbreviation "REC_ACTION_RECOVERED \<equiv> \<guillemotleft>0b001::nat\<guillemotright>"
text \<open>No action is performed by XEN\<close>
abbreviation "REC_ACTION_NONE \<equiv> \<guillemotleft>0b010::nat\<guillemotright>"
text \<open>It's possible DOM0 might take action ownership in some case\<close>
abbreviation "REC_ACTION_NEED_RESET \<equiv> \<guillemotleft>0b100::nat\<guillemotright>"

text \<open>Different Recovery Action types; if the action is performed successfully,
@{const REC_ACTION_RECOVERED} flag will be returned.\<close>

text\<open>Page Offline Action\<close>
abbreviation "MC_ACTION_PAGE_OFFLINE \<equiv> \<guillemotleft>0b001::nat\<guillemotright>"
text\<open>CPU offline Action\<close>
abbreviation "MC_ACTION_CPU_OFFLINE \<equiv> \<guillemotleft>0b010::nat\<guillemotright>"
text\<open>L3 cache disable Action\<close>
abbreviation "MC_ACTION_CACHE_SHRINK \<equiv> \<guillemotleft>0b100::nat\<guillemotright>"

text \<open>Skipping recovery interface description\<close>

text \<open>Params for passing the offlined page number to DOM0\<close>
record page_offline_action =
  mfn :: nat -- 64
  status :: nat -- 64

text \<open>Params for passing the identity of the offlined CPU to DOM0\<close>
record cpu_offline_action =
  mc_socketid :: nat -- 32
  mc_coreid :: nat -- 16
  mc_core_threadid :: nat -- 16

abbreviation "MAX_UNION_SIZE \<equiv> \<guillemotleft>16::nat\<guillemotright>"
record mcinfo_recovery =
  common :: mcinfo_common
  mc_bank :: nat -- \<open>16, bank number\<close>
  action_flags :: nat -- 8
  action_types :: nat -- 8
  union action_info

abbreviation "MCINFO_HYPERCALLSIZE    \<equiv> \<guillemotleft>1024::nat\<guillemotright>"
abbreviation "MCINFO_MAXSIZE          \<equiv> \<guillemotleft>768::nat\<guillemotright>"
abbreviation "MCINFO_FLAGS_UNCOMPLETE \<equiv> \<guillemotleft>0b1::nat\<guillemotright>"

record mc_info_t =
  mi_nentries :: nat -- \<open>32, number of \texttt{mcinfo\_*} entries in \texttt{mi_data}\<close>
  flags :: nat -- 32
  mi_data :: "nat list" -- \<open>64[(@{const MCINFO_MAXSIZE} - 1) div 8]\<close>

text \<open>\texttt{DEFINE\_XEN\_GUEST\_HANDLE(mc\_info\_t)}\<close>
record '\<alpha> guest_handle_mc_info_t'' =
  p :: "mc_info_t \<Longrightarrow> '\<alpha>"

abbreviation "MC_MSR_ARRAYSIZE'' \<equiv> \<guillemotleft>8::nat\<guillemotright>"
abbreviation "MC_NMSRS''         \<equiv> \<guillemotleft>1::nat\<guillemotright>"
abbreviation "MC_NCAPS           \<equiv> \<guillemotleft>7::nat\<guillemotright>" -- \<open>7 CPU feature flag words\<close>
abbreviation "MC_CAPS_STD_EDX    \<equiv> \<guillemotleft>0::nat\<guillemotright>" -- \<open>cpuid level 0x00000001 (\texttt{%edx})\<close>
abbreviation "MC_CAPS_AMD_EDX    \<equiv> \<guillemotleft>1::nat\<guillemotright>" -- \<open>cpuid level 0x80000001 (\texttt{%edx})\<close>
abbreviation "MC_CAPS_TM         \<equiv> \<guillemotleft>2::nat\<guillemotright>" -- \<open>cpuid level 0x80860001 (TransMeta)\<close>
abbreviation "MC_CAPS_LINUX      \<equiv> \<guillemotleft>3::nat\<guillemotright>" -- \<open>Linux-defined\<close>
abbreviation "MC_CAPS_STD_ECX    \<equiv> \<guillemotleft>4::nat\<guillemotright>" -- \<open>cpuid level 0x00000001 (\texttt{%ecx})\<close>
abbreviation "MC_CAPS_VIA        \<equiv> \<guillemotleft>5::nat\<guillemotright>" -- \<open>cpuid level 0xc0000001\<close>
abbreviation "MC_CAPS_AMD_ECX    \<equiv> \<guillemotleft>6::nat\<guillemotright>" -- \<open>cpuid level 0x80000001 (\texttt{%ecx})\<close>

record mcinfo_logical_cpu =
  mc_cpunr :: nat -- 32
  mc_chipid :: nat -- 32
  mc_coreid :: nat -- 16
  mc_threadid :: nat -- 16
  mc_apicid :: nat -- 32
  mc_clusterid :: nat -- 32
  mc_ncores :: nat -- 32
  mc_ncores_active :: nat -- 32
  mc_nthreads :: nat -- 32
  mc_cpuid_level :: int -- 32
  mc_family :: nat -- 32
  mc_vendor :: nat -- 32
  mc_model :: nat -- 32
  mc_step :: nat -- 32
  mc_vendorid :: "char list" -- \<open>char[16]\<close>
  mc_brandid :: "char list" -- \<open>char[64]\<close>
  mc_cpu_caps :: "nat list" -- \<open>32[@{const MC_NCAPS}]\<close>
  mc_cache_size :: nat -- 32
  mc_cache_alignment :: nat -- 32
  mc_nmsrvals :: int -- 32
  mc_msrvalues :: mcinfo_msr -- \<open>[@{const MC_MSR_ARRAYSIZE''}]\<close>

type_synonym xen_mc_logical_cpu_t = mcinfo_logical_cpu

text \<open>\texttt{DEFINE\_XEN\_GUEST\_HANDLE(xen\_mc\_logical\_cpu\_t)}\<close>
record '\<alpha> guest_handle_xen_mc_logical_cpu_t'' =
  p :: "xen_mc_logical_cpu_t \<Longrightarrow> '\<alpha>"

(* TODO: struct access defines x86_mcinfo_nentries, x86_mcinfo_first, x86_mcinfo_next,
x86_mcinfo_lookup; some may be tricky due to icky typecasting to use pointer arithmetic. *)

text \<open>Use cases:
\<^enum> Register machine check trap callback handler (already done by \texttt{set\_trap\_table} hypercall)
\<^enum> Dom0 registers machine check event callback handler (done by \texttt{EVTCHNOP\_bind\_virq})
\<^enum> Fetch machine check data from hypervisor.
The last hypercall is special because both Dom0 and DomU must use it.\<close>
abbreviation "XEN_MC_fetch \<equiv> \<guillemotleft>1::nat\<guillemotright>"

record '\<alpha> xen_mc_fetch_t =
  -- \<open>IN/OUT variables\<close>
  flags :: nat -- \<open>32, IN: @{const XEN_MC_NONURGENT}, @{const XEN_MC_URGENT}, @{const XEN_MC_ACK} if
                   ack'ing an earlier fetch\<close>
               -- \<open>OUT: @{const XEN_MC_OK}, @{const XEN_MC_FETCHFAILED}, @{const XEN_MC_NODATA},
                   @{const XEN_MC_NOMATCH}\<close>
  pad0' :: nat -- 32
  fetch_id :: nat -- \<open>64, IN: id we are ack'ing, OUT: id for ack\<close>
  -- \<open>OUT variable\<close>
  data :: "'\<alpha> guest_handle_mc_info_t''"

text \<open>Additional use case: tells the hypervisor to notify a DomU about machine check error.\<close>
abbreviation "XEN_MC_notifydomain \<equiv> \<guillemotleft>2::nat\<guillemotright>"
record xen_mc_notifydomain_t =
  -- \<open>IN variables\<close>
  mc_domid :: nat -- \<open>16, the unprivileged domain to notify.\<close>
  mc_vcpuid :: nat -- \<open>16, the vcpu in mc_domid to notify.
                       Usually echo'd value from the fetch hypercall.\<close>
  -- \<open>IN/OUT variable\<close>
  flags :: nat -- \<open>32, IN: @{const XEN_MC_CORRECTABLE}, @{const XEN_MC_TRAP}\<close>
               -- \<open>OUT: @{const XEN_MC_OK}, @{const XEN_MC_CANNOTHANDLE},
                  @{const XEN_MC_NOTDELIVERED}, @{const XEN_MC_NOMATCH}\<close>
(* TODO: Xen guest handle for the above struct? *)

abbreviation "XEN_MC_physcpuinfo \<equiv> \<guillemotleft>3::nat\<guillemotright>"
record '\<alpha> xen_mc_physcpuinfo =
  -- \<open>IN/OUT\<close>
  ncpus :: nat -- 32
  pad0' :: nat -- 32
  -- OUT
  info :: "'\<alpha> guest_handle_xen_mc_logical_cpu_t''"

abbreviation "XEN_MC_msrinject \<equiv> \<guillemotleft>4::nat\<guillemotright>"
abbreviation "MC_MSRINJ_MAXMSRS \<equiv> \<guillemotleft>8::nat\<guillemotright>"
record xen_mc_msrinject =
  -- IN
  mcinj_cpunr :: nat -- \<open> 32, target processor id\<close>
  mcinj_flags :: nat -- \<open> 32, see \texttt{MC\_MSRINJ\_F\_*} below\<close>
  mcinj_count :: nat -- \<open> 32, 0 .. count-1 in array are valid\<close>
  pad0' :: nat -- 32
  mcinj_msr :: "mcinfo_msr list" -- \<open>[@{const MC_MSRINJ_MAXMSRS}]\<close>

text \<open>Flags for mcinj_flags above; bits 16-31 are reserved\<close>
abbreviation "MC_MSRINJ_F_INTERPOSE \<equiv> \<guillemotleft>0b1::nat\<guillemotright>"

abbreviation "XEN_MC_mceinject \<equiv> \<guillemotleft>5::nat\<guillemotright>"
record xen_mc_mceinject =
  mceinj_cpunr :: nat -- \<open>32, target processor id\<close>

abbreviation "XEN_MC_inject_v2            \<equiv> \<guillemotleft>6::nat\<guillemotright>"
abbreviation "XEN_MC_INJECT_TYPE_MASK     \<equiv> \<guillemotleft>0x7::nat\<guillemotright>"
abbreviation "XEN_MC_INJECT_TYPE_MCE      \<equiv> \<guillemotleft>0x0::nat\<guillemotright>"
abbreviation "XEN_MC_INJECT_TYPE_CMCI     \<equiv> \<guillemotleft>0x1::nat\<guillemotright>"
abbreviation "XEN_MC_INJECT_CPU_BROADCAST \<equiv> \<guillemotleft>0x8::nat\<guillemotright>"

text \<open>Assuming \texttt{\_\_XEN\_\_} or \texttt{\_\_XEN\_TOOLS\_\_} defined.\<close>
record xen_mc_inject_v2 =
  flags :: nat -- 32
  cpumap :: xenctl_bitmap

record xen_mc_t =
  cmd :: nat -- 32
  interface_version :: nat -- \<open>32, @{const XEN_MCA_INTERFACE_VERSION}\<close>
  u union
(* TODO: guest handle for above struct? *)

end
