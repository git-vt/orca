subsection \<open>Xen stuff\<close>

theory xen
imports
  "../../helpers"
  "arch-x86/xen-x86_64"
begin

type_synonym xen_ulong_t = nat -- \<open>\texttt{uint64\_t}/\texttt{unsigned long} (assuming 64-bit)\<close>
abbreviation "SIZEOF_XEN_ULONG_T \<equiv> SIZEOF_LONG"

type_synonym xen_pfn_t = nat -- \<open>\texttt{uint64\_t}/\texttt{unsigned long} (assuming 64-bit)\<close>
abbreviation "SIZEOF_XEN_PFN_T \<equiv> SIZEOF_LONG"

(* TODO: arch-specific stuff? *)
(* TODO: guest handles for primitive C types? Based on arch-x86 xen.h, a guest handle is a struct
that contains a pointer (it used to be just the pointer directly). *)

subsubsection \<open>Hypercalls\<close>
text \<open>\texttt{hypercall\_num} enum\<close>
abbreviation "HYPERVISOR_set_trap_table''                \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "HYPERVISOR_mmu_update''                    \<equiv> \<guillemotleft>1::nat\<guillemotright>"
abbreviation "HYPERVISOR_set_gdt''                       \<equiv> \<guillemotleft>2::nat\<guillemotright>"
abbreviation "HYPERVISOR_stack_switch''                  \<equiv> \<guillemotleft>3::nat\<guillemotright>"
abbreviation "HYPERVISOR_set_callbacks''                 \<equiv> \<guillemotleft>4::nat\<guillemotright>"
abbreviation "HYPERVISOR_fpu_taskswitch''                \<equiv> \<guillemotleft>5::nat\<guillemotright>"
abbreviation "HYPERVISOR_sched_op_compat''               \<equiv> \<guillemotleft>6::nat\<guillemotright>" -- \<open>compat since 0x00030101\<close>
abbreviation "HYPERVISOR_platform_op''                   \<equiv> \<guillemotleft>7::nat\<guillemotright>"
abbreviation "HYPERVISOR_set_debugreg''                  \<equiv> \<guillemotleft>8::nat\<guillemotright>"
abbreviation "HYPERVISOR_get_debugreg''                  \<equiv> \<guillemotleft>9::nat\<guillemotright>"
abbreviation "HYPERVISOR_update_descriptor''             \<equiv> \<guillemotleft>10::nat\<guillemotright>"
abbreviation "HYPERVISOR_memory_op''                     \<equiv> \<guillemotleft>12::nat\<guillemotright>"
abbreviation "HYPERVISOR_multicall''                     \<equiv> \<guillemotleft>13::nat\<guillemotright>"
abbreviation "HYPERVISOR_update_va_mapping''             \<equiv> \<guillemotleft>14::nat\<guillemotright>"
abbreviation "HYPERVISOR_set_timer_op''                  \<equiv> \<guillemotleft>15::nat\<guillemotright>"
abbreviation "HYPERVISOR_event_channel_op_compat''       \<equiv> \<guillemotleft>16::nat\<guillemotright>" -- \<open>compat since 0x00030202\<close>
abbreviation "HYPERVISOR_xen_version''                   \<equiv> \<guillemotleft>17::nat\<guillemotright>"
abbreviation "HYPERVISOR_console_io''                    \<equiv> \<guillemotleft>18::nat\<guillemotright>"
abbreviation "HYPERVISOR_physdev_op_compat''             \<equiv> \<guillemotleft>19::nat\<guillemotright>" -- \<open>compat since 0x00030202\<close>
abbreviation "HYPERVISOR_grant_table_op''                \<equiv> \<guillemotleft>20::nat\<guillemotright>"
abbreviation "HYPERVISOR_vm_assist''                     \<equiv> \<guillemotleft>21::nat\<guillemotright>"
abbreviation "HYPERVISOR_update_va_mapping_otherdomain'' \<equiv> \<guillemotleft>22::nat\<guillemotright>"
abbreviation "HYPERVISOR_iret''                          \<equiv> \<guillemotleft>23::nat\<guillemotright>" -- \<open>x86 only\<close>
abbreviation "HYPERVISOR_vcpu_op''                       \<equiv> \<guillemotleft>24::nat\<guillemotright>"
abbreviation "HYPERVISOR_set_segment_base''              \<equiv> \<guillemotleft>25::nat\<guillemotright>" -- \<open>x86/64 only\<close>
abbreviation "HYPERVISOR_mmuext_op''                     \<equiv> \<guillemotleft>26::nat\<guillemotright>"
abbreviation "HYPERVISOR_xsm_op''                        \<equiv> \<guillemotleft>27::nat\<guillemotright>"
abbreviation "HYPERVISOR_nmi_op''                        \<equiv> \<guillemotleft>28::nat\<guillemotright>"
abbreviation "HYPERVISOR_sched_op''                      \<equiv> \<guillemotleft>29::nat\<guillemotright>"
abbreviation "HYPERVISOR_callback_op''                   \<equiv> \<guillemotleft>30::nat\<guillemotright>"
abbreviation "HYPERVISOR_xenoprof_op''                   \<equiv> \<guillemotleft>31::nat\<guillemotright>"
abbreviation "HYPERVISOR_event_channel_op''              \<equiv> \<guillemotleft>32::nat\<guillemotright>"
abbreviation "HYPERVISOR_physdev_op''                    \<equiv> \<guillemotleft>33::nat\<guillemotright>"
abbreviation "HYPERVISOR_hvm_op''                        \<equiv> \<guillemotleft>34::nat\<guillemotright>"
abbreviation "HYPERVISOR_sysctl''                        \<equiv> \<guillemotleft>35::nat\<guillemotright>"
abbreviation "HYPERVISOR_domctl''                        \<equiv> \<guillemotleft>36::nat\<guillemotright>"
abbreviation "HYPERVISOR_kexec_op''                      \<equiv> \<guillemotleft>37::nat\<guillemotright>"
abbreviation "HYPERVISOR_tmem_op''                       \<equiv> \<guillemotleft>38::nat\<guillemotright>"
abbreviation "HYPERVISOR_xc_reserved_op''                \<equiv> \<guillemotleft>39::nat\<guillemotright>" -- \<open>reserved for XenClient\<close>

text \<open>Architecture-specific hypercall definitions.\<close>
abbreviation "HYPERVISOR_arch_0'' \<equiv> \<guillemotleft>48::nat\<guillemotright>"
abbreviation "HYPERVISOR_arch_1'' \<equiv> \<guillemotleft>49::nat\<guillemotright>"
abbreviation "HYPERVISOR_arch_2'' \<equiv> \<guillemotleft>50::nat\<guillemotright>"
abbreviation "HYPERVISOR_arch_3'' \<equiv> \<guillemotleft>51::nat\<guillemotright>"
abbreviation "HYPERVISOR_arch_4'' \<equiv> \<guillemotleft>52::nat\<guillemotright>"
abbreviation "HYPERVISOR_arch_5'' \<equiv> \<guillemotleft>53::nat\<guillemotright>"
abbreviation "HYPERVISOR_arch_6'' \<equiv> \<guillemotleft>54::nat\<guillemotright>"
abbreviation "HYPERVISOR_arch_7'' \<equiv> \<guillemotleft>55::nat\<guillemotright>"

text \<open>Skipping compatibility of calls with old versions of Xen.\<close>

subsubsection \<open>Virtual Interrupts\<close>
text \<open>\texttt{virq} enum; quoting from the Xen header:

"Virtual interrupts that a guest OS may receive from Xen.

In the side comments, `V.' denotes a per-VCPU VIRQ while `G.' denotes a global VIRQ. The former can
be bound once per VCPU and cannot be re-bound. The latter can be allocated only once per guest: they
must initially be allocated to VCPU0 but can subsequently be re-bound."

Most of the rest of the text that follows is also direct quotes from \texttt{xen.h}.\<close>
abbreviation "VIRQ_TIMER       \<equiv> \<guillemotleft>0::nat\<guillemotright>" --\<open>V. Timebase update, and/or requested timeout.\<close>
abbreviation "VIRQ_DEBUG       \<equiv> \<guillemotleft>1::nat\<guillemotright>" --\<open>V. Request guest to dump debug info.\<close>
abbreviation "VIRQ_CONSOLE     \<equiv> \<guillemotleft>2::nat\<guillemotright>" --\<open>G. (DOM0) Bytes received on emergency console.\<close>
abbreviation "VIRQ_DOM_EXC     \<equiv> \<guillemotleft>3::nat\<guillemotright>" --\<open>G. (DOM0) Exceptional event for some domain.\<close>
abbreviation "VIRQ_TBUF        \<equiv> \<guillemotleft>4::nat\<guillemotright>" --\<open>G. (DOM0) Trace buffer has records available.\<close>
abbreviation "VIRQ_DEBUGGER    \<equiv> \<guillemotleft>6::nat\<guillemotright>" --\<open>G. (DOM0) A domain has paused for debugging.\<close>
abbreviation "VIRQ_XENOPROF    \<equiv> \<guillemotleft>7::nat\<guillemotright>" --\<open>V. XenOprofile interrupt: new sample available\<close>
abbreviation "VIRQ_CON_RING    \<equiv> \<guillemotleft>8::nat\<guillemotright>" --\<open>G. (DOM0) Bytes received on console\<close>
abbreviation "VIRQ_PCPU_STATE  \<equiv> \<guillemotleft>9::nat\<guillemotright>" --\<open>G. (DOM0) PCPU state changed\<close>
abbreviation "VIRQ_MEM_EVENT   \<equiv> \<guillemotleft>10::nat\<guillemotright>" --\<open>G. (DOM0) A memory event has occurred\<close>
abbreviation "VIRQ_XC_RESERVED \<equiv> \<guillemotleft>11::nat\<guillemotright>" --\<open>G. Reserved for XenClient\<close>
abbreviation "VIRQ_ENOMEM      \<equiv> \<guillemotleft>12::nat\<guillemotright>" --\<open>G. (DOM0) Low on heap memory\<close>

text \<open>Architecture-specific VIRQ definitions.\<close>
abbreviation "VIRQ_ARCH_0 \<equiv> \<guillemotleft>16::nat\<guillemotright>"
abbreviation "VIRQ_ARCH_1 \<equiv> \<guillemotleft>17::nat\<guillemotright>"
abbreviation "VIRQ_ARCH_2 \<equiv> \<guillemotleft>18::nat\<guillemotright>"
abbreviation "VIRQ_ARCH_3 \<equiv> \<guillemotleft>19::nat\<guillemotright>"
abbreviation "VIRQ_ARCH_4 \<equiv> \<guillemotleft>20::nat\<guillemotright>"
abbreviation "VIRQ_ARCH_5 \<equiv> \<guillemotleft>21::nat\<guillemotright>"
abbreviation "VIRQ_ARCH_6 \<equiv> \<guillemotleft>22::nat\<guillemotright>"
abbreviation "VIRQ_ARCH_7 \<equiv> \<guillemotleft>23::nat\<guillemotright>"
abbreviation "NR_VIRQS    \<equiv> \<guillemotleft>24::nat\<guillemotright>"

subsubsection \<open>\texttt{HYPERVISOR\_mmu\_update}\<close>
text \<open>Skipping all the flags detail.\<close>
abbreviation "MMU_NORMAL_PT_UPDATE      \<equiv> \<guillemotleft>0::nat\<guillemotright>" -- \<open>checked '*ptr = val'. ptr is MA.\<close>
abbreviation "MMU_MACHPHYS_UPDATE       \<equiv> \<guillemotleft>1::nat\<guillemotright>" -- \<open>ptr = MA of frame to modify entry for\<close>
abbreviation "MMU_PT_UPDATE_PRESERVE_AD \<equiv> \<guillemotleft>2::nat\<guillemotright>" -- \<open>atomically: *ptr = val | (*ptr&(A|D))\<close>

subsubsection \<open>Extended MMU operations\<close>
text \<open>Skipping the descriptions of the below enum (\texttt{mmuext\_cmd}.\<close>
abbreviation "MMUEXT_PIN_L1_TABLE       \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "MMUEXT_PIN_L2_TABLE       \<equiv> \<guillemotleft>1::nat\<guillemotright>"
abbreviation "MMUEXT_PIN_L3_TABLE       \<equiv> \<guillemotleft>2::nat\<guillemotright>"
abbreviation "MMUEXT_PIN_L4_TABLE       \<equiv> \<guillemotleft>3::nat\<guillemotright>"
abbreviation "MMUEXT_UNPIN_TABLE        \<equiv> \<guillemotleft>4::nat\<guillemotright>"
abbreviation "MMUEXT_NEW_BASEPTR        \<equiv> \<guillemotleft>5::nat\<guillemotright>"
abbreviation "MMUEXT_TLB_FLUSH_LOCAL    \<equiv> \<guillemotleft>6::nat\<guillemotright>"
abbreviation "MMUEXT_INVLPG_LOCAL       \<equiv> \<guillemotleft>7::nat\<guillemotright>"
abbreviation "MMUEXT_TLB_FLUSH_MULTI    \<equiv> \<guillemotleft>8::nat\<guillemotright>"
abbreviation "MMUEXT_INVLPG_MULTI       \<equiv> \<guillemotleft>9::nat\<guillemotright>"
abbreviation "MMUEXT_TLB_FLUSH_ALL      \<equiv> \<guillemotleft>10::nat\<guillemotright>"
abbreviation "MMUEXT_INVLPG_ALL         \<equiv> \<guillemotleft>11::nat\<guillemotright>"
abbreviation "MMUEXT_FLUSH_CACHE        \<equiv> \<guillemotleft>12::nat\<guillemotright>"
abbreviation "MMUEXT_SET_LDT            \<equiv> \<guillemotleft>13::nat\<guillemotright>"
abbreviation "MMUEXT_NEW_USER_BASEPTR   \<equiv> \<guillemotleft>15::nat\<guillemotright>"
abbreviation "MMUEXT_CLEAR_PAGE         \<equiv> \<guillemotleft>16::nat\<guillemotright>"
abbreviation "MMUEXT_COPY_PAGE          \<equiv> \<guillemotleft>17::nat\<guillemotright>"
abbreviation "MMUEXT_FLUSH_CACHE_GLOBAL \<equiv> \<guillemotleft>18::nat\<guillemotright>"
abbreviation "MMUEXT_MARK_SUPER         \<equiv> \<guillemotleft>19::nat\<guillemotright>"
abbreviation "MMUEXT_UNMARK_SUPER       \<equiv> \<guillemotleft>20::nat\<guillemotright>"

record mmuext_op_t =
  cmd :: nat -- \<open>32; enum mmuext_cmd\<close>
  union ...

subsubsection \<open>Miscellaneous defines\<close>
text \<open>\texttt{uvm\_flags} enum (\texttt{update\_va\_mapping} flags)\<close>
abbreviation "UVMF_NONE           \<equiv> \<guillemotleft>0b000::nat\<guillemotright>" -- \<open>No flushing at all.\<close>
abbreviation "UVMF_TLB_FLUSH      \<equiv> \<guillemotleft>0b001::nat\<guillemotright>" -- \<open>Flush entire TLB(s).\<close>
abbreviation "UVMF_INVLPG         \<equiv> \<guillemotleft>0b010::nat\<guillemotright>" -- \<open>Flush only one entry.\<close>
abbreviation "UVMF_FLUSHTYPE_MASK \<equiv> \<guillemotleft>0b011::nat\<guillemotright>"
abbreviation "UVMF_MULTI          \<equiv> \<guillemotleft>0b000::nat\<guillemotright>" -- \<open>Flush subset of TLBs.\<close>
abbreviation "UVMF_LOCAL          \<equiv> \<guillemotleft>0b000::nat\<guillemotright>" -- \<open>Flush local TLB.\<close>
abbreviation "UVMF_ALL            \<equiv> \<guillemotleft>0b100::nat\<guillemotright>" -- \<open>Flush all TLBs.\<close>

text \<open>Commands to \texttt{HYPERVISOR\_console\_io()}.\<close>
abbreviation "CONSOLEIO_write \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "CONSOLEIO_read  \<equiv> \<guillemotleft>1::nat\<guillemotright>"

text \<open>Commands to \texttt{HYPERVISOR\_vm\_assist()}.\<close>
abbreviation "VMASST_CMD_enable  \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "VMASST_CMD_disable \<equiv> \<guillemotleft>1::nat\<guillemotright>"

text \<open>x86/32 guests: simulate full 4GB segment limits.\<close>
abbreviation "VMASST_TYPE_4gb_segments \<equiv> \<guillemotleft>0::nat\<guillemotright>"

text \<open>x86/32 guests: trap (vector 15) whenever above vmassist is used.\<close>
abbreviation "VMASST_TYPE_4gb_segments_notify \<equiv> \<guillemotleft>1::nat\<guillemotright>"

text \<open>x86 guests: support writes to bottom-level PTEs.
NB1. Page-directory entries cannot be written.
NB2. Guest must continue to remove all writable mappings of PTEs.\<close>
abbreviation "VMASST_TYPE_writable_pagetables \<equiv> \<guillemotleft>2::nat\<guillemotright>"

text \<open>x86/PAE guests: support PDPTs above 4GB.\<close>
abbreviation "VMASST_TYPE_pae_extended_cr3 \<equiv> \<guillemotleft>3::nat\<guillemotright>"
abbreviation "MAX_VMASST_TYPE \<equiv> \<guillemotleft>3::nat\<guillemotright>"

subsubsection \<open>Domain IDs\<close>

type_synonym domid_t = nat -- uint16

abbreviation "DOMID_FIRST_RESERVED \<equiv> \<guillemotleft>0x7FF0::nat\<guillemotright>"
text \<open>Domain ids \<ge> @{const DOMID_FIRST_RESERVED} cannot be used for ordinary domains.\<close>

abbreviation "DOMID_SELF \<equiv> \<guillemotleft>0x7FF0::nat\<guillemotright>"
text \<open>@{const DOMID_SELF} is used in certain contexts to refer to oneself.\<close>

abbreviation "DOMID_IO \<equiv> \<guillemotleft>0x7FF1::nat\<guillemotright>"
text \<open>@{const DOMID_IO} is used to restrict page-table updates to mapping I/O memory. Although no
Foreign Domain need be specified to map I/O pages, @{const DOMID_IO} is useful to ensure that no
mappings to the OS's own heap are accidentally installed. (e.g., in Linux this could cause havoc as
reference counts aren't adjusted on the I/O-mapping code path). This only makes sense in
\texttt{MMUEXT\_SET\_FOREIGNDOM} (which doesn't seem to be defined in \texttt{xen.h}, but in that
context can be specified by any calling domain.\<close>

abbreviation "DOMID_XEN \<equiv> \<guillemotleft>0x7FF2::nat\<guillemotright>"
text \<open>@{const DOMID_XEN} is used to allow privileged domains to map restricted parts of Xen's heap
space (e.g., the \texttt{machine\_to\_phys} table). This only makes sense in
\texttt{MMUEXT\_SET\_FOREIGNDOM}, and is only permitted if the caller is privileged.\<close>

abbreviation "DOMID_COW \<equiv> \<guillemotleft>0x7FF3::nat\<guillemotright>"
text \<open>@{const DOMID_COW} is used as the owner of sharable pages\<close>

abbreviation "DOMID_INVALID \<equiv> \<guillemotleft>0x7FF4::nat\<guillemotright>"
text \<open>@{const DOMID_INVALID} is used to identify pages with unknown owner.\<close>

abbreviation "DOMID_IDLE \<equiv> \<guillemotleft>0x7FFF::nat\<guillemotright>"
text \<open>@{const DOMID_IDLE} identifies idle domains.\<close>

subsubsection \<open>More stuff\<close>

record multicall_entry_t =
  op :: xen_ulong_t
  result :: xen_ulong_t
  args :: "xen_ulong_t list" -- \<open>[6]\<close>

(* TODO: DEFINE_XEN_GUEST_HANDLE(multicall_entry_t); ? *)

text \<open>Updates to the following values are preceded and followed by an  increment of
\texttt{version}. The guest can therefore detect updates by looking for changes to \texttt{version}.
If the least-significant bit of the version number is set then an update is in progress and the
guest must wait to read a consistent set of values. The correct way to interact with the version
number is similar to Linux's seqlock: see the implementations of
\texttt{read\_seqbegin}/\texttt{read\_seqretry}.

Current system time:
  system_time +
  ((((tsc - tsc_timestamp) << tsc_shift) * tsc_to_system_mul) >> 32)
CPU frequency (Hz):
  ((10^9 << 32) / tsc_to_system_mul) >> tsc_shift\<close>
record vcpu_time_info_t =
  version :: nat -- 32
  pad0 :: nat -- 32
  tsc_timestamp :: nat -- \<open>64, TSC at last update of time vals.\<close>
  system_time :: nat -- \<open>64, Time, in nanosecs, since boot.\<close>
  tsc_to_system_mul :: nat -- 32
  tsc_shift :: nat -- \<open>8; signed in source, but must be unsigned for use with shift operator here\<close>
  pad1 :: "int list" -- \<open>8[3]\<close>

record vcpu_info_t =
  evtchn_upcall_pending :: nat -- 8
  evtchn_upcall_mask :: nat -- \<open>8; assuming \texttt{XEN\_HAVE\_PV\_UPCALL\_MASK}\<close>
  evtchn_pending_sel :: xen_ulong_t
  arch :: arch_vcpu_info_t
  time :: vcpu_time_info_t
text \<open>Skipping the detail of @{typ vcpu_info_t}.\<close>

record shared_info_t =
  vcpu_info :: "vcpu_info_t list" -- \<open>[XEN_LEGACY_MAX_VCPUS]\<close>
  evtchn_pending :: "xen_ulong_t list" -- \<open>[sizeof(xen_ulong_t) * 8]\<close>
  evtchn_mask :: "xen_ulong_t list" -- \<open>[sizeof(xen_ulong_t) * 8]\<close>
  (* Wallclock time; for guest usage. *)
  wc_version :: nat -- \<open>32; Version counter: see vcpu_time_info_t.\<close>
  wc_sec :: nat -- \<open>32;  Secs  00:00:00 UTC, Jan 1, 1970.\<close>
  wc_nsec :: nat -- \<open>32; Nsecs 00:00:00 UTC, Jan 1, 1970.\<close>
  arch :: arch_shared_info_t
text \<open>Skipping the detail of @{typ shared_info_t}.\<close>

text \<open>Everything before \texttt{pt\_base} is filled in both on initial boot and on resume.
\texttt{pt\_base} and everything after will only be filled in on initial boot.\<close>
abbreviation "MAX_GUEST_CMDLINE \<equiv> \<guillemotleft>1024::nat\<guillemotright>"
record start_info_t =
  magic :: "char list" -- \<open>[32]; "xen-<version>-<platform>".\<close>
  nr_pages :: nat -- \<open>64; Total pages allocated to this domain.\<close>
  shared_info :: nat -- \<open>64; MACHINE address of shared info struct.\<close>
  flags :: nat -- \<open>32; SIF_xxx flags.\<close>
  store_mfn :: xen_pfn_t -- \<open>MACHINE page number of shared page.\<close>
  store_evtchn :: nat -- \<open>32; Event channel for store communication.\<close>
  (* TODO: union of structs *)
  pt_base :: nat -- \<open>64; VIRTUAL address of page directory.\<close>
  nr_pt_frames :: nat -- \<open>64; Number of bootstrap p.t. frames.\<close>
  mfn_list :: nat -- \<open>64; VIRTUAL address of page-frame list.\<close>
  mod_start :: nat -- \<open>64; VIRTUAL address of pre-loaded module (PFN of pre-loaded module if
                       \texttt{SIF\_MOD\_START\_PFN} set in flags).\<close>
  mod_len :: nat -- \<open>64; Size (bytes) of pre-loaded module.\<close>
  cmd_line :: "int list" -- \<open>8[MAX_GUEST_CMDLINE]; shouldn't these just be chars?\<close>
  -- \<open>The pfn range here covers both page table and \texttt{p->m} table frames.\<close>
  first_p2m_pfn :: nat -- \<open>64; 1st pfn forming initial \texttt{P->M} table.\<close>
  nr_p2m_frames :: nat -- \<open>64; # of pfns forming initial \texttt{P->M} table.\<close>
text \<open>Skipping the detail of @{typ start_info_t}.\<close>

text \<open>These flags are passed in the 'flags' field of @{typ start_info_t}.\<close>
abbreviation "SIF_PRIVILEGED    \<equiv> \<guillemotleft>0b0001::nat\<guillemotright>" -- \<open>Is the domain privileged?\<close>
abbreviation "SIF_INITDOMAIN    \<equiv> \<guillemotleft>0b0010::nat\<guillemotright>" -- \<open>Is this the initial control domain?\<close>
abbreviation "SIF_MULTIBOOT_MOD \<equiv> \<guillemotleft>0b0100::nat\<guillemotright>" -- \<open>Is mod_start a multiboot module?\<close>
abbreviation "SIF_MOD_START_PFN \<equiv> \<guillemotleft>0b1000::nat\<guillemotright>" -- \<open>Is mod_start a PFN?\<close>
abbreviation "SIF_PM_MASK       \<equiv> \<guillemotleft>0xFF00::nat\<guillemotright>" -- \<open>reserve 1 byte for xen-pm options\<close>

record xen_multiboot_mod_list_t =
  mod_start :: nat -- \<open>32; Address of first byte of the module\<close>
  mod_end :: nat -- \<open>32; Address of last byte of the module (inclusive)\<close>
  cmdline :: nat -- \<open>32; Address of zero-terminated command line\<close>
  pad :: nat -- \<open>32; Unused, must be zero\<close>
text \<open>Skipping the detail of @{typ xen_multiboot_mod_list_t}.\<close>

subsubsection \<open>VGA/VESA Consoles\<close>
abbreviation "XEN_VGATYPE_TEXT_MODE_3 \<equiv> \<guillemotleft>0x03::nat\<guillemotright>"
abbreviation "XEN_VGATYPE_VESA_LFB    \<equiv> \<guillemotleft>0x23::nat\<guillemotright>"
abbreviation "XEN_VGATYPE_EFI_LFB     \<equiv> \<guillemotleft>0x70::nat\<guillemotright>"

record dom0_vga_console_info_t =
  video_type :: nat -- \<open>8; \texttt{DOM0\_VGA\_CONSOLE\_???}\<close>
  union \<dots>

type_synonym xen_vga_console_info_t = dom0_vga_console_info_t

type_synonym xen_domain_handle_t = "nat list" -- \<open>uint8_t[16]\<close>

end
