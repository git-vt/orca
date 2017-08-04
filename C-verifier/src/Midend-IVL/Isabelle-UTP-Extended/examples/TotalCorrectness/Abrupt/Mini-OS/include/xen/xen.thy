subsection \<open>Xen stuff\<close>

theory xen
imports
  "../../helpers"
begin

(* TODO: guest handles for primitive C types? *)

subsubsection \<open>Hypercalls\<close>

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
text \<open>Quoting from the Xen header:

"Virtual interrupts that a guest OS may receive from Xen.

In the side comments, `V.' denotes a per-VCPU VIRQ while `G.' denotes a global VIRQ. The former can
be bound once per VCPU and cannot be re-bound. The latter can be allocated only once per guest: they
must initially be allocated to VCPU0 but can subsequently be re-bound."\<close>
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

text \<open>Skipping all the info about HYPERVISOR_mmu_update flags\dots\<close>

abbreviation "MMU_NORMAL_PT_UPDATE      \<equiv> \<guillemotleft>0::nat\<guillemotright>" -- \<open>checked '*ptr = val'. ptr is MA.\<close>
abbreviation "MMU_MACHPHYS_UPDATE       \<equiv> \<guillemotleft>1::nat\<guillemotright>" -- \<open>ptr = MA of frame to modify entry for\<close>
abbreviation "MMU_PT_UPDATE_PRESERVE_AD \<equiv> \<guillemotleft>2::nat\<guillemotright>" -- \<open>atomically: *ptr = val | (*ptr&(A|D))\<close>

end
