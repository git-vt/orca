subsection \<open>Xen stuff for x86\_64\<close>

theory "xen-x86_64"
imports
  "../../../helpers"
begin

subsubsection \<open>64-bit segment selectors\<close>
text \<open>From the header file: "These flat segments are in the Xen-private section of every GDT. Since
these are also present in the initial GDT, many OSes will be able to avoid installing their own
GDT."\<close>
abbreviation "FLAT_RING3_CS32 \<equiv> \<guillemotleft>0xe023::nat\<guillemotright>" -- \<open>GDT index 260\<close>
abbreviation "FLAT_RING3_CS64 \<equiv> \<guillemotleft>0xe033::nat\<guillemotright>" -- \<open>GDT index 261\<close>
abbreviation "FLAT_RING3_DS32 \<equiv> \<guillemotleft>0xe02b::nat\<guillemotright>" -- \<open>GDT index 262\<close>
abbreviation "FLAT_RING3_DS64 \<equiv> \<guillemotleft>0x0000::nat\<guillemotright>" -- \<open>NULL selector\<close>
abbreviation "FLAT_RING3_SS32 \<equiv> \<guillemotleft>0xe02b::nat\<guillemotright>" -- \<open>GDT index 262\<close>
abbreviation "FLAT_RING3_SS64 \<equiv> \<guillemotleft>0xe02b::nat\<guillemotright>" -- \<open>GDT index 262\<close>

abbreviation "FLAT_KERNEL_DS64 \<equiv> FLAT_RING3_DS64"
abbreviation "FLAT_KERNEL_DS32 \<equiv> FLAT_RING3_DS32"
abbreviation "FLAT_KERNEL_DS   \<equiv> FLAT_KERNEL_DS64"
abbreviation "FLAT_KERNEL_CS64 \<equiv> FLAT_RING3_CS64"
abbreviation "FLAT_KERNEL_CS32 \<equiv> FLAT_RING3_CS32"
abbreviation "FLAT_KERNEL_CS   \<equiv> FLAT_KERNEL_CS64"
abbreviation "FLAT_KERNEL_SS64 \<equiv> FLAT_RING3_SS64"
abbreviation "FLAT_KERNEL_SS32 \<equiv> FLAT_RING3_SS32"
abbreviation "FLAT_KERNEL_SS   \<equiv> FLAT_KERNEL_SS64"

abbreviation "FLAT_USER_DS64 \<equiv> FLAT_RING3_DS64"
abbreviation "FLAT_USER_DS32 \<equiv> FLAT_RING3_DS32"
abbreviation "FLAT_USER_DS   \<equiv> FLAT_USER_DS64"
abbreviation "FLAT_USER_CS64 \<equiv> FLAT_RING3_CS64"
abbreviation "FLAT_USER_CS32 \<equiv> FLAT_RING3_CS32"
abbreviation "FLAT_USER_CS   \<equiv> FLAT_USER_CS64"
abbreviation "FLAT_USER_SS64 \<equiv> FLAT_RING3_SS64"
abbreviation "FLAT_USER_SS32 \<equiv> FLAT_RING3_SS32"
abbreviation "FLAT_USER_SS   \<equiv> FLAT_USER_SS64"

subsubsection \<open>Assuming \texttt{CONFIG\_PARAVIRT}\<close>
abbreviation "HYPERVISOR_VIRT_START'' \<equiv> \<guillemotleft>0xFFFF800000000000::nat\<guillemotright>"
abbreviation "HYPERVISOR_VIRT_END''   \<equiv> \<guillemotleft>0xFFFF880000000000::nat\<guillemotright>"
abbreviation "MACH2PHYS_VIRT_START''  \<equiv> \<guillemotleft>0xFFFF800000000000::nat\<guillemotright>"
abbreviation "MACH2PHYS_VIRT_END''    \<equiv> \<guillemotleft>0xFFFF804000000000::nat\<guillemotright>"

subsubsection \<open>Assuming \texttt{HYPERVISOR\_VIRT\_START}\<close>
abbreviation "HYPERVISOR_VIRT_START \<equiv> HYPERVISOR_VIRT_START''"
abbreviation "HYPERVISOR_VIRT_END   \<equiv> HYPERVISOR_VIRT_END''"

subsubsection \<open>Continuing from the above\<close>
abbreviation "MACH2PHYS_VIRT_START \<equiv> MACH2PHYS_VIRT_START''"
abbreviation "MACH2PHYS_VIRT_END   \<equiv> MACH2PHYS_VIRT_END''"
abbreviation "MACH2PHYS_NR_ENTRIES \<equiv> (MACH2PHYS_VIRT_END-MACH2PHYS_VIRT_START) \<ggreater>\<^bsub>u/SIZEOF_LONG\<^esub> 3"

text \<open>Assuming \texttt{machine\_to\_phys\_mapping} is defined.\<close>

subsubsection \<open>Segment bases\<close>
abbreviation "SEGBASE_FS          \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "SEGBASE_GS_USER     \<equiv> \<guillemotleft>1::nat\<guillemotright>"
abbreviation "SEGBASE_GS_KERNEL   \<equiv> \<guillemotleft>2::nat\<guillemotright>"
abbreviation "SEGBASE_GS_USER_SEL \<equiv> \<guillemotleft>3::nat\<guillemotright>" -- \<open>Set user \texttt{%gs} specified in \texttt{base[15:0]}\<close>

subsubsection \<open>Syscall bits\<close>
abbreviation "VGCF_in_syscall' \<equiv> \<guillemotleft>8::nat\<guillemotright>"
abbreviation "VGCF_in_syscall  \<equiv> 1 \<lless>\<^bsub>u/SIZEOF_LONG\<^esub> VGCF_in_syscall'"
abbreviation "VGCF_IN_SYSCALL  \<equiv> VGCF_in_syscall"

subsubsection \<open>Stack and CPU status\<close>
text \<open>Top of stack (\texttt{%rsp} at point of hypercall).\<close>
record iret_context_t =
  rax :: nat -- 64
  r11 :: nat -- 64
  rcx :: nat -- 64
  flags :: nat -- 64
  rip :: nat -- 64
  cs :: nat -- 64
  rflags :: nat -- 64
  rsp :: nat -- 64
  ss :: nat -- 64
text \<open>Bottom of \texttt{iret} stack frame.\<close>

(* TODO: __DECL_REG union define; maybe go with non-gcc version where it's just the name? *)

record cpu_user_regs =
  r15 :: nat -- 64
  r14 :: nat -- 64
  r13 :: nat -- 64
  r12 :: nat -- 64
  bp
  bx
  r11 :: nat -- 64
  r10 :: nat -- 64
  r9 :: nat -- 64
  r8 :: nat -- 64
  ax
  cx
  dx
  si
  di
  error_code :: nat -- \<open>32; private\<close>
  entry_vector :: nat -- \<open>32; private\<close>
  ip
  cs :: nat -- 16
  pad0' :: "nat list" -- \<open>16[1]\<close>
  saved_upcall_mask :: nat -- 8
  pad1' :: "nat list" -- \<open>8[3]\<close>
  flags -- \<open>\texttt{rflags.IF == !saved\_upcall\_mask}\<close>
  sp
  ss :: nat -- 16
  pad2' :: "nat list" -- \<open>16[3]\<close>
  es :: nat -- 16
  pad3' :: "nat list" -- \<open>16[3]\<close>
  ds :: nat -- 16
  pad4' :: "nat list" -- \<open>16[3]\<close>
  fs :: nat -- \<open>16; non-zero @{text \<Rightarrow>} takes precedence over fs_base.\<close>
  pad5' :: "nat list" -- \<open>16[3]\<close>
  gs :: nat -- \<open>16; non-zero @{text \<Rightarrow>} takes precedence over gs_base_usr.\<close>
  pad6' :: "nat list" -- \<open>16[3]\<close>

abbreviation "xen_pfn_to_cr3 pfn \<equiv> pfn \<lless>\<^bsub>u/SIZEOF_LONG\<^esub> 12"
abbreviation "xen_cr3_to_pfn cr3 \<equiv> cr3 \<ggreater>\<^bsub>u/SIZEOF_LONG\<^esub> 12"

record arch_vcpu_info_t =
  cr2 :: nat -- 64
  pad :: nat -- \<open>64; \texttt{sizeof(vcpu\_info\_t)} == 64\<close>

type_synonym xen_callback_t = nat -- 64

end
