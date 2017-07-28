subsection \<open>Paravirtualization stuff\<close>

theory paravirt
imports
  "../helpers"
begin

subsubsection \<open>Paravirt enabled\<close>
text \<open>@{text machine_to_phys_mapping} and @{text phys_to_machine_mapping} are global arrays of some
sort.\<close>
abbreviation mfn_to_pfn :: "(nat list, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr" where
  "mfn_to_pfn machine_to_phys_mapping mfn \<equiv> machine_to_phys_mapping\<lparr>mfn\<rparr>\<^sub>u"

abbreviation pfn_to_mfn  :: "(nat list, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr" where
  "pfn_to_mfn phys_to_machine_mapping pfn \<equiv> phys_to_machine_mapping\<lparr>pfn\<rparr>\<^sub>u"

abbreviation "P2M_SHIFT \<equiv> \<guillemotleft>9::nat\<guillemotright>" -- \<open>For x86-64\<close>
abbreviation "P2M_SHIFT' \<equiv> \<guillemotleft>10::nat\<guillemotright>" -- \<open>For others; currently unused for verification\<close>

abbreviation "P2M_ENTRIES \<equiv> 1 \<lless>\<^bsub>u/SIZEOF_LONG\<^esub> P2M_SHIFT" -- \<open>1UL in source, so ulong\<close>
abbreviation "P2M_MASK \<equiv> P2M_ENTRIES - 1"
abbreviation "L1_P2M_SHIFT \<equiv> P2M_SHIFT"
abbreviation "L2_P2M_SHIFT \<equiv> 2 * P2M_SHIFT"
abbreviation "L3_P2M_SHIFT \<equiv> 3 * P2M_SHIFT"
abbreviation "L1_P2M_IDX pfn \<equiv> pfn \<and>\<^sub>b\<^sub>u P2M_MASK"
abbreviation "L2_P2M_IDX pfn \<equiv> (pfn \<ggreater>\<^bsub>u/SIZEOF_LONG\<^esub> L1_P2M_SHIFT) \<and>\<^sub>b\<^sub>u P2M_MASK"
abbreviation "L3_P2M_IDX pfn \<equiv> (pfn \<ggreater>\<^bsub>u/SIZEOF_LONG\<^esub> L2_P2M_SHIFT) \<and>\<^sub>b\<^sub>u P2M_MASK"
abbreviation "INVALID_P2M_ENTRY \<equiv> \<not>\<^bsub>u/SIZEOF_LONG\<^esub> 0" -- \<open>~0UL in source\<close>

(* functions that are merely declared in paravirt.h:
void p2m_chk_pfn(unsigned long pfn);
void arch_init_p2m(unsigned long max_pfn_p);
*)

definition "p2m_pages pages = (pages + P2M_ENTRIES - 1) \<ggreater>\<^bsub>u/SIZEOF_LONG\<^esub> L1_P2M_SHIFT"

subsubsection \<open>Paravirt disabled\<close>

abbreviation mfn_to_pfn' :: "(nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr" where
  "mfn_to_pfn' mfn \<equiv> mfn"

abbreviation pfn_to_mfn' :: "(nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr" where
  "pfn_to_mfn' pfn \<equiv> pfn"

definition "arch_init_p2m max_pfn_p = SKIP\<^sub>A\<^sub>B\<^sub>R"

subsubsection \<open>Both paravirt and ballooning enabled\<close>

(* functions merely declared:
void arch_remap_p2m(unsigned long max_pfn);
int arch_expand_p2m(unsigned long max_pfn);
*)

subsubsection \<open>Paravirt or ballooning disabled\<close>

definition "arch_remap_p2m max_pfn = SKIP\<^sub>A\<^sub>B\<^sub>R"
definition "arch_expand_p2m max_pfn = \<guillemotleft>0::int\<guillemotright>"

end