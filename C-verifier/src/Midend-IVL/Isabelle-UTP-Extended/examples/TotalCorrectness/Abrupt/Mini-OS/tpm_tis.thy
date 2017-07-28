subsection \<open>Derivations from Linux's \texttt{drivers/char/tpm.c}\<close>

theory tpm_tis
imports
  "include/byteorder"
(*   helpers *)
begin

subsubsection \<open>From header file \texttt{tpm_tis.h}\<close>

text \<open>Bare numeric literals are (possibly signed) integers in C, and usually compilers try to fit
the value in a larger type if regular \texttt{int} is too small.\<close>

abbreviation "TPM_TIS_EN_LOCL0 \<equiv> \<guillemotleft>0b00001::nat\<guillemotright>" -- \<open>1 << 0\<close>
abbreviation "TPM_TIS_EN_LOCL1 \<equiv> \<guillemotleft>0b00010::nat\<guillemotright>" -- \<open>1 << 1\<close>
abbreviation "TPM_TIS_EN_LOCL2 \<equiv> \<guillemotleft>0b00100::nat\<guillemotright>" -- \<open>1 << 2\<close>
abbreviation "TPM_TIS_EN_LOCL3 \<equiv> \<guillemotleft>0b01000::nat\<guillemotright>" -- \<open>1 << 3\<close>
abbreviation "TPM_TIS_EN_LOCL4 \<equiv> \<guillemotleft>0b10000::nat\<guillemotright>" -- \<open>1 << 4\<close>
abbreviation "TPM_TIS_EN_LOCLALL \<equiv>
  TPM_TIS_EN_LOCL0 \<or>\<^sub>b\<^sub>u
  TPM_TIS_EN_LOCL1 \<or>\<^sub>b\<^sub>u
  TPM_TIS_EN_LOCL2 \<or>\<^sub>b\<^sub>u
  TPM_TIS_EN_LOCL3 \<or>\<^sub>b\<^sub>u
  TPM_TIS_EN_LOCL4"
abbreviation "TPM_BASEADDR \<equiv> \<guillemotleft>0xFED40000::nat\<guillemotright>"
abbreviation "TPM_PROBE_IRQ \<equiv> \<guillemotleft>0xFFFF::nat\<guillemotright>"
abbreviation "TPM_TIS_LOCL_INT_TO_FLAG x \<equiv> 1 \<lless>\<^bsub>u/\<guillemotleft>32::nat\<guillemotright>\<^esub> x"

subsubsection \<open>From source file \texttt{tpm\_tis.c}\<close>

text \<open>The source file provides a backup definition of \texttt{min}, but we can just use @{text
min\<^sub>u}.\<close>

text \<open>@{text timeout_no} not used here as we're leaving out the printk statements.\<close>
abbreviation "ADJUST_TIMEOUTS_TO_STANDARD initial standard timeout_no \<equiv>
  bif &initial <\<^sub>u &standard then
    initial \<Midarrow> &standard
  else
    II
  eif"

abbreviation "TPM_HEADER_SIZE \<equiv> \<guillemotleft>10::nat\<guillemotright>"
abbreviation "TPM_BUFSIZE \<equiv> \<guillemotleft>2048::nat\<guillemotright>"

(* TODO: structs! They're all packed, too. *)

text \<open>The following values are encoded in a single enum, \texttt{tpm\_duration}, in
\texttt{tpm\_tis.c}, but the enum itself is never used again (the values are only stored in unsigned
integers) so there's no need for enum support for this portion of the code.\<close>
abbreviation "TPM_SHORT \<equiv> \<guillemotleft>0::nat\<guillemotright>"
abbreviation "TPM_MEDIUM \<equiv> \<guillemotleft>1::nat\<guillemotright>"
abbreviation "TPM_LONG \<equiv> \<guillemotleft>2::nat\<guillemotright>"
abbreviation "TPM_UNDEFINED \<equiv> \<guillemotleft>3::nat\<guillemotright>"

text \<open>The first two of these abbreviations defines the size of the later external-linkage global
constant lists (arrays).\<close>
abbreviation "TPM_MAX_PROTECTED_ORDINAL \<equiv> \<guillemotleft>12::nat\<guillemotright>"
abbreviation "TPM_MAX_ORDINAL \<equiv> \<guillemotleft>0xF3::nat\<guillemotright>"
abbreviation "TPM_PROTECTED_ORDINAL_MASK \<equiv> \<guillemotleft>0xFF::nat\<guillemotright>"

abbreviation "TPM_DIGEST_SIZE \<equiv> \<guillemotleft>20::nat\<guillemotright>"
abbreviation "TPM_ERROR_SIZE \<equiv> \<guillemotleft>10::nat\<guillemotright>"

abbreviation "TPM_RET_CODE_IDX \<equiv> \<guillemotleft>6::nat\<guillemotright>"

text \<open>@{text tmp_capabilities}\<close>
abbreviation "TPM_CAP_FLAG \<equiv> cpu_to_be32 4"
abbreviation "TPM_CAP_PROP \<equiv> cpu_to_be32 5"
abbreviation "CAP_VERSION_1_1 \<equiv> cpu_to_be32 6"
abbreviation "CAP_VERSION_1_2 \<equiv> cpu_to_be32 0x1A"

text \<open>@{text tpm_sub_capabilities}\<close>
abbreviation "TPM_CAP_PROP_PCR \<equiv> cpu_to_be32 0x101"
abbreviation "TPM_CAP_PROP_MANUFACTURER \<equiv> cpu_to_be32 0x103"
abbreviation "TPM_CAP_FLAG_PERM \<equiv> cpu_to_be32 0x108"
abbreviation "TPM_CAP_FLAG_VOL \<equiv> cpu_to_be32 0x109"
abbreviation "TPM_CAP_PROP_OWNER \<equiv> cpu_to_be32 0x111"
abbreviation "TPM_CAP_PROP_TIS_TIMEOUT \<equiv> cpu_to_be32 0x115"
abbreviation "TPM_CAP_PROP_TIS_DURATION \<equiv> cpu_to_be32 0x120"

abbreviation "TPM_INTERNAL_RESULT_SIZE \<equiv> 200"
abbreviation "TPM_TAG_RQU_COMMAND \<equiv> cpu_to_be16 0xC1"
abbreviation "TPM_ORD_GET_CAP \<equiv> cpu_to_be32 0x65"

paragraph \<open>Constant arrays\<close>

definition "tpm_protected_ordinal_duration = \<langle>
  TPM_UNDEFINED,          (* 0 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,          (* 5 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_SHORT,              (* 10 *)
  TPM_SHORT
\<rangle>"

definition "tpm_ordinal_duration = \<langle>
  TPM_UNDEFINED,          (* 0 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,          (* 5 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_SHORT,              (* 10 *)
  TPM_SHORT,
  TPM_MEDIUM,
  TPM_LONG,
  TPM_LONG,
  TPM_MEDIUM,             (* 15 *)
  TPM_SHORT,
  TPM_SHORT,
  TPM_MEDIUM,
  TPM_LONG,
  TPM_SHORT,              (* 20 *)
  TPM_SHORT,
  TPM_MEDIUM,
  TPM_MEDIUM,
  TPM_MEDIUM,
  TPM_SHORT,              (* 25 *)
  TPM_SHORT,
  TPM_MEDIUM,
  TPM_SHORT,
  TPM_SHORT,
  TPM_MEDIUM,             (* 30 *)
  TPM_LONG,
  TPM_MEDIUM,
  TPM_SHORT,
  TPM_SHORT,
  TPM_SHORT,              (* 35 *)
  TPM_MEDIUM,
  TPM_MEDIUM,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_MEDIUM,             (* 40 *)
  TPM_LONG,
  TPM_MEDIUM,
  TPM_SHORT,
  TPM_SHORT,
  TPM_SHORT,              (* 45 *)
  TPM_SHORT,
  TPM_SHORT,
  TPM_SHORT,
  TPM_LONG,
  TPM_MEDIUM,             (* 50 *)
  TPM_MEDIUM,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,          (* 55 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_MEDIUM,             (* 60 *)
  TPM_MEDIUM,
  TPM_MEDIUM,
  TPM_SHORT,
  TPM_SHORT,
  TPM_MEDIUM,             (* 65 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_SHORT,              (* 70 *)
  TPM_SHORT,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,          (* 75 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_LONG,               (* 80 *)
  TPM_UNDEFINED,
  TPM_MEDIUM,
  TPM_LONG,
  TPM_SHORT,
  TPM_UNDEFINED,          (* 85 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_SHORT,              (* 90 *)
  TPM_SHORT,
  TPM_SHORT,
  TPM_SHORT,
  TPM_SHORT,
  TPM_UNDEFINED,          (* 95 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_MEDIUM,             (* 100 *)
  TPM_SHORT,
  TPM_SHORT,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,          (* 105 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_SHORT,              (* 110 *)
  TPM_SHORT,
  TPM_SHORT,
  TPM_SHORT,
  TPM_SHORT,
  TPM_SHORT,              (* 115 *)
  TPM_SHORT,
  TPM_SHORT,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_LONG,               (* 120 *)
  TPM_LONG,
  TPM_MEDIUM,
  TPM_UNDEFINED,
  TPM_SHORT,
  TPM_SHORT,              (* 125 *)
  TPM_SHORT,
  TPM_LONG,
  TPM_SHORT,
  TPM_SHORT,
  TPM_SHORT,              (* 130 *)
  TPM_MEDIUM,
  TPM_UNDEFINED,
  TPM_SHORT,
  TPM_MEDIUM,
  TPM_UNDEFINED,          (* 135 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_SHORT,              (* 140 *)
  TPM_SHORT,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,          (* 145 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_SHORT,              (* 150 *)
  TPM_MEDIUM,
  TPM_MEDIUM,
  TPM_SHORT,
  TPM_SHORT,
  TPM_UNDEFINED,          (* 155 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_SHORT,              (* 160 *)
  TPM_SHORT,
  TPM_SHORT,
  TPM_SHORT,
  TPM_UNDEFINED,
  TPM_UNDEFINED,          (* 165 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_LONG,               (* 170 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,          (* 175 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_MEDIUM,             (* 180 *)
  TPM_SHORT,
  TPM_MEDIUM,
  TPM_MEDIUM,
  TPM_MEDIUM,
  TPM_MEDIUM,             (* 185 *)
  TPM_SHORT,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,          (* 190 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,          (* 195 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_SHORT,              (* 200 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_SHORT,
  TPM_SHORT,              (* 205 *)
  TPM_SHORT,
  TPM_SHORT,
  TPM_SHORT,
  TPM_SHORT,
  TPM_MEDIUM,             (* 210 *)
  TPM_UNDEFINED,
  TPM_MEDIUM,
  TPM_MEDIUM,
  TPM_MEDIUM,
  TPM_UNDEFINED,          (* 215 *)
  TPM_MEDIUM,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_SHORT,
  TPM_SHORT,              (* 220 *)
  TPM_SHORT,
  TPM_SHORT,
  TPM_SHORT,
  TPM_SHORT,
  TPM_UNDEFINED,          (* 225 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_SHORT,              (* 230 *)
  TPM_LONG,
  TPM_MEDIUM,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,          (* 235 *)
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_UNDEFINED,
  TPM_SHORT,              (* 240 *)
  TPM_UNDEFINED,
  TPM_MEDIUM
\<rangle>"

(* TODO: fit in extern const struct tpm_input_header tpm_getcap_header, initialize *)

paragraph \<open>More enums that are never used by type.\<close>
text \<open>\texttt{tis\_access}\<close>
abbreviation "TPM_ACCESS_VALID \<equiv> \<guillemotleft>0x80::nat\<guillemotright>"
abbreviation "TPM_ACCESS_ACTIVE_LOCALITY \<equiv> \<guillemotleft>0x20::nat\<guillemotright>" -- R
abbreviation "TPM_ACCESS_RELINQUISH_LOCALITY \<equiv> \<guillemotleft>0x20::nat\<guillemotright>" -- W
abbreviation "TPM_ACCESS_REQUEST_PENDING \<equiv> \<guillemotleft>0x04::nat\<guillemotright>" -- W
abbreviation "TPM_ACCESS_REQUEST_USE \<equiv> \<guillemotleft>0x02::nat\<guillemotright>" -- W

text \<open>\texttt{tis\_status}\<close>
abbreviation "TPM_STS_VALID \<equiv> \<guillemotleft>0x80::nat\<guillemotright>" -- R
abbreviation "TPM_STS_COMMAND_READY \<equiv> \<guillemotleft>0x40::nat\<guillemotright>" -- R
abbreviation "TPM_STS_DATA_AVAIL \<equiv> \<guillemotleft>0x10::nat\<guillemotright>" -- R
abbreviation "TPM_STS_DATA_EXPECT \<equiv> \<guillemotleft>0x08::nat\<guillemotright>" -- R
abbreviation "TPM_STS_DATA_GO \<equiv> \<guillemotleft>0x20::nat\<guillemotright>" -- W

text \<open>\texttt{tis\_int\_flags}\<close>
abbreviation "TPM_GLOBAL_INT_ENABLE \<equiv> \<guillemotleft>0x80000000::nat\<guillemotright>"
abbreviation "TPM_INTF_BURST_COUNT_STATIC \<equiv> \<guillemotleft>0x100::nat\<guillemotright>"
abbreviation "TPM_INTF_CMD_READY_INT \<equiv> \<guillemotleft>0x080::nat\<guillemotright>"
abbreviation "TPM_INTF_INT_EDGE_FALLING \<equiv> \<guillemotleft>0x040::nat\<guillemotright>"
abbreviation "TPM_INTF_INT_EDGE_RISING \<equiv> \<guillemotleft>0x020::nat\<guillemotright>"
abbreviation "TPM_INTF_INT_LEVEL_LOW \<equiv> \<guillemotleft>0x010::nat\<guillemotright>"
abbreviation "TPM_INTF_INT_LEVEL_HIGH \<equiv> \<guillemotleft>0x008::nat\<guillemotright>"
abbreviation "TPM_INTF_LOCALITY_CHANGE_INT \<equiv> \<guillemotleft>0x004::nat\<guillemotright>"
abbreviation "TPM_INTF_STS_VALID_INT \<equiv> \<guillemotleft>0x002::nat\<guillemotright>"
abbreviation "TPM_INTF_DATA_AVAIL_INT \<equiv> \<guillemotleft>0x001::nat\<guillemotright>"

text \<open>\texttt{tis\_defaults}\<close>
abbreviation "TIS_MEM_BASE \<equiv> \<guillemotleft>0xFED40000::nat\<guillemotright>"
abbreviation "TIS_MEM_LEN \<equiv> \<guillemotleft>0x5000::nat\<guillemotright>"
abbreviation "TIS_SHORT_TIMEOUT \<equiv> \<guillemotleft>750::nat\<guillemotright>" -- \<open>ms\<close>
abbreviation "TIS_LONG_TIMEOUT \<equiv> \<guillemotleft>2000::nat\<guillemotright>" -- \<open>2 sec\<close>

abbreviation "TPM_TIMEOUT \<equiv> \<guillemotleft>5::nat\<guillemotright>"

paragraph \<open>pointer-struct accesses for later\<close>
abbreviation "TPM_ACCESS t l \<equiv> \<guillemotleft>0\<guillemotright>"
abbreviation "TPM_INT_ENABLE t l \<equiv> \<guillemotleft>0\<guillemotright>"
abbreviation "TPM_INT_VECTOR t l \<equiv> \<guillemotleft>0\<guillemotright>"
abbreviation "TPM_INT_STATUS t l \<equiv> \<guillemotleft>0\<guillemotright>"
abbreviation "TPM_INTF_CAPS t l \<equiv> \<guillemotleft>0\<guillemotright>"
abbreviation "TPM_STS t l \<equiv> \<guillemotleft>0\<guillemotright>"
abbreviation "TPM_DATA_FIFO t l \<equiv> \<guillemotleft>0\<guillemotright>"

abbreviation "TPM_DID_VID t l \<equiv> \<guillemotleft>0\<guillemotright>"
abbreviation "TPM_RID t l \<equiv> \<guillemotleft>0\<guillemotright>"

(* tpm_chip struct... *)

paragraph \<open>Functions\<close>
(* TODO: once we get structs and pointers, as well as external function calls w/nondeterminism
static void __init_tpm_chip(struct tpm_chip* tpm)
s_time_t tpm_calc_ordinal_duration(struct tpm_chip *chip, uint32_t ordinal)
static int locality_enabled(struct tpm_chip* tpm, int l)
static int check_locality(struct tpm_chip* tpm, int l)
void release_locality(struct tpm_chip* tpm, int l, int force)
int tpm_tis_request_locality(struct tpm_chip* tpm, int l)
static uint8_t tpm_tis_status(struct tpm_chip* tpm)
static void tpm_tis_ready(struct tpm_chip* tpm)
#define tpm_tis_cancel_cmd(v) tpm_tis_ready(v)
static int get_burstcount(struct tpm_chip* tpm)
static int wait_for_stat(struct tpm_chip* tpm, uint8_t mask, unsigned long timeout, struct wait_queue_head* queue)
static int recv_data(struct tpm_chip* tpm, uint8_t* buf, size_t count)
int tpm_tis_recv(struct tpm_chip* tpm, uint8_t* buf, size_t count)
int tpm_tis_send(struct tpm_chip* tpm, uint8_t* buf, size_t len)
static void tpm_tis_irq_handler(evtchn_port_t port, struct pt_regs *regs, void* data)
static ssize_t tpm_transmit(struct tpm_chip *chip, const uint8_t *buf, size_t bufsiz)
static ssize_t transmit_cmd(struct tpm_chip *chip, struct tpm_cmd_t *cmd, int len, const char *desc)
int tpm_get_timeouts(struct tpm_chip *chip)
void tpm_continue_selftest(struct tpm_chip* chip)
ssize_t tpm_getcap(struct tpm_chip *chip, uint32_t subcap_id, cap_t *cap, const char *desc)
struct tpm_chip* init_tpm_tis(unsigned long baseaddr, int localities, unsigned int irq)
void shutdown_tpm_tis(struct tpm_chip* tpm)
int tpm_tis_cmd(struct tpm_chip* tpm, uint8_t* req, size_t reqlen, uint8_t** resp, size_t* resplen)
int tpm_tis_open(struct tpm_chip* tpm)
int tpm_tis_posix_write(int fd, const uint8_t* buf, size_t count)
int tpm_tis_posix_read(int fd, uint8_t* buf, size_t count)
int tpm_tis_posix_fstat(int fd, struct stat* buf)
static void tpm2_selftest(struct tpm_chip* chip)
struct tpm_chip* init_tpm2_tis(unsigned long baseaddr, int localities, unsigned int irq)
*)

end
