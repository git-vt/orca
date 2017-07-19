subsection \<open>Memory mapping\<close>

theory mm
imports
  "../../../../../../Backend/VCG/VCG_total_ML"
begin

text \<open>sizeof(unsigned long) * 8\<close>
abbreviation "SIZEOF_ULONG \<equiv> \<guillemotleft>64::nat\<guillemotright>" (* assuming non-Windows 64-bit architecture *)
abbreviation "PAGES_PER_MAPWORD \<equiv> SIZEOF_ULONG * 8"

text \<open>Currently representing functions as individual definitions (without Hoare triples); this is
slightly troublesome as it requires passing in local variables to have them treated as such, but
that might just be an issue with my setup.\<close>
definition "map_alloc
  (*inputs*) first_page nr_pages
  (* global variables *) mm_alloc_bitmap nr_free_pages
  (* local variables*) curr_idx_start curr_idx start_off end_idx end_off temp
  =
  curr_idx_start \<Midarrow> &first_page div PAGES_PER_MAPWORD;;
  curr_idx  \<Midarrow> &curr_idx_start;;
  start_off \<Midarrow> &first_page \<and>\<^sub>b\<^sub>u (PAGES_PER_MAPWORD - 1);;
  end_idx   \<Midarrow> (&first_page + &nr_pages) div PAGES_PER_MAPWORD;;
  end_off   \<Midarrow> (&first_page + &nr_pages) \<and>\<^sub>b\<^sub>u (PAGES_PER_MAPWORD - 1);;

  bif &curr_idx =\<^sub>u &end_idx then
    temp \<Midarrow> (1 \<lless>\<^bsub>u/SIZEOF_ULONG\<^esub> &end_off) - 1;;
    temp \<Midarrow> &temp \<and>\<^sub>b\<^sub>u -\<^bsub>u/SIZEOF_ULONG\<^esub>(1 \<lless>\<^bsub>u/SIZEOF_ULONG\<^esub> &start_off);;
    temp \<Midarrow> &mm_alloc_bitmap\<lparr>&curr_idx\<rparr>\<^sub>u \<or>\<^sub>b\<^sub>u &temp;;
    mm_alloc_bitmap \<Midarrow> (&mm_alloc_bitmap:\<^sub>u nat list)(&curr_idx \<mapsto> &temp)\<^sub>u
  else
    temp \<Midarrow> -\<^bsub>u/SIZEOF_ULONG\<^esub>(1 \<lless>\<^bsub>u/SIZEOF_ULONG\<^esub> &start_off);;
    temp \<Midarrow> &mm_alloc_bitmap\<lparr>&curr_idx\<rparr>\<^sub>u \<or>\<^sub>b\<^sub>u &temp;;
    mm_alloc_bitmap \<Midarrow> &mm_alloc_bitmap(&curr_idx \<mapsto> &temp)\<^sub>u;;
    (true)\<^sup>\<top>\<^sup>C;; (* TODO: needs proper assumption *)
    while &curr_idx + 1 <\<^sub>u &end_idx
    invr (&curr_idx_start \<le>\<^sub>u &curr_idx) \<and>
         (true) (* needs to be something involving mm_alloc_bitmap *)
    do
      curr_idx \<Midarrow> &curr_idx + 1;;
      mm_alloc_bitmap \<Midarrow> &mm_alloc_bitmap(&curr_idx \<mapsto> \<not>\<^bsub>u/SIZEOF_ULONG\<^esub> 0)\<^sub>u
    od;;
    curr_idx \<Midarrow> &curr_idx + 1;; (* needed for last increment *)
    temp \<Midarrow> (1 \<lless>\<^bsub>u/SIZEOF_ULONG\<^esub> &end_off) - 1;;
    temp \<Midarrow> &mm_alloc_bitmap\<lparr>&curr_idx\<rparr>\<^sub>u \<or>\<^sub>b\<^sub>u &temp;;
    mm_alloc_bitmap \<Midarrow> &mm_alloc_bitmap(&curr_idx \<mapsto> &temp)\<^sub>u
  eif;;

  nr_free_pages \<Midarrow> &nr_free_pages - &nr_pages (* Global, so should use :==? Only if in alphabet... *)
  "

end
