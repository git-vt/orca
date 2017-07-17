theory heap_scratch

imports examples_total_correctness

begin

lemma swap_test_manual:
  assumes "weak_lens x" and "weak_lens y" and "weak_lens z"
  and "x \<bowtie> y" and "x \<bowtie> z" and "y \<bowtie> z"
  shows "\<lbrace>&x =\<^sub>u \<guillemotleft>a\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>b\<guillemotright>\<rbrace>
  z \<Midarrow> &x;;
  x \<Midarrow> &y;;
  y \<Midarrow> &z
  \<lbrace>&x =\<^sub>u \<guillemotleft>b\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>a\<guillemotright>\<rbrace>\<^sub>D"

oops
term "\<guillemotleft>s\<guillemotright>"
term "\<lceil>s\<rceil>\<^sub><"
term "\<lfloor>\<langle>id\<rangle>\<^sub>s heap\<rfloor>\<^sub><"
term "\<langle>id\<rangle>\<^sub>s (heap:: ('d, 'e) rel \<Longrightarrow> ('a, 'b) cp)"
term "\<lbrakk>\<langle>id\<rangle>\<^sub>s (heap:: ('d, 'e) rel \<Longrightarrow> ('a, 'b) cp)\<rbrakk>\<^sub>e t"
term "z \<Midarrow> &x;; heap :== \<guillemotleft>s\<guillemotright> ;; \<lceil>s :== h\<rceil>\<^sub>C\<^sub>>"
term "(\<lambda> (s, s') (t, t'). \<lbrakk>\<langle>id\<rangle>\<^sub>s (heap:: ('d, 'e) rel \<Longrightarrow> ('a, 'b) cp)\<rbrakk>\<^sub>e t ;; ss)"
term "block (II) (II) restore return"

term "z \<Midarrow> &x;; heap :== ( \<guillemotleft> sheap ;;s :== h;; s' :== h'\<guillemotright>) ;; heap :== &heap"
term "z \<Midarrow> &x;; heap :== \<guillemotleft>s;\<^sub>Ls'\<guillemotright> ;; \<lceil>s :== h\<rceil>\<^sub>C\<^sub>>"
term " heap :== \<guillemotleft>s\<guillemotright> ;; \<lceil>s :== h\<rceil>\<^sub>>"
alphabet cp_heap = "'f cp_vars" +
  heap :: "nat \<Longrightarrow> int"
term " heap :== \<guillemotleft>s \<guillemotright> ;; \<lceil>s :== h\<rceil>\<^sub>C\<^sub>>"

term "\<lceil>s :== h\<rceil>\<^sub>C\<^sub>>"
end