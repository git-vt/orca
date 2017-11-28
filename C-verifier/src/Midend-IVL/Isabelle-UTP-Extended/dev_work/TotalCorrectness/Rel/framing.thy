section \<open>Work on framing and function calls\<close>

theory framing
imports
  "../../../../../Backend/VCG/VCG_rel_Floyd"
  "../../../utils/vcg_helpers"
begin
lemma blah1: 
  assumes "vwb_lens g'" "vwb_lens l"
   assumes  "l \<bowtie> g'" 
   shows "vwb_lens  (g' +\<^sub>L l)" 
   using assms 
    by (simp add: lens_indep_sym plus_vwb_lens) 

    
 lemma blah12:
  assumes "vwb_lens g" "vwb_lens g'" "vwb_lens l"
  assumes "l \<bowtie> g"  " g = g'"
    defines "gl \<equiv> g' +\<^sub>L l"
  assumes "gl:[C] = C" 
  assumes "\<lbrace>p\<rbrace>C\<lbrace>q\<rbrace>\<^sub>u"
  assumes "`r \<Rightarrow> p`"      
  shows "\<lbrace>r\<rbrace> l:\<lbrakk>C\<rbrakk> \<lbrace>(\<exists> l \<bullet> q) \<and> (\<exists>g' \<bullet> r)\<rbrace>\<^sub>u"
  using assms unfolding lens_indep_def

   apply rel_auto 
  apply (metis (no_types, lifting) vwb_lens_wb wb_lens.get_put)
  apply pred_simp
    apply (rename_tac a x)
    apply (rule_tac x="get\<^bsub>g'\<^esub> a" in exI)
  
proof -
  fix a :: 'b and x :: 'b
  assume a1: "\<lbrakk>r\<rbrakk>\<^sub>e a"
  assume a2: "vwb_lens l"
  assume a3: "vwb_lens g'"
  assume a4: "\<forall>\<sigma> v u. put\<^bsub>l\<^esub> (put\<^bsub>g'\<^esub> \<sigma> v) u = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> \<sigma> u) v"
  assume a5: "\<lbrakk>C\<rbrakk>\<^sub>e (a, x)"
  assume a6: "\<forall>a b. (\<exists>x. \<lbrakk>C\<rbrakk>\<^sub>e (a, x) \<and> b = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> x)) (get\<^bsub>g'\<^esub> x)) = \<lbrakk>C\<rbrakk>\<^sub>e (a, b)"
  obtain bb :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" where
    "\<forall>x0 x1. (\<exists>v2. \<lbrakk>C\<rbrakk>\<^sub>e (x1, v2) \<and> x0 = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x1 (get\<^bsub>l\<^esub> v2)) (get\<^bsub>g'\<^esub> v2)) = (\<lbrakk>C\<rbrakk>\<^sub>e (x1, bb x0 x1) \<and> x0 = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x1 (get\<^bsub>l\<^esub> (bb x0 x1))) (get\<^bsub>g'\<^esub> (bb x0 x1)))"
    by moura
  then have "\<lbrakk>C\<rbrakk>\<^sub>e (a, bb x a) \<and> x = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> (bb x a))) (get\<^bsub>g'\<^esub> (bb x a))"
    using a6 a5 by presburger
  then show "\<lbrakk>r\<rbrakk>\<^sub>e (put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x (get\<^bsub>l\<^esub> a)) (get\<^bsub>g'\<^esub> a))"
    using a4 a3 a2 a1 by (metis (no_types) mwb_lens.put_put vwb_lens_mwb vwb_lens_wb wb_lens.get_put)
qed
term "{$g', $l}:[C] = C"  
lemma
  assumes "vwb_lens g" "vwb_lens g'" "vwb_lens l"
  assumes "l \<bowtie> g" "g' \<subseteq>\<^sub>L g"
    defines "gl \<equiv> g' +\<^sub>L l"
  assumes "gl:[C] = C" 
  assumes "\<lbrace>p\<rbrace>C\<lbrace>q\<rbrace>\<^sub>u"
  assumes "`r \<Rightarrow> p`"      
  shows "\<lbrace>r\<rbrace> l:\<lbrakk>C\<rbrakk> \<lbrace>(\<exists> l \<bullet> q) \<and> (\<exists>g' \<bullet> r)\<rbrace>\<^sub>u"
  using assms unfolding lens_indep_def

   apply rel_auto 
  apply (metis (no_types, lifting) vwb_lens_wb wb_lens.get_put)
  apply pred_simp
  term "lens_get (fst\<^sub>L ;\<^sub>L gl) a"
        term "lens_get (Z ;\<^sub>L gl) a"
        term "get\<^bsub>Z ;\<^sub>L g\<^esub> (put \<^bsub>Z ;\<^sub>L g\<^esub> a (get\<^bsub>g\<^esub> a))"
        apply (rule_tac x="get\<^bsub> g'\<^esub> (put\<^bsub>g\<^esub> a (get\<^bsub>g\<^esub> x))" in exI) find_theorems "(?a = ?b) = (?b = ?a)"
          
        apply (subst (asm) eq_commute[of "get\<^bsub>_\<^esub> (get\<^bsub>g\<^esub> _)" "get\<^bsub>_\<^esub> (get\<^bsub>g\<^esub> _)"])
        apply (simp) 
        thm wb_lens.get_put [of Z ]  
        apply (simp add: vwb_lens_wb wb_lens.get_put)  

        oops    
lemma
  assumes 1:"vwb_lens g" 
  assumes 2:"vwb_lens g'" 
  assumes 3:"vwb_lens l"
  assumes 4:"l \<bowtie> g'" 
  assumes 8:"g' \<subseteq>\<^sub>L g"
  assumes 5:"{&g', &l}:[C] = C" 
  assumes 6:"\<lbrace>p\<rbrace>C\<lbrace>q\<rbrace>\<^sub>u"
  assumes 7:"`r \<Rightarrow> p`"      
  shows "\<lbrace>r\<rbrace> l:\<lbrakk>C\<rbrakk> \<lbrace>(\<exists> l \<bullet> q) \<and> (\<exists>g' \<bullet> r)\<rbrace>\<^sub>u"
  using 1 2 3 4 5 6 7unfolding lens_indep_def

   apply rel_auto 
   apply (metis (no_types, lifting) vwb_lens_wb wb_lens.get_put)
  apply pred_simp
  apply (rule_tac x="get\<^bsub> g'\<^esub> a" in exI)
proof -
  fix a :: 'b and x :: 'b
  assume a1: "\<lbrakk>r\<rbrakk>\<^sub>e a"
  assume a2: "vwb_lens l"
  assume a3: "vwb_lens g'"
  assume a4: "\<forall>\<sigma> v u. put\<^bsub>l\<^esub> (put\<^bsub>g'\<^esub> \<sigma> v) u = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> \<sigma> u) v"
  assume a5: "\<lbrakk>C\<rbrakk>\<^sub>e (a, x)"
  assume a6: "\<forall>a b. (\<exists>x. \<lbrakk>C\<rbrakk>\<^sub>e (a, x) \<and> b = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> x)) (get\<^bsub>g'\<^esub> x)) = \<lbrakk>C\<rbrakk>\<^sub>e (a, b)"
  obtain bb :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" where
    "\<forall>x0 x1. (\<exists>v2. \<lbrakk>C\<rbrakk>\<^sub>e (x1, v2) \<and> x0 = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x1 (get\<^bsub>l\<^esub> v2)) (get\<^bsub>g'\<^esub> v2)) = (\<lbrakk>C\<rbrakk>\<^sub>e (x1, bb x0 x1) \<and> x0 = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x1 (get\<^bsub>l\<^esub> (bb x0 x1))) (get\<^bsub>g'\<^esub> (bb x0 x1)))"
    by moura
  then have "\<lbrakk>C\<rbrakk>\<^sub>e (a, bb x a) \<and> x = put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> a (get\<^bsub>l\<^esub> (bb x a))) (get\<^bsub>g'\<^esub> (bb x a))"
    using a6 a5 by presburger
  then show "\<lbrakk>r\<rbrakk>\<^sub>e (put\<^bsub>g'\<^esub> (put\<^bsub>l\<^esub> x (get\<^bsub>l\<^esub> a)) (get\<^bsub>g'\<^esub> a))"
    using a4 a3 a2 a1 by (metis (no_types) mwb_lens.put_put vwb_lens_mwb vwb_lens_wb wb_lens.get_put)
qed

     
definition \<open>EXINV l P \<equiv> \<^bold>\<exists>st \<bullet> P\<lbrakk>(\<guillemotleft>st\<guillemotright> \<oplus> &\<Sigma> on &l)/&\<Sigma>\<rbrakk>\<close>

subsection \<open>Modification is existential\<close>

definition \<open>modifies x \<equiv> \<^bold>\<exists>v' \<bullet> $\<Sigma>\<acute> \<oplus> \<guillemotleft>v'\<guillemotright> on &x =\<^sub>u $\<Sigma>\<close>

lemma modifies_to_ext:
  assumes \<open>vwb_lens x\<close>
      and \<open>modifies x \<sqsubseteq> c\<close>
  shows \<open>\<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u\<close>
  using assms unfolding modifies_def
  by rel_simp metis

lemma ext_to_modifies:
  assumes \<open>vwb_lens x\<close>
      and \<open>\<forall>P. \<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u\<close>
  shows \<open>modifies x \<sqsubseteq> c\<close>
  using assms unfolding modifies_def
  apply - \<comment> \<open>Why do we need to inline the assumptions? Weird.\<close>
  apply rel_simp
  by (metis skip_r_eq subst.rep_eq vwb_lens.put_eq)

lemma modifies_ext:
  assumes \<open>vwb_lens x\<close>
  shows \<open>modifies x \<sqsubseteq> c = (\<forall>P. \<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u)\<close>
  by (metis assms modifies_to_ext ext_to_modifies)

subsection \<open>Region-based modifies\<close>
text \<open>We want to be able to reason about the intersection of lenses and the above modifies does not
allow us to do so.\<close>

definition region :: \<open>('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha> set\<close> where
  \<open>region x s = {s'. \<exists>v. s' = put\<^bsub>x\<^esub> s v}\<close>

definition region_modifies :: \<open>('\<alpha> \<Rightarrow> '\<alpha> set) \<Rightarrow> _\<close> where
  \<open>region_modifies reg \<equiv> $\<Sigma>\<acute> \<in>\<^sub>u uop reg $\<Sigma>\<close>

abbreviation region_modifies_ref where
  \<open>region_modifies_ref r c \<equiv> region_modifies r \<sqsubseteq> c\<close>

lemma region_modifies_to_ext:
  assumes \<open>region_modifies (region x) \<sqsubseteq> c\<close>
          \<open>vwb_lens x\<close>
  shows \<open>\<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u\<close>
  using assms unfolding region_modifies_def region_def
  by rel_simp (metis vwb_lens.put_eq)

lemma ext_to_region_modifies:
  assumes \<open>\<forall>P. \<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u\<close>
          \<open>vwb_lens x\<close>
  shows \<open>region_modifies (region x) \<sqsubseteq> c\<close>
  using assms unfolding region_modifies_def region_def
  by rel_simp (metis (no_types, hide_lams) skip_r_eq subst.rep_eq vwb_lens.put_eq)

lemma region_modifies_ext:
  assumes \<open>vwb_lens x\<close>
  shows \<open>region_modifies (region x) \<sqsubseteq> c = (\<forall>P. \<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u)\<close>
  using assms ext_to_region_modifies region_modifies_to_ext
  by blast

text \<open>supposed to be @{text \<sqinter>} but UTP messed it up\<close>
abbreviation \<open>reg_inter r\<^sub>1 r\<^sub>2 \<equiv> Lattices.inf r\<^sub>1 r\<^sub>2\<close> \<comment> \<open>@{text \<open>\<lambda>s. r\<^sub>1 s \<inter> r\<^sub>2 s\<close>}\<close>

lemma reg_mod_intersect: \<comment> \<open>Greatest lower bound\<close>
  assumes \<open>region_modifies r\<^sub>1 \<sqsubseteq> c\<close> \<open>region_modifies r\<^sub>2 \<sqsubseteq> c\<close>
  shows \<open>region_modifies (reg_inter r\<^sub>1 r\<^sub>2) \<sqsubseteq> c\<close>
  using assms unfolding region_def region_modifies_def
  by rel_simp

lemma reg_mod_intersect_sym:
  assumes \<open>region_modifies (reg_inter r\<^sub>1 r\<^sub>2) \<sqsubseteq> c\<close>
  shows \<open>region_modifies r\<^sub>1 \<sqsubseteq> c\<close> \<open>region_modifies r\<^sub>2 \<sqsubseteq> c\<close> \<comment> \<open>@{text \<ge>}\<close>
  using assms unfolding region_def region_modifies_def
  by rel_simp+

lemma reg_mod_intersect_antiframe1:
  assumes \<open>region_modifies r\<^sub>1 \<sqsubseteq> c\<close> \<open>region_modifies r\<^sub>2 \<sqsubseteq> c\<close>
          \<open>vwb_lens b\<close>
  shows \<open>region_modifies (reg_inter r\<^sub>1 r\<^sub>2) \<sqsubseteq> b:[c]\<close>
  using assms unfolding region_modifies_def region_def
  apply rel_auto
  oops \<comment> \<open>Don't know how either region relates to b\<close>
   apply (metis mwb_lens.put_put vwb_lens_def wb_lens.get_put)
  apply (metis vwb_lens.put_eq)
  done

lemma reg_mod_intersect_antiframe2:
  assumes \<open>region_modifies r\<^sub>1 \<sqsubseteq> c\<close> \<open>region_modifies r\<^sub>2 \<sqsubseteq> c\<close>
          \<open>vwb_lens a\<close>
  shows \<open>region_modifies (reg_inter r\<^sub>1 r\<^sub>2) \<sqsubseteq> a:[c]\<close>
  using assms unfolding region_modifies_def region_def
  apply rel_auto
  oops \<comment> \<open>Don't know how either region relates to a\<close>
    apply (metis vwb_lens_def wb_lens.get_put)
  apply (metis vwb_lens.put_eq)
  done

subsection \<open>Regions of a program\<close>

definition \<open>prog_region c s = {s'. \<lbrakk>c\<rbrakk>\<^sub>e (s, s')}\<close>
abbreviation prog_region_ref (infix "\<flat>" 95) where
  \<open>r \<flat> c \<equiv> r \<ge> prog_region c\<close>

lemma reg_mod_prog_temp:
  \<open>region_modifies r \<sqsubseteq> c = r \<flat> c\<close>
  unfolding prog_region_def region_modifies_def
  by rel_auto (auto simp: le_fun_def)

lemma prog_reg_to_ext:
  assumes \<open>region x \<flat> c\<close>
          \<open>vwb_lens x\<close>
  shows \<open>\<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u\<close>
proof -
  have \<open>(region x) \<flat> c = (\<forall>s s'. \<lbrakk>c\<rbrakk>\<^sub>e (s, s') \<longrightarrow> (\<exists>v. s' = put\<^bsub>x\<^esub> s v))\<close>
    unfolding prog_region_def region_def le_fun_def
    by auto
  with assms show ?thesis by rel_simp (metis vwb_lens.put_eq)
qed

lemma ext_to_prog_reg:
  assumes \<open>\<forall>P. \<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u\<close>
          \<open>vwb_lens x\<close>
  shows \<open>region x \<flat> c\<close>
  using assms unfolding prog_region_def region_def le_fun_def
  by rel_simp (metis (no_types, hide_lams) skip_r_eq subst.rep_eq vwb_lens.put_eq)

lemma prog_reg_ext:
  assumes \<open>vwb_lens x\<close>
  shows \<open>(region x) \<flat> c = (\<forall>P. \<lbrace>P\<rbrace>c\<lbrace>\<exists>x \<bullet> P\<rbrace>\<^sub>u)\<close>
  using assms prog_reg_to_ext ext_to_prog_reg
  by blast

lemma prog_reg_inf_antiframe:
  assumes \<open>r \<flat> c\<close>
          \<open>vwb_lens x\<close>
  shows \<open>reg_inter r (region x) \<flat> x:[c]\<close>
  using assms unfolding prog_region_def region_def le_fun_def
  apply rel_auto
  oops

text \<open>Lenses are too abstract for proper region reasoning right now.\<close>

subsection \<open>Antiframe rule work\<close>

lemma antiframe_rule(* [hoare_rules] *):
  assumes \<open>vwb_lens a\<close> \<open>\<lbrace>P\<rbrace>c\<lbrace>Q\<rbrace>\<^sub>u\<close>
  shows \<open>\<lbrace>P\<rbrace> a:[c] \<lbrace>(\<exists>a \<bullet> P) \<and> (EXINV a Q)\<rbrace>\<^sub>u\<close>
  using assms unfolding EXINV_def
  by rel_simp (metis assms(1) vwb_lens_wb wb_lens.get_put)

(* declare assigns_floyd_r[hoare_rules del] *)
lemma assigns_floyd_rX (* [hoare_rules] *):
  assumes \<open>vwb_lens x\<close>
  shows   \<open>\<lbrace>p\<rbrace>x :== e\<lbrace>(\<exists>x \<bullet> p) \<and> (\<^bold>\<exists>v \<bullet> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>)\<rbrace>\<^sub>u\<close>(*INCOMPLETE*)
  apply (insert assms)
  apply pred_simp
  apply transfer
  apply rule
   apply (rule_tac x = \<open>get\<^bsub>x\<^esub> a\<close> in exI)
   apply auto
  apply (rule_tac x = \<open>get\<^bsub>x\<^esub> a\<close> in exI)
  apply auto
  done

lemma modified_assign_rule (* [hoare_rules] *):
  assumes \<open>vwb_lens x\<close>
  shows   \<open>\<lbrace>p\<rbrace>x :== e\<lbrace>\<exists>x \<bullet> p\<rbrace>\<^sub>u\<close>
  apply (rule hoare_post_weak)
   apply (rule assigns_floyd_rX)
   apply fact
  apply pred_simp
  done

lemma EXINV_pull_out_sublens:
  assumes A: \<open>vwb_lens x\<close> \<open>vwb_lens l\<close>
  defines \<open>XX \<equiv> x ;\<^sub>L l\<close>
  shows \<open>EXINV l (\<exists>XX \<bullet> P) = (\<exists>XX \<bullet> EXINV l P)\<close>
  unfolding EXINV_def XX_def using A
  by pred_blast

lemma EXINV_drop_indep:
  assumes A: \<open>vwb_lens l\<^sub>1\<close> \<open>vwb_lens l\<^sub>2\<close> \<open>l\<^sub>1 \<bowtie> l\<^sub>2\<close>
  shows "EXINV l\<^sub>1 (\<exists>l\<^sub>2 \<bullet> P) = (EXINV l\<^sub>1 P)"
  unfolding EXINV_def using A
  by pred_simp (metis lens_indep_def vwb_lens_wb wb_lens.get_put)

lemma lens_indep_right_ext' [intro, simp]:
  \<open>z \<bowtie> x \<Longrightarrow> x \<bowtie> (y ;\<^sub>L z)\<close>
  using lens_indep_sym by blast

lemma lens_indep_left_ext' [intro, simp]:
  \<open>x \<bowtie> z \<Longrightarrow> (y ;\<^sub>L z) \<bowtie> x\<close>
  using lens_indep_sym by blast

(*lemmas [simp] = lens_indep_right_ext lens_indep_left_ext*)

lemma conj_ex2_move_front: \<open>l \<sharp> P \<Longrightarrow> (P \<and> (\<exists>l \<bullet> Q)) = (\<exists>l \<bullet> P \<and> Q)\<close>
  by pred_simp

lemma dep_unrest_ex:
  assumes A: \<open>vwb_lens x\<close> \<open>vwb_lens l\<close>
  defines \<open>XX \<equiv> x;\<^sub>Ll\<close>
  shows \<open>XX \<sharp> (\<exists> l \<bullet> F)\<close>
  unfolding XX_def using A
  by pred_simp

lemma
  assumes \<open>vwb_lens l\<close>
  shows \<open>((\<exists> l \<bullet> F) \<and> EXINV l F) = F\<close>
  using assms
  unfolding EXINV_def
  apply pred_simp
  apply transfer
  oops

lemma \<open>(\<exists>x. P x y) \<and> (\<exists>y. P x y) \<Longrightarrow> P x y\<close>
  oops

subsection \<open>Locales for modularity\<close>

locale peter =
  fixes lvars :: \<open>'l \<Longrightarrow> 's\<close>
    and gvars :: \<open>'g \<Longrightarrow> 's\<close>
    and   ret :: \<open>nat \<Longrightarrow> 'g\<close>
    and     x :: \<open>nat \<Longrightarrow> 'l\<close>
    and     y :: \<open>nat \<Longrightarrow> 'l\<close>
  assumes INDEP: \<open>lvars \<bowtie> gvars\<close> \<open>x \<bowtie> y\<close>
          \<open>vwb_lens lvars\<close> \<open>vwb_lens gvars\<close> \<open>vwb_lens ret\<close> \<open>vwb_lens x\<close> \<open>vwb_lens y\<close>
begin

abbreviation \<open>Lx \<equiv> x ;\<^sub>L lvars\<close>
abbreviation \<open>Ly \<equiv> y ;\<^sub>L lvars\<close>
abbreviation \<open>Gret \<equiv> ret ;\<^sub>L gvars\<close>

definition \<open>f r a = gvars:[Lx :== a ;; Lx :== (&Lx + \<guillemotleft>1\<guillemotright>);; Gret:==&Lx];; r :== &Gret\<close>

lemma f_rule:
  assumes \<open>vwb_lens r\<close>
  shows \<open>\<lbrace> e=\<^sub>u\<guillemotleft>val\<guillemotright> \<rbrace> f r e \<lbrace> &r=\<^sub>u\<guillemotleft>val+1\<guillemotright> \<rbrace>\<^sub>u\<close>
  unfolding f_def using assms INDEP
  by rel_simp

lemma
  assumes \<open>vwb_lens r\<close>
  shows \<open>\<lbrace> F \<rbrace> f r a \<lbrace> \<exists> r \<bullet> \<exists> Gret \<bullet> F \<rbrace>\<^sub>u\<close>
  unfolding f_def using INDEP
  apply (insert assms)
    supply frame_hoare_r[hoare_rules]
  apply exp_vcg
  apply (simp add: EXINV_pull_out_sublens EXINV_drop_indep conj_ex2_move_front dep_unrest_ex)
  unfolding EXINV_def
  apply pred_simp
  apply (subst conj_ex2_move_front)
  oops
  apply (subst EXINV_drop_indep)
  apply simp
  apply simp
  apply (rule lens_indep_sym)
  solve_direct
  using lens_indep_sym apply blast
  apply simp
  oops
  apply solve_vcg
  apply pred_simp
  apply (simp add: vwb_lens_wb[THEN wb_lens.get_put])

end

end
