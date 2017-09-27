section \<open>Syntax extensions for UTP\<close>

theory utp_extensions
imports
  BitOps
  "../../Isabelle-UTP/utp/utp"
  "~~/src/HOL/Library/Multiset"
begin
recall_syntax \<comment> \<open>Fixes notation issue with inclusion of HOL libraries.\<close>
 (*TODO @Yakoub: Fix the F** of the priorities of the syntax*)

subsection \<open>Notation\<close>

text \<open>We need multisets for concise list invariants for sorting. Also, int/nat conversion is
sometimes needed as some loop methods mix array indices and loop variables (which sometimes rely on
going below 0 for termination). Bitwise operations and record access/update are included for
completeness.\<close>
  
text \<open>A helper function for record updating.\<close>
lift_definition rec_update_wrapper :: \<open>('a, '\<alpha>) uexpr \<Rightarrow> ('a \<Rightarrow> 'a, '\<alpha>) uexpr\<close> is
  \<open>\<lambda>v s _. v s\<close> .

syntax
  "_umset" :: \<open>('a list, '\<alpha>) uexpr \<Rightarrow> ('a multiset, '\<alpha>) uexpr\<close> ("mset\<^sub>u'(_')")
  "_unat" :: \<open>(nat, '\<alpha>) uexpr \<Rightarrow> (int, '\<alpha>) uexpr\<close> ("int\<^sub>u'(_')")
  "_uint" :: \<open>(int, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr\<close> ("nat\<^sub>u'(_')")
  "_uapply_rec" :: \<open>('a, '\<alpha>) uexpr \<Rightarrow> utuple_args \<Rightarrow> ('b, '\<alpha>) uexpr\<close> ("_\<lparr>_\<rparr>\<^sub>r" [999,0] 999)
  "_uupd_rec"   :: \<open>('a, '\<alpha>) uexpr \<Rightarrow> (('b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr\<close> ("_/'(_ /\<mapsto>/ _')\<^sub>r" [900,0,0] 900)
  "_ubs_and"    :: \<open>(int, '\<alpha>) uexpr \<Rightarrow> (int, '\<alpha>) uexpr \<Rightarrow> (int, '\<alpha>) uexpr\<close> (infixl "\<and>\<^sub>b\<^sub>s" 85)
  "_ubu_and"    :: \<open>(nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr\<close> (infixl "\<and>\<^sub>b\<^sub>u" 85)
  "_ubs_or"     :: \<open>(int, '\<alpha>) uexpr \<Rightarrow> (int, '\<alpha>) uexpr \<Rightarrow> (int, '\<alpha>) uexpr\<close> (infixl "\<or>\<^sub>b\<^sub>s" 80)
  "_ubu_or"     :: \<open>(nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr\<close> (infixl "\<or>\<^sub>b\<^sub>u" 80)
  "_ubs_lsh"    :: \<open>(int, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> (int, '\<alpha>) uexpr\<close>	("_ \<lless>\<^bsub>s'/_\<^esub> _" [100,100,101] 100)
  "_ubu_lsh"    :: \<open>(nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr\<close>	("_ \<lless>\<^bsub>u'/_\<^esub> _" [100,100,101] 100)
  "_ubs_rsh"    :: \<open>(int, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> (int, '\<alpha>) uexpr\<close>	("_ \<ggreater>\<^bsub>s'/_\<^esub> _" [100,100,101] 100)
  "_ubu_rsh"    :: \<open>(nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr\<close>	("_ \<ggreater>\<^bsub>u'/_\<^esub> _" [100,100,101] 100)
  "_ubs_not"    :: \<open>(nat, '\<alpha>) uexpr \<Rightarrow> (int, '\<alpha>) uexpr \<Rightarrow> (int, '\<alpha>) uexpr\<close> ("\<not>\<^bsub>s'/_\<^esub> _" [200, 150] 150)
  "_ubu_not"    :: \<open>(nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr\<close>	 ("\<not>\<^bsub>u'/_\<^esub> _" [200, 150] 150)
  "_ubu_neg"    :: \<open>(nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr\<close>	 ("-\<^bsub>u'/_\<^esub> _" [200, 150] 150)

translations
  "_umset" == "CONST uop CONST mset"
  "_uint" == "CONST uop CONST int"
  "_unat" == "CONST uop CONST nat"
  "f\<lparr>kf\<rparr>\<^sub>r" => "CONST uop kf f"
  "f(k \<mapsto> v)\<^sub>r" => "CONST bop k (CONST rec_update_wrapper v) f"
  "_ubs_and" == "CONST bop (CONST s_bitop (op AND))"
  "_ubu_and" == "CONST bop (CONST u_bitop (op AND))"
  "_ubs_or" == "CONST bop (CONST s_bitop (op OR))"
  "_ubu_or" == "CONST bop (CONST u_bitop (op OR))"
  "_ubs_lsh" == "CONST trop CONST s_lsh"
  "_ubu_lsh" == "CONST trop CONST u_lsh"
  "_ubs_rsh" == "CONST trop CONST s_rsh"
  "_ubu_rsh" == "CONST trop CONST u_rsh"
  "_ubs_not" == "CONST bop CONST s_not"
  "_ubu_not" == "CONST bop CONST u_not"
  "_ubu_neg" == "CONST bop CONST u_neg"

subsection \<open>Extra stuff to work more-arg functions into UTP\<close>

lift_definition qiop ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f) \<Rightarrow>
   ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr \<Rightarrow> ('d, '\<alpha>) uexpr \<Rightarrow> ('e, '\<alpha>) uexpr \<Rightarrow>
   ('f, '\<alpha>) uexpr\<close>
  is \<open>\<lambda>f u v w x y b. f (u b) (v b) (w b) (x b) (y b)\<close> .
lift_definition sxop ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g) \<Rightarrow>
   ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr \<Rightarrow> ('d, '\<alpha>) uexpr \<Rightarrow> ('e, '\<alpha>) uexpr \<Rightarrow>
   ('f, '\<alpha>) uexpr \<Rightarrow> ('g, '\<alpha>) uexpr\<close>
  is \<open>\<lambda>f u v w x y z b. f (u b) (v b) (w b) (x b) (y b) (z b)\<close> .
update_uexpr_rep_eq_thms \<comment> \<open>Necessary to get the above utilized by {pred,rel}_{auto,simp}\<close>

text \<open>The below lemmas do not seem useful in general but are included for completeness.\<close>
lemma qiop_ueval [ueval]: \<open>\<lbrakk>qiop f v x y z w\<rbrakk>\<^sub>eb = f (\<lbrakk>v\<rbrakk>\<^sub>eb) (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb) (\<lbrakk>z\<rbrakk>\<^sub>eb) (\<lbrakk>w\<rbrakk>\<^sub>eb)\<close>
  by transfer simp

lemma subst_qiop [usubst]: \<open>\<sigma> \<dagger> qiop f t u v w x = qiop f (\<sigma> \<dagger> t) (\<sigma> \<dagger> u) (\<sigma> \<dagger> v) (\<sigma> \<dagger> w) (\<sigma> \<dagger> x)\<close>
  by transfer simp

lemma unrest_qiop [unrest]: \<open>\<lbrakk>x \<sharp> t; x \<sharp> u; x \<sharp> v; x \<sharp> w; x \<sharp> y\<rbrakk> \<Longrightarrow> x \<sharp> qiop f t u v w y\<close>
  by transfer simp

lemma aext_qiop [alpha]:
  \<open>qiop f t u v w x \<oplus>\<^sub>p a = qiop f (t \<oplus>\<^sub>p a) (u \<oplus>\<^sub>p a) (v \<oplus>\<^sub>p a) (w \<oplus>\<^sub>p a) (x \<oplus>\<^sub>p a)\<close>
  by pred_auto

lemma lit_qiop_simp [lit_simps]:
  \<open>\<guillemotleft>i x y z u t\<guillemotright> = qiop i \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright> \<guillemotleft>z\<guillemotright> \<guillemotleft>u\<guillemotright> \<guillemotleft>t\<guillemotright>\<close>
  by transfer simp

lemma sxop_ueval [ueval]: \<open>\<lbrakk>sxop f v x y z w t\<rbrakk>\<^sub>eb = f (\<lbrakk>v\<rbrakk>\<^sub>eb) (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb) (\<lbrakk>z\<rbrakk>\<^sub>eb) (\<lbrakk>w\<rbrakk>\<^sub>eb) (\<lbrakk>t\<rbrakk>\<^sub>eb)\<close>
  by transfer simp

lemma subst_sxop [usubst]:
  \<open>\<sigma> \<dagger> sxop f t u v w x y = sxop f (\<sigma> \<dagger> t) (\<sigma> \<dagger> u) (\<sigma> \<dagger> v) (\<sigma> \<dagger> w) (\<sigma> \<dagger> x) (\<sigma> \<dagger> y)\<close>
  by transfer simp

lemma unrest_sxop [unrest]: \<open>\<lbrakk>x \<sharp> t; x \<sharp> u; x \<sharp> v; x \<sharp> w; x \<sharp> y; x \<sharp> z\<rbrakk> \<Longrightarrow> x \<sharp> sxop f t u v w y z\<close>
  by transfer simp

lemma aext_sxop [alpha]:
  \<open>sxop f t u v w x y \<oplus>\<^sub>p a = sxop f (t \<oplus>\<^sub>p a) (u \<oplus>\<^sub>p a) (v \<oplus>\<^sub>p a) (w \<oplus>\<^sub>p a) (x \<oplus>\<^sub>p a) (y \<oplus>\<^sub>p a)\<close>
  by pred_auto

lemma lit_sxop_simp [lit_simps]:
  \<open>\<guillemotleft>i x y z u t v\<guillemotright> = sxop i \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright> \<guillemotleft>z\<guillemotright> \<guillemotleft>u\<guillemotright> \<guillemotleft>t\<guillemotright> \<guillemotleft>v\<guillemotright>\<close>
  by transfer simp

end