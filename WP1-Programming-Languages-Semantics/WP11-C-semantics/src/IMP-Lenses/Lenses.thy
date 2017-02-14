
(*This theory is inspired by the theory of Simon foster*)
chapter "Lenses"


theory Lenses
imports Main
        (*../../../../../HOL-TestGen-2016/src/SharedMemory" *)      
begin
section {* Lenses *}


subsection {* Lens signature *}

record ('a, 'b) lens =
  lens_get :: "'b \<Rightarrow> 'a" ("get\<index>")
  lens_put :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" ("put\<index>")

type_notation
  lens (infixr "\<Longrightarrow>" 0)

named_theorems lens_defs

definition lens_create :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("create\<index>") where
[lens_defs]: "lens_create X v = lens_put X undefined v"

subsection {* Lens composition, plus, unit, and identity *}

definition lens_comp :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('b \<Longrightarrow> 'c) \<Rightarrow> ('a \<Longrightarrow> 'c)" (infixr ";\<^sub>L" 80) where
[lens_defs]: "lens_comp X Y = \<lparr> lens_get = lens_get X \<circ> lens_get Y, 
                                lens_put = (\<lambda> \<sigma> v. lens_put Y \<sigma> (lens_put X (lens_get Y \<sigma>) v)) \<rparr>"

definition lens_plus :: "('a \<Longrightarrow> 'c) \<Rightarrow> ('b \<Longrightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Longrightarrow> 'c" (infixr "+\<^sub>L" 75) where
[lens_defs]: "X +\<^sub>L Y = \<lparr> lens_get = (\<lambda> \<sigma>. (lens_get X \<sigma>, lens_get Y \<sigma>))
                       , lens_put = (\<lambda> \<sigma> (u, v). lens_put X (lens_put Y \<sigma> v) u) \<rparr>"

definition fst_lens :: "'a \<Longrightarrow> 'a \<times> 'b" ("fst\<^sub>L") where
[lens_defs]: "fst\<^sub>L = \<lparr> lens_get = fst, lens_put = (\<lambda> (\<sigma>, \<rho>) u. (u, \<rho>)) \<rparr>"

definition snd_lens :: "'b \<Longrightarrow> 'a \<times> 'b" ("snd\<^sub>L") where
[lens_defs]: "snd\<^sub>L = \<lparr> lens_get = snd, lens_put = (\<lambda> (\<sigma>, \<rho>) u. (\<sigma>, u)) \<rparr>"

lemma get_fst_lens [simp]: "get\<^bsub>fst\<^sub>L\<^esub> (x, y) = x"
  by (simp add: fst_lens_def)

lemma get_snd_lens [simp]: "get\<^bsub>snd\<^sub>L\<^esub> (x, y) = y"
  by (simp add: snd_lens_def)

definition unit_lens :: "unit \<Longrightarrow> 'a" ("0\<^sub>L") where
[lens_defs]: "0\<^sub>L = \<lparr> lens_get = (\<lambda> _. ()), lens_put = (\<lambda> \<sigma> x. \<sigma>) \<rparr>"

text {* The quotient operator $X /_L Y$ shortens lens $X$ by cutting off $Y$ from the end. It is
        thus the dual of the composition operator. *} 

definition lens_quotient :: "('a \<Longrightarrow> 'c) \<Rightarrow> ('b \<Longrightarrow> 'c) \<Rightarrow> 'a \<Longrightarrow> 'b" (infixr "'/\<^sub>L" 90) where
[lens_defs]: "X /\<^sub>L Y = \<lparr>lens_get = \<lambda> \<sigma>. get\<^bsub>X\<^esub> (create\<^bsub>Y\<^esub> \<sigma>), 
                        lens_put = \<lambda> \<sigma> v. get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> (create\<^bsub>Y\<^esub> \<sigma>) v) \<rparr>"

definition id_lens :: "'a \<Longrightarrow> 'a" ("1\<^sub>L") where
[lens_defs]: "1\<^sub>L = \<lparr> lens_get = id, lens_put = (\<lambda> _. id) \<rparr>"

lemma lens_comp_assoc: "(X ;\<^sub>L Y) ;\<^sub>L Z = X ;\<^sub>L (Y ;\<^sub>L Z)"
  unfolding  lens_comp_def
  by auto

lemma lens_comp_left_id [simp]: "1\<^sub>L ;\<^sub>L X = X"
  unfolding id_lens_def lens_comp_def
  by simp

lemma lens_comp_right_id [simp]: "X ;\<^sub>L 1\<^sub>L = X"
  unfolding id_lens_def lens_comp_def
  by simp 

definition lens_override :: "'a \<Rightarrow> 'a \<Rightarrow> ('b \<Longrightarrow> 'a) \<Rightarrow> 'a" ("_ \<oplus>\<^sub>L _ on _" [95,0,96] 95) where
"S\<^sub>1 \<oplus>\<^sub>L S\<^sub>2 on X = put\<^bsub>X\<^esub> S\<^sub>1 (get\<^bsub>X\<^esub> S\<^sub>2)"

subsection {* Weak lenses *}

locale weak_lens =
  fixes x :: "'a \<Longrightarrow> 'b" (structure)
  assumes put_get: "get (put \<sigma> v) = v"
begin

  lemma create_get: "get (create v) = v"
    unfolding lens_create_def put_get
    by simp

  lemma create_inj: "inj create"
  proof -
    { fix g1 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a" and g2 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a"
      { assume "\<not> inj create \<and> g1 create \<noteq> g2 create"
        have "\<exists>f. inj create \<or> g1 f = g2 f \<or> \<not> inj f \<and> f (g1 f) \<noteq> f (g2 f)"
          by (metis (full_types) lens_create_def put_get) }
      then have "\<exists>f. inj create \<or> g1 f = g2 f \<or> \<not> inj f \<and> f (g1 f) \<noteq> f (g2 f)"
        by metis }
    then have "\<exists>f. \<forall>g1 g2. inj create \<or> (g1::'a) = g2 \<or> \<not> inj f \<and> (f g1::'b) \<noteq> f g2"
      by metis
    then show ?thesis
  by (meson injI)
  qed

  definition update :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b)" where
  [lens_defs]: "update f \<sigma> = put \<sigma> (f (get \<sigma>))"

  lemma get_update: "get (update f \<sigma>) = f (get \<sigma>)"
    unfolding put_get update_def
    by simp

  lemma view_determination: "put \<sigma> u = put \<rho> v \<Longrightarrow> u = v"
    by (metis put_get)

  lemma put_inj: "inj (put \<sigma>)"
    by (simp add: injI view_determination)
end

declare weak_lens.put_get [simp]
declare weak_lens.create_get [simp]

subsection {* Well-behaved lenses *}

locale wb_lens = weak_lens +
  assumes get_put: "put \<sigma> (get \<sigma>) = \<sigma>"
begin

  lemma put_twice: "put (put \<sigma> v) v = put \<sigma> v"
    by (metis get_put put_get)

  lemma put_surjectivity: "\<exists> \<rho> v. put \<rho> v = \<sigma>"
    using get_put by blast

  lemma source_stability: "\<exists> v. put \<sigma> v = \<sigma>"
    using get_put by auto

end

declare wb_lens.get_put [simp]

lemma wb_lens_weak [simp]: 
 assumes 1: "wb_lens x"
 shows "weak_lens x"
 using 1 unfolding wb_lens_def
 by simp 

lemma id_wb_lens: "wb_lens id_lens"
  by (unfold_locales, simp_all add: id_lens_def)

lemma unit_wb_lens: "wb_lens unit_lens"
  by (unfold_locales, simp_all add: unit_lens_def)

lemma comp_wb_lens: 
  assumes 1:"wb_lens x"
  and     2:" wb_lens y" 
  shows "wb_lens (x ;\<^sub>L y)"
  using 1 2  unfolding lens_comp_def
  by (unfold_locales, simp_all)

subsection {* Mainly well-behaved lenses *}

locale mwb_lens = weak_lens +
  assumes put_put: "put (put \<sigma> v) u = put \<sigma> u"
begin
  lemma update_comp: "update f (update g \<sigma>) = update (f \<circ> g) \<sigma>"
    unfolding put_get put_put update_def
    by simp 
end

declare mwb_lens.put_put [simp]

lemma mwb_lens_weak [simp]:
  assumes 1: "mwb_lens x"
  shows "weak_lens x"
  using 1 unfolding mwb_lens_def
  by simp 

lemma comp_mwb_lens: 
  assumes 1:"mwb_lens x"
  and     2:" mwb_lens y"
  shows "mwb_lens (x ;\<^sub>L y)"
  using 1 2 unfolding lens_comp_def
  by (unfold_locales, simp_all)

subsection {* Very well-behaved lenses *}

locale vwb_lens = wb_lens + mwb_lens
begin
  lemma source_determination:
    assumes 1:"get \<sigma> = get \<rho>"
    and     2:"put \<sigma> v = put \<rho> v"
    shows "\<sigma> = \<rho>"
    using 1 2 get_put put_put
    by metis 

  lemma put_eq: 
    assumes 1:"get \<sigma> = k" 
    and     2:"put \<sigma> u = put \<rho> v" 
    shows "put \<rho> k = \<sigma>"
    using 1 2 get_put put_put
    by metis    
end

lemma vwb_lens_wb [simp]: 
  assumes 1:"vwb_lens x"
  shows "wb_lens x"
  using 1 unfolding vwb_lens_def
  by simp

lemma vwb_lens_mwb [simp]: 
  assumes 1:"vwb_lens x"
  shows "mwb_lens x"
  using 1 unfolding vwb_lens_def
  by simp

lemma id_vwb_lens: "vwb_lens 1\<^sub>L"
  unfolding id_lens_def
  by (unfold_locales, simp_all)

lemma unit_vwb_lens: "vwb_lens 0\<^sub>L"
  unfolding unit_lens_def
  by (unfold_locales, simp_all)

lemma comp_vwb_lens: 
  assumes 1:"vwb_lens x"
  and     2:" vwb_lens y" 
  shows "vwb_lens (x ;\<^sub>L y)"
  using 1 2 unfolding lens_comp_def
  by (unfold_locales, simp_all)

lemma lens_comp_anhil [simp]: 
  assumes 1:"wb_lens x"
  shows "0\<^sub>L ;\<^sub>L x = 0\<^sub>L"
  using 1 unfolding unit_lens_def lens_comp_def comp_def
  by simp 

subsection {* Ineffectual lenses *}

locale ief_lens = weak_lens +
  assumes put_inef: "put \<sigma> v = \<sigma>"
begin

sublocale vwb_lens
proof
  fix \<sigma> v u
  show "put \<sigma> (get \<sigma>) = \<sigma>"
    by (simp add: put_inef)  
  show "put (put \<sigma> v) u = put \<sigma> u"
    by (simp add: put_inef)
qed

lemma ineffectual_const_get:
  "\<exists> v.  \<forall> \<sigma>. get \<sigma> = v"
  by (metis create_get lens_create_def put_inef)

end

lemma unit_ief_lens: "ief_lens 0\<^sub>L"
  by (unfold_locales, simp_all add: unit_lens_def)

abbreviation "eff_lens X \<equiv> (weak_lens X \<and> (\<not> ief_lens X))"

subsection {* Lens independence *}

(* FIXME: Should this be another locale? *)

definition lens_indep :: "('a \<Longrightarrow> 'c) \<Rightarrow> ('b \<Longrightarrow> 'c) \<Rightarrow> bool" (infix "\<bowtie>" 50) where
"x \<bowtie> y = (\<forall> u v \<sigma>. lens_put x (lens_put y \<sigma> v) u = lens_put y (lens_put x \<sigma> u) v
                    \<and> lens_get x (lens_put y \<sigma> v) = lens_get x \<sigma>
                    \<and> lens_get y (lens_put x \<sigma> u) = lens_get y \<sigma>)"

lemma lens_indepI:
  assumes 1:"\<forall> u v \<sigma>. lens_put x (lens_put y \<sigma> v) u = lens_put y (lens_put x \<sigma> u) v"
  and     2:"\<forall> v \<sigma>. lens_get x (lens_put y \<sigma> v) = lens_get x \<sigma>"
  and     3:"\<forall> u \<sigma>. lens_get y (lens_put x \<sigma> u) = lens_get y \<sigma>"
  shows " x \<bowtie> y"
  using 1 2 3 unfolding lens_indep_def
  by simp

text {* Independence is irreflexive for effectual lenses *}

lemma lens_indep_sym:  "x \<bowtie> y \<Longrightarrow> y \<bowtie> x"
  unfolding lens_indep_def
  by simp

lemma lens_indep_comm:
  assumes 1: "x \<bowtie> y"
  shows "lens_put x (lens_put y \<sigma> v) u = lens_put y (lens_put x \<sigma> u) v"
  using 1 unfolding lens_indep_def
  by simp

lemma lens_indep_get [simp]:
  assumes 1:"x \<bowtie> y"
  shows "lens_get x (lens_put y \<sigma> v) = lens_get x \<sigma>"
  using 1 lens_indep_def by fastforce

lemma plus_wb_lens:
  assumes 1:"wb_lens x" and 2:"wb_lens y" and 3:"x \<bowtie> y"
  shows "wb_lens (x +\<^sub>L y)"
  using 1 2 3 unfolding lens_plus_def  
  by (unfold_locales, simp_all add: lens_indep_sym prod.case_eq_if)


lemma fst_lens_plus:
  assumes 1:"wb_lens y"
  shows "fst\<^sub>L ;\<^sub>L (x +\<^sub>L y) = x"
  using 1 unfolding fst_lens_def lens_plus_def lens_comp_def comp_def
  by simp

lemma fst_snd_lens_indep:
  "fst\<^sub>L \<bowtie> snd\<^sub>L"
  unfolding lens_indep_def fst_lens_def snd_lens_def
  by simp 

text {* The second law requires independence as we have to apply x first, before y *}

lemma snd_lens_prod:
  assumes 1:"wb_lens x" 
  and     2:"x \<bowtie> y"
  shows "snd\<^sub>L ;\<^sub>L (x +\<^sub>L y) = y"
  using 1 2 unfolding  snd_lens_def lens_plus_def lens_comp_def comp_def
  by (simp_all add: lens_indep_comm)

lemma plus_mwb_lens:
  assumes 1:"mwb_lens x" and 2:"mwb_lens y" and 3:"x \<bowtie> y"
  shows "mwb_lens (x +\<^sub>L y)"
  using 1 2 3 unfolding lens_plus_def 
  by (unfold_locales) (simp_all add: lens_indep_comm Product_Type.split_beta)

lemma lens_indep_quasi_irrefl: 
  assumes 1:"wb_lens x"
  and     2:"eff_lens x"
  shows   " \<not> (x \<bowtie> x)"
  using 1 2 unfolding lens_indep_def ief_lens_def ief_lens_axioms_def
proof (auto)
  fix \<sigma> :: 'b and v :: 'a
  assume "put\<^bsub>x\<^esub> \<sigma> v \<noteq> \<sigma>"
  then have "\<exists>b. put\<^bsub>x\<^esub> b v \<noteq> b"
    by metis
  then have "\<exists>b. wb_lens x \<and> put\<^bsub>x\<^esub> b v \<noteq> b"
    by (metis "1") (* failed *)
  then show "\<exists>a aa b. aa = get\<^bsub>x\<^esub> b \<longrightarrow> put\<^bsub>x\<^esub> b a = put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> b a) (get\<^bsub>x\<^esub> b) \<longrightarrow> a \<noteq> get\<^bsub>x\<^esub> b"
    by (metis (full_types) wb_lens.get_put)
qed

lemma lens_indep_left_comp:
  assumes 1:"mwb_lens z"
  and     2:"x \<bowtie> y"
  shows"(x ;\<^sub>L z) \<bowtie> (y ;\<^sub>L z)"
  using 1 2 unfolding lens_comp_def lens_indep_def
  by auto

lemma lens_indep_right_comp:
  assumes 1:"y \<bowtie> z"
  shows "(x ;\<^sub>L y) \<bowtie> (x ;\<^sub>L z)"
  using 1 unfolding lens_indep_def lens_comp_def
  by auto

lemma lens_indep_left_ext:
  assumes 1:"y \<bowtie> z" 
  shows"(x ;\<^sub>L y) \<bowtie> z" 
  using 1 unfolding lens_indep_def lens_comp_def
  by auto

lemma plus_vwb_lens:
  assumes "vwb_lens x" "vwb_lens y" "x \<bowtie> y"
  shows "vwb_lens (x +\<^sub>L y)"
  using assms unfolding lens_indep_def lens_plus_def
  by (unfold_locales) (simp_all add: lens_indep_sym prod.case_eq_if)

lemma fst_vwb_lens: "vwb_lens fst\<^sub>L"
  unfolding fst_lens_def
  by (unfold_locales, simp_all add:  prod.case_eq_if)

lemma snd_vwb_lens: "vwb_lens snd\<^sub>L"
  unfolding snd_lens_def
  by (unfold_locales, simp_all add: prod.case_eq_if)

subsection {* Bijective lenses *}

text {* Bijective lenses express that two views of a particular source are equivalent. *}

locale bij_lens = weak_lens +
  assumes strong_get_put: "put \<sigma> (get \<rho>) = \<rho>"
begin

sublocale vwb_lens
proof
  fix \<sigma> v u
  show "put \<sigma> (get \<sigma>) = \<sigma>"
    by (simp add: strong_get_put)
  show "put (put \<sigma> v) u = put \<sigma> u"
    by (metis put_get strong_get_put)
qed

  lemma put_surj: "surj (put \<sigma>)"
    by (metis strong_get_put surj_def)

  lemma put_bij: "bij (put \<sigma>)"
    by (simp add: bijI put_inj put_surj)

  lemma put_is_create: "put \<sigma> v = create v"
    by (metis create_get strong_get_put)

  lemma get_create: "create (get \<sigma>) = \<sigma>"
    by (metis put_get put_is_create source_stability)

end

declare bij_lens.strong_get_put [simp]
declare bij_lens.get_create [simp]

lemma bij_lens_weak [simp]: 
 assumes 1:"bij_lens x"
 shows "weak_lens x"
 using 1 bij_lens.axioms(1)
 by auto

lemma bij_lens_vwb [simp]: 
  assumes 1:"bij_lens x"
  shows "vwb_lens x"
  using 1
  by (unfold_locales, simp_all add: bij_lens.put_is_create)

definition lens_inv :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('b \<Longrightarrow> 'a)" where
[lens_defs]: "lens_inv x = \<lparr> lens_get = create\<^bsub>x\<^esub>, lens_put = \<lambda> \<sigma>. get\<^bsub>x\<^esub> \<rparr>"

lemma id_bij_lens: "bij_lens 1\<^sub>L"
  unfolding id_lens_def
  by (unfold_locales, simp_all)

lemma inv_id_lens: "lens_inv 1\<^sub>L = 1\<^sub>L"
  unfolding lens_inv_def id_lens_def 
  by (auto simp add: lens_create_def)

lemma lens_inv_bij: 
  assumes 1:"bij_lens X"
  shows "bij_lens (lens_inv X)"
  using 1 unfolding lens_inv_def
  by (unfold_locales, simp_all add:lens_create_def)

subsection {* Order and equivalence on lenses *}

text {* A lens $X$ is a sub-lens of $Y$ if there is a well-behaved lens $Z$ such that $X = Z ; Y$,
  or in other words if $X$ can be expressed purely in terms of $Y$. *}

definition sublens :: "('a \<Longrightarrow> 'c) \<Rightarrow> ('b \<Longrightarrow> 'c) \<Rightarrow> bool" (infix "\<subseteq>\<^sub>L" 55) where
[lens_defs]: "sublens X Y = (\<exists> Z :: ('a, 'b) lens. vwb_lens Z \<and> X = Z ;\<^sub>L Y)"

lemma sublens_pres_mwb:
  assumes 1:"mwb_lens Y" and 2:"X \<subseteq>\<^sub>L Y"
  shows  "mwb_lens X"
  using 1 2 unfolding sublens_def lens_comp_def
  by (unfold_locales, auto)

lemma sublens_pres_wb:
  assumes 1:"wb_lens Y" and 2:"X \<subseteq>\<^sub>L Y"
  shows "wb_lens X"
  using 1 2 unfolding sublens_def lens_comp_def
  by (unfold_locales, auto)

lemma sublens_pres_vwb:
  assumes 1: "vwb_lens Y" and 2:"X \<subseteq>\<^sub>L Y"
  shows "vwb_lens X"
  using 1 2 unfolding sublens_def lens_comp_def
  by (unfold_locales, auto)

lemma sublens_refl:
  "X \<subseteq>\<^sub>L X"
  using id_vwb_lens sublens_def by force

lemma sublens_trans:
  assumes 1:"X \<subseteq>\<^sub>L Y" and 2 :"Y \<subseteq>\<^sub>L Z"
  shows "X \<subseteq>\<^sub>L Z"
  using 1 2 
  apply (auto simp add: sublens_def lens_comp_assoc)
  apply (rename_tac Z\<^sub>1 Z\<^sub>2)
  apply (rule_tac x="Z\<^sub>1 ;\<^sub>L Z\<^sub>2" in exI)
  apply (simp add: lens_comp_assoc)
  using comp_vwb_lens apply blast
done

lemma sublens_least: 
  assumes 1:"wb_lens X"
  shows "0\<^sub>L \<subseteq>\<^sub>L X"
  using 1 sublens_def unit_vwb_lens by fastforce

lemma sublens_greatest: 
  assumes 1: "vwb_lens X"
  shows "X \<subseteq>\<^sub>L 1\<^sub>L"
  using 1 unfolding sublens_def
  by simp

lemma sublens_put_put:
  assumes 1:"mwb_lens X"
  and     2:"Y \<subseteq>\<^sub>L X"
  shows "lens_put X (lens_put Y \<sigma> v) u = lens_put X \<sigma> u"
  using 1 2 unfolding sublens_def lens_comp_def 
  by auto

lemma sublens_obs_get:
  assumes 1:"mwb_lens X" and 2:" Y \<subseteq>\<^sub>L X"
  shows "get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> \<sigma> v) = get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> \<rho> v)"
  using 1 2 unfolding sublens_def lens_comp_def
  by auto

definition lens_equiv :: "('a \<Longrightarrow> 'c) \<Rightarrow> ('b \<Longrightarrow> 'c) \<Rightarrow> bool" (infix "\<approx>\<^sub>L" 51) where
[lens_defs]: "lens_equiv X Y = (X \<subseteq>\<^sub>L Y \<and> Y \<subseteq>\<^sub>L X)"

lemma lens_equivI [intro]:
  assumes 1:"X \<subseteq>\<^sub>L Y" and 2:"Y \<subseteq>\<^sub>L X"
  shows "X \<approx>\<^sub>L Y"
  using 1 2 unfolding lens_equiv_def
  by simp

lemma lens_equiv_refl:
  "X \<approx>\<^sub>L X"
  unfolding lens_equiv_def using sublens_refl
  by simp

lemma lens_equiv_sym:
  assumes 1: "X \<approx>\<^sub>L Y"
  shows  "Y \<approx>\<^sub>L X"
  using 1 unfolding lens_equiv_def
  by simp

lemma lens_equiv_trans:
  assumes 1: "X \<approx>\<^sub>L Y" and 2:"Y \<approx>\<^sub>L Z" 
  shows"X \<approx>\<^sub>L Z"
  using 1 2 unfolding lens_equiv_def
  using sublens_trans sublens_trans 
  by auto 

lemma unit_lens_indep: "0\<^sub>L \<bowtie> X"
  unfolding unit_lens_def lens_indep_def lens_equiv_def
  by simp 

lemma fst_snd_id_lens: "fst\<^sub>L +\<^sub>L snd\<^sub>L = 1\<^sub>L"
  unfolding lens_plus_def fst_lens_def snd_lens_def id_lens_def
  by auto

lemma sublens_pres_indep:
  assumes 1:"X \<subseteq>\<^sub>L Y" and 2: "Y \<bowtie> Z"
  shows"X \<bowtie> Z"
  using 1 2 unfolding lens_indep_def sublens_def lens_comp_def
  by auto

lemma plus_pres_lens_indep: 
  assumes 1:"X \<bowtie> Z" and 2:"Y \<bowtie> Z" 
  shows "(X +\<^sub>L Y) \<bowtie> Z"
  using 1 2 unfolding lens_indep_def lens_plus_def
  by auto

lemma lens_comp_indep_cong_left:
  assumes 1:"mwb_lens Z"
  and     2:"X ;\<^sub>L Z \<bowtie> Y ;\<^sub>L Z"
  shows "X \<bowtie> Y"
  using 1 2 unfolding lens_indep_def lens_comp_def
proof (auto)
  fix u :: 'c and v :: 'd and \<sigma> :: 'a
  assume a1: "mwb_lens Z"
  assume a2: "\<forall>u v \<sigma>. put\<^bsub>Z\<^esub> \<sigma> (put\<^bsub>X\<^esub> (put\<^bsub>Y\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) v) u) = 
              put\<^bsub>Z\<^esub> \<sigma> (put\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) u) v) \<and> get\<^bsub>X\<^esub> (put\<^bsub>Y\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) v) = 
              get\<^bsub>X\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) \<and> get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) u) = get\<^bsub>Y\<^esub> (get\<^bsub>Z\<^esub> \<sigma>)"
  have "weak_lens Z"
    using a1 by (metis mwb_lens_weak)
  then show "put\<^bsub>X\<^esub> (put\<^bsub>Y\<^esub> \<sigma> v) u = put\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> \<sigma> u) v"
    using weak_lens.put_get a2 by metis 
next
  fix v :: 'd and \<sigma> :: 'a
  assume a1:"mwb_lens Z "
  assume a2:"\<forall>u v \<sigma>.
              put\<^bsub>Z\<^esub> \<sigma> (put\<^bsub>X\<^esub> (put\<^bsub>Y\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) v) u) =
              put\<^bsub>Z\<^esub> \<sigma> (put\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) u) v) \<and>
              get\<^bsub>X\<^esub> (put\<^bsub>Y\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) v) = get\<^bsub>X\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) \<and>
              get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) u) = get\<^bsub>Y\<^esub> (get\<^bsub>Z\<^esub> \<sigma>)"
  show "get\<^bsub>X\<^esub> (put\<^bsub>Y\<^esub> \<sigma> v) = get\<^bsub>X\<^esub> \<sigma>"
  using a1 a2 mwb_lens_weak weak_lens.put_get by metis 
next 
  fix \<sigma>::'a and u::'c
  assume a1:"mwb_lens Z"
  assume a2:" \<forall>u v \<sigma>.
              put\<^bsub>Z\<^esub> \<sigma> (put\<^bsub>X\<^esub> (put\<^bsub>Y\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) v) u) =
              put\<^bsub>Z\<^esub> \<sigma> (put\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) u) v) \<and>
              get\<^bsub>X\<^esub> (put\<^bsub>Y\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) v) = get\<^bsub>X\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) \<and>
              get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> (get\<^bsub>Z\<^esub> \<sigma>) u) = get\<^bsub>Y\<^esub> (get\<^bsub>Z\<^esub> \<sigma>)"
  show "get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> \<sigma> u) = get\<^bsub>Y\<^esub> \<sigma>"
  using a1 a2 mwb_lens_weak weak_lens.put_get by (metis (full_types))
qed
  
lemma lens_comp_indep_cong:
  assumes 1:"mwb_lens x" and 2:"mwb_lens y" and 3:"mwb_lens z"
  shows "(x ;\<^sub>L z) \<bowtie> (y ;\<^sub>L z) \<longleftrightarrow> x \<bowtie> y"
  using 1 2 3 lens_comp_indep_cong_left lens_indep_left_comp by blast

lemma lens_quotient_mwb:
  assumes 1:"mwb_lens Y" and 2:"X \<subseteq>\<^sub>L Y" 
  shows"mwb_lens (X /\<^sub>L Y)"
  using 1 2 unfolding lens_quotient_def lens_create_def sublens_def lens_comp_def comp_def
  by (unfold_locales, auto)  

subsection {* Lens algebraic laws *}

lemma plus_lens_distr: 
  assumes 1:"mwb_lens Z"
  shows "(X +\<^sub>L Y) ;\<^sub>L Z = (X ;\<^sub>L Z) +\<^sub>L (Y ;\<^sub>L Z)"
  using 1 unfolding lens_comp_def lens_plus_def comp_def
  by auto 

text {* This law explains the behaviour of lens quotient. *}

lemma lens_quotient_comp:
  assumes 1:"weak_lens Y" and 2:"X \<subseteq>\<^sub>L Y"  
  shows "(X /\<^sub>L Y) ;\<^sub>L Y = X"
  using 1 2 unfolding lens_quotient_def lens_comp_def comp_def sublens_def 
  by auto

lemma lens_comp_quotient:
  assumes 1:"weak_lens Y"
  shows "(X ;\<^sub>L Y) /\<^sub>L Y = X"
  using 1 unfolding lens_quotient_def lens_comp_def
  by simp 

lemma lens_quotient_id: 
  assumes 1:"weak_lens X"
  shows "(X /\<^sub>L X) = 1\<^sub>L"
  using 1 unfolding lens_quotient_def id_lens_def
  by force

lemma lens_quotient_id_denom: "X /\<^sub>L 1\<^sub>L = X"
  unfolding  lens_quotient_def id_lens_def lens_create_def
  by simp 
 
lemma lens_quotient_unit: 
  assumes 1:"weak_lens X" 
  shows "(0\<^sub>L /\<^sub>L X) = 0\<^sub>L"
  using 1 unfolding lens_quotient_def unit_lens_def
  by simp

lemma lens_quotient_plus:
  assumes 1:"mwb_lens Z" and 2:"X \<subseteq>\<^sub>L Z" 
  shows" (X +\<^sub>L Y) /\<^sub>L Z = (X /\<^sub>L Z) +\<^sub>L (Y /\<^sub>L Z)"
  using 1 2 unfolding lens_quotient_def lens_plus_def sublens_def lens_comp_def comp_def
  apply (auto simp add: )
  apply (rule ext)+
  apply (simp add: prod.case_eq_if)
done

lemma plus_pred_sublens: 
  assumes 1: "mwb_lens Z" and 2:"X \<subseteq>\<^sub>L Z" and 3:"Y \<subseteq>\<^sub>L Z" and 4:"X \<bowtie> Y" 
  shows "(X +\<^sub>L Y) \<subseteq>\<^sub>L Z"
  using 1 2 3 4
proof -
  have "\<forall>l la. (\<not> (l::'c \<Longrightarrow> 'b) \<subseteq>\<^sub>L (la::'a \<Longrightarrow> _) \<or> (\<exists>lb. vwb_lens lb \<and> lb ;\<^sub>L la = l)) \<and> ((\<forall>lb. \<not> vwb_lens lb \<or> lb ;\<^sub>L la \<noteq> l) \<or> l \<subseteq>\<^sub>L la)"
    by (metis sublens_def)
  then obtain ll :: "('c \<Longrightarrow> 'b) \<Rightarrow> ('a \<Longrightarrow> 'b) \<Rightarrow> 'c \<Longrightarrow> 'a" where
    f1: "\<forall>l la. (\<not> l \<subseteq>\<^sub>L la \<or> vwb_lens (ll l la) \<and> ll l la ;\<^sub>L la = l) \<and> ((\<forall>lb. \<not> vwb_lens lb \<or> lb ;\<^sub>L la \<noteq> l) \<or> l \<subseteq>\<^sub>L la)"
    by moura
  obtain lla :: "('d \<Longrightarrow> 'b) \<Rightarrow> ('a \<Longrightarrow> 'b) \<Rightarrow> 'd \<Longrightarrow> 'a" where
    f2: "\<forall>l la. (\<not> l \<subseteq>\<^sub>L la \<or> vwb_lens (lla l la) \<and> lla l la ;\<^sub>L la = l) \<and> ((\<forall>lb. \<not> vwb_lens lb \<or> lb ;\<^sub>L la \<noteq> l) \<or> l \<subseteq>\<^sub>L la)"
    by (metis sublens_def)
  have f3: "ll X Z ;\<^sub>L Z = X"
    using f1 by (metis "2") (* > 1.0 s, timed out *)
  have f4: "lla Y Z ;\<^sub>L Z = Y"
    using f2 by (metis "3") (* > 1.0 s, timed out *)
  have f5: "\<forall>l la. \<not> (l::'c \<Longrightarrow> 'a) ;\<^sub>L Z \<bowtie> (la::'d \<Longrightarrow> 'a) ;\<^sub>L Z \<or> l \<bowtie> la"
    by (metis "1" lens_comp_indep_cong_left) (* > 1.0 s, timed out *)
  have f6: "\<forall>l la. ((l::'c \<Longrightarrow> 'a) +\<^sub>L (la::'d \<Longrightarrow> 'a)) ;\<^sub>L Z = l ;\<^sub>L Z +\<^sub>L la ;\<^sub>L Z"
    by (metis "1" plus_lens_distr) (* > 1.0 s, timed out *)
  have "\<not> X \<bowtie> Y \<or> ll X Z \<bowtie> lla Y Z"
    using f5 f4 f3 by presburger
  then have "ll X Z \<bowtie> lla Y Z"
    by (metis "4") (* > 1.0 s, timed out *)
  then have "vwb_lens (ll X Z +\<^sub>L lla Y Z) \<or> \<not> vwb_lens (ll X Z) \<or> \<not> Y \<subseteq>\<^sub>L Z"
    using f2 plus_vwb_lens by blast
  then have "\<not> vwb_lens (ll X Z) \<or> vwb_lens (ll X Z +\<^sub>L lla Y Z)"
    by (metis "3") (* > 1.0 s, timed out *)
  then have "vwb_lens (ll X Z +\<^sub>L lla Y Z) \<or> \<not> X \<subseteq>\<^sub>L Z"
    using f1 by meson
  then have "vwb_lens (ll X Z +\<^sub>L lla Y Z)"
    by (metis "2") (* > 1.0 s, timed out *)
  then have f7: "\<forall>l la. la \<subseteq>\<^sub>L (l::'a \<Longrightarrow> 'b) \<or> (ll X Z +\<^sub>L lla Y Z) ;\<^sub>L l \<noteq> la"
    using sublens_def by blast
  have "X +\<^sub>L Y = X +\<^sub>L lla Y Z ;\<^sub>L Z"
    using f4 by metis
  then show ?thesis
    using f7 f6 f3 by (metis (full_types))
qed 

lemma lens_plus_sub_assoc_1:
   "X +\<^sub>L Y +\<^sub>L Z \<subseteq>\<^sub>L (X +\<^sub>L Y) +\<^sub>L Z"
  unfolding sublens_def
  apply (rule_tac x="(fst\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L (snd\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L snd\<^sub>L" in exI)
  apply (auto)
  apply (rule plus_vwb_lens)
  apply (simp add: comp_vwb_lens fst_vwb_lens)
  apply (rule plus_vwb_lens)
  apply (simp add: comp_vwb_lens fst_vwb_lens snd_vwb_lens)
  apply (simp add: snd_vwb_lens)
  apply (simp add: fst_snd_lens_indep lens_indep_left_ext)
  apply (rule lens_indep_sym)
  apply (rule plus_pres_lens_indep)
  using fst_snd_lens_indep fst_vwb_lens lens_indep_left_comp lens_indep_sym vwb_lens_mwb apply blast
  using fst_snd_lens_indep lens_indep_left_ext lens_indep_sym apply blast
  apply (auto simp add: lens_plus_def lens_comp_def fst_lens_def snd_lens_def prod.case_eq_if split_beta')[1]
done

lemma lens_plus_sub_assoc_2:
  "(X +\<^sub>L Y) +\<^sub>L Z \<subseteq>\<^sub>L X +\<^sub>L Y +\<^sub>L Z"
  apply (simp add: sublens_def)
  apply (rule_tac x="(fst\<^sub>L +\<^sub>L (fst\<^sub>L ;\<^sub>L snd\<^sub>L)) +\<^sub>L (snd\<^sub>L ;\<^sub>L snd\<^sub>L)" in exI)
  apply (auto)
  apply (rule plus_vwb_lens)
  apply (rule plus_vwb_lens)
  apply (simp add: fst_vwb_lens)
  apply (simp add: comp_vwb_lens fst_vwb_lens snd_vwb_lens)
  apply (rule lens_indep_sym)
  apply (rule lens_indep_left_ext)
  using fst_snd_lens_indep lens_indep_sym apply blast
  apply (auto intro: comp_vwb_lens simp add: snd_vwb_lens)
  apply (rule plus_pres_lens_indep)
  apply (simp add: fst_snd_lens_indep lens_indep_left_ext lens_indep_sym)
  apply (simp add: fst_snd_lens_indep lens_indep_left_comp snd_vwb_lens)
  apply (auto simp add: lens_plus_def lens_comp_def fst_lens_def snd_lens_def prod.case_eq_if split_beta')[1]
done

lemma lens_plus_assoc:
  "(X +\<^sub>L Y) +\<^sub>L Z \<approx>\<^sub>L X +\<^sub>L Y +\<^sub>L Z"
  unfolding lens_equiv_def
  by (simp add: lens_plus_sub_assoc_1 lens_plus_sub_assoc_2)

lemma lens_plus_swap:
  assumes 1:"X \<bowtie> Y" 
  shows "(snd\<^sub>L +\<^sub>L fst\<^sub>L) ;\<^sub>L (X +\<^sub>L Y) = (Y +\<^sub>L X)"
  using 1 unfolding lens_plus_def fst_lens_def snd_lens_def id_lens_def lens_comp_def
  by (auto simp add: lens_indep_comm)

lemma lens_plus_sub_comm: 
  assumes 1:"X \<bowtie> Y"
  shows "X +\<^sub>L Y \<subseteq>\<^sub>L Y +\<^sub>L X"
  using 1
  apply (simp add: sublens_def)
  apply (rule_tac x="snd\<^sub>L +\<^sub>L fst\<^sub>L" in exI)
  apply (auto)
  apply (simp add: fst_snd_lens_indep fst_vwb_lens lens_indep_sym plus_vwb_lens snd_vwb_lens)
  apply (simp add: lens_indep_sym lens_plus_swap)
done
  
lemma lens_plus_comm: 
  assumes 1:"X \<bowtie> Y" 
  shows   "X +\<^sub>L Y \<approx>\<^sub>L Y +\<^sub>L X"
  using 1
  by (simp add: lens_equivI lens_indep_sym lens_plus_sub_comm)

lemma lens_plus_ub: 
  assumes 1: "wb_lens Y"
  shows"X \<subseteq>\<^sub>L X +\<^sub>L Y"
  using 1 sublens_def fst_lens_plus fst_vwb_lens
  by metis

lemma lens_plus_right_sublens:
  assumes 1:"vwb_lens Y" and 2:"Y \<bowtie> Z" and 3:"X \<subseteq>\<^sub>L Z" 
  shows"X \<subseteq>\<^sub>L Y +\<^sub>L Z"
  using 1 2 3
  apply (auto simp add: sublens_def)
  apply (rename_tac Z')
  apply (rule_tac x="Z' ;\<^sub>L snd\<^sub>L" in exI)
  apply (auto)
  using comp_vwb_lens snd_vwb_lens apply blast
  apply (simp add: lens_comp_assoc snd_lens_prod)
done

lemma lens_comp_lb: 
  assumes 1:"vwb_lens X" 
  shows  "X ;\<^sub>L Y \<subseteq>\<^sub>L Y"
  using 1 unfolding sublens_def
  by auto 

lemma lens_unit_plus_sublens_1: "X \<subseteq>\<^sub>L 0\<^sub>L +\<^sub>L X"
  by (metis lens_comp_lb snd_lens_prod snd_vwb_lens unit_lens_indep unit_wb_lens)

lemma lens_unit_prod_sublens_2: "0\<^sub>L +\<^sub>L x \<subseteq>\<^sub>L x"
  apply (auto simp add: sublens_def)
  apply (rule_tac x="0\<^sub>L +\<^sub>L 1\<^sub>L" in exI)
  apply (auto)
  apply (rule plus_vwb_lens)
  apply (simp add: unit_vwb_lens)
  apply (simp add: id_vwb_lens)
  apply (simp add: unit_lens_indep)
  apply (auto simp add: lens_plus_def unit_lens_def lens_comp_def id_lens_def prod.case_eq_if comp_def)
  apply (rule ext)
  apply (rule ext)
  apply (auto)
done

lemma lens_plus_left_unit: "0\<^sub>L +\<^sub>L X \<approx>\<^sub>L X"
  by (simp add: lens_equivI lens_unit_plus_sublens_1 lens_unit_prod_sublens_2)
  
lemma lens_plus_right_unit: "X +\<^sub>L 0\<^sub>L \<approx>\<^sub>L X"
  using lens_equiv_trans lens_indep_sym lens_plus_comm lens_plus_left_unit unit_lens_indep by blast

lemma bij_lens_inv_left:
  assumes 1:"bij_lens X"
  shows "lens_inv X ;\<^sub>L X = 1\<^sub>L"
  by (auto simp add: 1 lens_inv_def lens_comp_def comp_def id_lens_def, rule ext, auto)

lemma bij_lens_inv_right:
  assumes 1:"bij_lens X" 
  shows "X ;\<^sub>L lens_inv X = 1\<^sub>L"
  by (auto simp add: 1 lens_inv_def lens_comp_def comp_def id_lens_def, rule ext, auto)

text {* Bijective lenses are precisely those that are equivalent to identity *}

lemma bij_lens_equiv_id:
  "bij_lens X = X \<approx>\<^sub>L 1\<^sub>L"
  apply (auto)
  apply (rule lens_equivI)
  apply (simp_all add: sublens_def)
  apply (rule_tac x="lens_inv X" in exI)
  apply (simp add: bij_lens_inv_left lens_inv_bij)
  apply (auto simp add: lens_equiv_def sublens_def id_lens_def lens_comp_def comp_def)
  apply (unfold_locales)
  apply (simp)
  apply (simp)
  apply (metis (no_types, lifting) vwb_lens_wb wb_lens_weak weak_lens.put_get)
done

lemma bij_lens_equiv:
  assumes 1:"bij_lens X" and 2:"X \<approx>\<^sub>L Y" 
  shows "bij_lens Y"
  using 1 2
  by (meson bij_lens_equiv_id lens_equiv_def sublens_trans)

lemma lens_id_unique:
  assumes 1:"weak_lens Y" and 2:"Y = X ;\<^sub>L Y"
  shows"X = 1\<^sub>L"
proof -
  have f1: "\<forall>l. ((l::'a \<Longrightarrow> 'a) ;\<^sub>L Y) /\<^sub>L Y = l"
    by (metis "1" lens_comp_quotient)
  then have "Y /\<^sub>L Y = X"
    by (metis "2") 
  then show ?thesis
    using f1 by (metis (no_types) lens_comp_left_id)
qed

lemma bij_lens_via_comp_id_left:
  assumes 1:"wb_lens X" and 2:"wb_lens Y" and 3: "X ;\<^sub>L Y = 1\<^sub>L" 
  shows "bij_lens X"
  using 1 2 3
  apply (cases Y)
  apply (cases X)
  apply (auto simp add: lens_comp_def comp_def id_lens_def fun_eq_iff)
  apply (unfold_locales)
  apply (simp_all)
  using vwb_lens_wb wb_lens_weak weak_lens.put_get apply fastforce
  apply (metis select_convs(1) select_convs(2) wb_lens_weak weak_lens.put_get)
done

lemma bij_lens_via_comp_id_right:
  assumes 1:"wb_lens X" and 2:"wb_lens Y" and 3:"X ;\<^sub>L Y = 1\<^sub>L" 
  shows  "bij_lens Y"
proof -
  have "\<forall>l. \<not> wb_lens (l::'b \<Longrightarrow> 'a) \<or> weak_lens l"
    by (metis wb_lens_weak)
  then have f1: "weak_lens Y"
    by (metis "2") 
  have f2: "\<forall>l la. \<not> wb_lens (l::'b \<Longrightarrow> 'a) \<or> \<not> wb_lens la \<or> l ;\<^sub>L la \<noteq> 1\<^sub>L \<or> bij_lens l"
    by (meson bij_lens_via_comp_id_left)
  have "Y = Y ;\<^sub>L X ;\<^sub>L Y"
    by (metis "3" lens_comp_right_id) 
  then have "Y ;\<^sub>L X = 1\<^sub>L"
    using f1 by (simp add: lens_comp_assoc lens_id_unique)
  then show ?thesis
    using f2 "1" "2" by auto
qed


text {* An equivalence can be proved by demonstrating a suitable bijective lens *}

lemma lens_equiv_via_bij:
  assumes "bij_lens Z" "X = Z ;\<^sub>L Y"
  shows "X \<approx>\<^sub>L Y"
  using assms
proof -
  have "bij_lens (lens_inv Z)"
    using assms(1)
    by (metis lens_inv_bij)
  then show ?thesis
    using assms
    by (metis (no_types) bij_lens_inv_left bij_lens_vwb lens_comp_assoc lens_comp_lb 
              lens_comp_left_id lens_equivI)
qed

lemma lens_equiv_iff_bij:
  assumes "weak_lens Y"
  shows "X \<approx>\<^sub>L Y = (\<exists> Z. bij_lens Z \<and> X = Z ;\<^sub>L Y)"
  apply (rule iffI)
  apply (auto simp add: lens_equiv_def sublens_def lens_id_unique)[1]
  apply (rename_tac Z\<^sub>1 Z\<^sub>2)
  apply (rule_tac x="Z\<^sub>1" in exI)
  apply (simp)
  apply (subgoal_tac "Z\<^sub>2 ;\<^sub>L Z\<^sub>1 = 1\<^sub>L")
  apply (meson bij_lens_via_comp_id_right vwb_lens_wb)
  apply (metis assms lens_comp_assoc lens_id_unique)
  using lens_equiv_via_bij apply blast
done

text {* Lens override laws *}

lemma lens_override_id:
  "S\<^sub>1 \<oplus>\<^sub>L S\<^sub>2 on 1\<^sub>L = S\<^sub>2"
  by (simp add: lens_override_def id_lens_def)

lemma lens_override_unit:
  "S\<^sub>1 \<oplus>\<^sub>L S\<^sub>2 on 0\<^sub>L = S\<^sub>1"
  by (simp add: lens_override_def unit_lens_def)

lemma lens_override_overshadow:
  assumes "mwb_lens Y"  "X \<subseteq>\<^sub>L Y"
  shows "(S\<^sub>1 \<oplus>\<^sub>L S\<^sub>2 on X) \<oplus>\<^sub>L S\<^sub>3 on Y = S\<^sub>1 \<oplus>\<^sub>L S\<^sub>3 on Y"
  using assms by (simp add: lens_override_def sublens_put_put)

(*
lemma lens_override_commute:
  assumes "bij_lens (X +\<^sub>L Y)" "vwb_lens X" "vwb_lens Y" "X \<bowtie> Y"
  shows "S\<^sub>1 \<oplus>\<^sub>L S\<^sub>2 on X = S\<^sub>2 \<oplus>\<^sub>L S\<^sub>1 on Y"
proof -
  have "1\<^sub>L \<subseteq>\<^sub>L X +\<^sub>L Y"
    using assms(1) bij_lens_equiv_id lens_equiv_def by blast
  with assms show ?thesis
    apply (simp add: lens_override_def)
*)

lemma lens_override_plus:
  assumes 1:"X \<bowtie> Y" 
  shows"S\<^sub>1 \<oplus>\<^sub>L S\<^sub>2 on (X +\<^sub>L Y) = (S\<^sub>1 \<oplus>\<^sub>L S\<^sub>2 on X) \<oplus>\<^sub>L S\<^sub>2 on Y"
  using 1
  by (simp add: lens_indep_comm lens_override_def lens_plus_def)

subsection {* Lens implementations *}

text {* Product functor lens *}

definition prod_lens :: "('a \<Longrightarrow> 'c) \<Rightarrow> ('b \<Longrightarrow> 'd) \<Rightarrow> ('a \<times> 'b \<Longrightarrow> 'c \<times> 'd)" (infixr "\<times>\<^sub>L" 85) where
[lens_defs]: "prod_lens X Y = \<lparr> lens_get = map_prod get\<^bsub>X\<^esub> get\<^bsub>Y\<^esub>
                              , lens_put = \<lambda> (u, v) (x, y). (put\<^bsub>X\<^esub> u x, put\<^bsub>Y\<^esub> v y) \<rparr>"

lemma prod_mwb_lens:
  assumes 1:"mwb_lens X" and 2:"mwb_lens Y" 
  shows "mwb_lens (X \<times>\<^sub>L Y)"
  using 1 2
  by (unfold_locales, simp_all add: prod_lens_def prod.case_eq_if)

lemma prod_wb_lens:
  assumes 1:"wb_lens X" and 2:"wb_lens Y" 
  shows "wb_lens (X \<times>\<^sub>L Y)"
  using 1 2
  by (unfold_locales, simp_all add: prod_lens_def prod.case_eq_if)

lemma prod_vwb_lens:
  assumes 1:"vwb_lens X" and 2:"vwb_lens Y"
  shows "vwb_lens (X \<times>\<^sub>L Y)"
  using 1 2
  by (unfold_locales, simp_all add: prod_lens_def prod.case_eq_if)

lemma prod_bij_lens:
  assumes 1:"bij_lens X" and 2:"bij_lens Y" 
  shows"bij_lens (X \<times>\<^sub>L Y)"
  using 1 2
  by (unfold_locales, simp_all add: prod_lens_def prod.case_eq_if)

lemma prod_as_plus: "X \<times>\<^sub>L Y = X ;\<^sub>L fst\<^sub>L +\<^sub>L Y ;\<^sub>L snd\<^sub>L"
  unfolding prod_lens_def fst_lens_def snd_lens_def lens_comp_def lens_plus_def
  by auto

lemma prod_lens_sublens_cong:
  assumes 1:"X\<^sub>1 \<subseteq>\<^sub>L X\<^sub>2" and 2: "Y\<^sub>1 \<subseteq>\<^sub>L Y\<^sub>2" 
  shows "(X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) \<subseteq>\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2)"
  using 1 2
  apply (auto simp add: sublens_def)
  apply (rename_tac Z\<^sub>1 Z\<^sub>2)
  apply (rule_tac x="Z\<^sub>1 \<times>\<^sub>L Z\<^sub>2" in exI)
  apply (auto)
  using prod_vwb_lens apply blast
  apply (auto simp add: prod_lens_def lens_comp_def prod.case_eq_if)
  apply (rule ext, rule ext)
  apply (auto simp add: prod_lens_def lens_comp_def prod.case_eq_if)
done

lemma prod_lens_equiv_cong:
  assumes 1:"X\<^sub>1 \<approx>\<^sub>L X\<^sub>2" and 2:"Y\<^sub>1 \<approx>\<^sub>L Y\<^sub>2" 
  shows"(X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) \<approx>\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2)"
  using 1 2
  by (simp add: lens_equiv_def prod_lens_sublens_cong)

lemma prod_lens_id_equiv:
  "1\<^sub>L \<times>\<^sub>L 1\<^sub>L = 1\<^sub>L"
  by (auto simp add: prod_lens_def id_lens_def)

lemma lens_indep_prod:
  assumes 1:"X\<^sub>1 \<bowtie> X\<^sub>2" and 2:" Y\<^sub>1 \<bowtie> Y\<^sub>2" 
  shows" X\<^sub>1 \<times>\<^sub>L Y\<^sub>1 \<bowtie> X\<^sub>2 \<times>\<^sub>L Y\<^sub>2"
proof -
  obtain pp :: "('c \<times> 'f \<Longrightarrow> 'b \<times> 'e) \<Rightarrow> ('a \<times> 'd \<Longrightarrow> 'b \<times> 'e) \<Rightarrow> 'b \<times> 'e"
     and ppa :: "('c \<times> 'f \<Longrightarrow> 'b \<times> 'e) \<Rightarrow> ('a \<times> 'd \<Longrightarrow> 'b \<times> 'e) \<Rightarrow> 'a \<times> 'd" where
    "\<forall>x0 x1. (\<exists>v2 v3. get\<^bsub>x0\<^esub> (put\<^bsub>x1\<^esub> v3 v2) \<noteq> get\<^bsub>x0\<^esub> v3) = (get\<^bsub>x0\<^esub> (put\<^bsub>x1\<^esub> (pp x0 x1) (ppa x0 x1)) \<noteq> get\<^bsub>x0\<^esub> (pp x0 x1))"
    by moura
  then obtain ppb :: "('c \<times> 'f \<Longrightarrow> 'b \<times> 'e) \<Rightarrow> ('a \<times> 'd \<Longrightarrow> 'b \<times> 'e) \<Rightarrow> 'b \<times> 'e" and 
              ppc :: "('c \<times> 'f \<Longrightarrow> 'b \<times> 'e) \<Rightarrow> ('a \<times> 'd \<Longrightarrow> 'b \<times> 'e) \<Rightarrow> 'c \<times> 'f" and
              ppd :: "('c \<times> 'f \<Longrightarrow> 'b \<times> 'e) \<Rightarrow> ('a \<times> 'd \<Longrightarrow> 'b \<times> 'e) \<Rightarrow> 'b \<times> 'e" and 
              ppe :: "('c \<times> 'f \<Longrightarrow> 'b \<times> 'e) \<Rightarrow> ('a \<times> 'd \<Longrightarrow> 'b \<times> 'e) \<Rightarrow> 'c \<times> 'f" and 
              ppf :: "('c \<times> 'f \<Longrightarrow> 'b \<times> 'e) \<Rightarrow> ('a \<times> 'd \<Longrightarrow> 'b \<times> 'e) \<Rightarrow> 'a \<times> 'd" where
    f1: "\<forall>l la. ((\<exists>p pa pb. put\<^bsub>la\<^esub> (put\<^bsub>l\<^esub> pb pa) p \<noteq> put\<^bsub>l\<^esub> (put\<^bsub>la\<^esub> pb p) pa) \<or> 
                 (\<exists>p pa. get\<^bsub>la\<^esub> (put\<^bsub>l\<^esub> pa p) \<noteq> get\<^bsub>la\<^esub> pa) \<or>
                 (\<exists>p pa. get\<^bsub>l\<^esub> (put\<^bsub>la\<^esub> pa p) \<noteq> get\<^bsub>l\<^esub> pa)) = 
                 (put\<^bsub>la\<^esub> (put\<^bsub>l\<^esub> (ppd l la) (ppe l la)) (ppf l la) \<noteq> 
                  put\<^bsub>l\<^esub> (put\<^bsub>la\<^esub> (ppd l la) (ppf l la)) (ppe l la) \<or> 
                  get\<^bsub>la\<^esub> (put\<^bsub>l\<^esub> (ppb l la) (ppc l la)) \<noteq> get\<^bsub>la\<^esub> (ppb l la) \<or> 
                  get\<^bsub>l\<^esub> (put\<^bsub>la\<^esub> (pp l la) (ppa l la)) \<noteq> get\<^bsub>l\<^esub> (pp l la))"
    by moura
  have f2: "put\<^bsub>X\<^sub>1 \<times>\<^sub>L Y\<^sub>1\<^esub> = (\<lambda>(b, e) (a, d). (put\<^bsub>X\<^sub>1\<^esub> b a, put\<^bsub>Y\<^sub>1\<^esub> e d))"
    by (simp add: prod_lens_def)
  have "\<forall>l la. \<not> (l::'a \<Longrightarrow> 'b) \<bowtie> (la::'c \<Longrightarrow> _) \<or> la \<bowtie> l"
    using lens_indep_sym by blast
  then have f3: "X\<^sub>2 \<bowtie> X\<^sub>1"
    by (metis "1")
  have "\<forall>l la. \<not> (l::'d \<Longrightarrow> 'e) \<bowtie> (la::'f \<Longrightarrow> _) \<or> la \<bowtie> l"
    using lens_indep_sym by blast
  then have "Y\<^sub>2 \<bowtie> Y\<^sub>1"
    by (metis "2")
  then have "get\<^bsub>Y\<^sub>2\<^esub> (put\<^bsub>Y\<^sub>1\<^esub> (snd (pp (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) (snd (ppa (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))) = 
             get\<^bsub>Y\<^sub>2\<^esub> (snd (pp (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))"
    by (meson lens_indep_get)
  then have "get\<^bsub>X\<^sub>2 \<times>\<^sub>L Y\<^sub>2\<^esub> (put\<^bsub>X\<^sub>1 \<times>\<^sub>L Y\<^sub>1\<^esub> (pp (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)) (ppa (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) = 
             (get\<^bsub>X\<^sub>2\<^esub> (fst (pp (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))), get\<^bsub>Y\<^sub>2\<^esub> (snd (pp (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))))"
    using f3 by (simp add: prod_lens_def split_beta)
  then have f4: "get\<^bsub>X\<^sub>2 \<times>\<^sub>L Y\<^sub>2\<^esub> (put\<^bsub>X\<^sub>1 \<times>\<^sub>L Y\<^sub>1\<^esub> (pp (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)) (ppa (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) = 
                 get\<^bsub>X\<^sub>2 \<times>\<^sub>L Y\<^sub>2\<^esub> (pp (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))"
    by (metis (no_types) map_prod_simp prod.collapse prod_lens_def select_convs(1))
  have "\<forall>l la b c a. \<not> l \<bowtie> la \<or> put\<^bsub>l\<^esub> (put\<^bsub>la\<^esub> (b::'b) (c::'c)) (a::'a) = put\<^bsub>la\<^esub> (put\<^bsub>l\<^esub> b a) c"
    using lens_indep_comm by fastforce
  then have "put\<^bsub>X\<^sub>1\<^esub> (put\<^bsub>X\<^sub>2\<^esub> (fst (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) 
                             (fst (ppe (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))) 
                             (fst (ppf (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) = 
                             put\<^bsub>X\<^sub>2\<^esub> (put\<^bsub>X\<^sub>1\<^esub> (fst (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) 
                                             (fst (ppf (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))) 
                                     (fst (ppe (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))"
    by (metis "1") 
  then have f5: "put\<^bsub>X\<^sub>2\<^esub> (fst (put\<^bsub>X\<^sub>1 \<times>\<^sub>L Y\<^sub>1\<^esub> (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)) 
                         (ppf (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))) (fst (ppe (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) = 
                 put\<^bsub>X\<^sub>1\<^esub> (put\<^bsub>X\<^sub>2\<^esub> (fst (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) 
                         (fst (ppe (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))) (fst (ppf (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))"
    using f2 by (simp add: split_beta)
  have f6: "put\<^bsub>X\<^sub>2 \<times>\<^sub>L Y\<^sub>2\<^esub> = (\<lambda>(b, e) (c, f). (put\<^bsub>X\<^sub>2\<^esub> b c, put\<^bsub>Y\<^sub>2\<^esub> e f))"
    by (simp add: prod_lens_def)
  then have f7: "put\<^bsub>X\<^sub>2\<^esub> (fst (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) (fst (ppe (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) = 
                 fst (put\<^bsub>X\<^sub>2 \<times>\<^sub>L Y\<^sub>2\<^esub> (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)) (ppe (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) \<and> 
                      put\<^bsub>Y\<^sub>2\<^esub> (snd (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) (snd (ppe (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) = 
                 snd (put\<^bsub>X\<^sub>2 \<times>\<^sub>L Y\<^sub>2\<^esub> (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)) (ppe (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))"
    by (simp add: split_beta)
  have "\<forall>l la e f d. \<not> l \<bowtie> la \<or> put\<^bsub>l\<^esub> (put\<^bsub>la\<^esub> (e::'e) (f::'f)) (d::'d) =
         put\<^bsub>la\<^esub> (put\<^bsub>l\<^esub> e d) f"
    using lens_indep_comm by fastforce
  then have "put\<^bsub>Y\<^sub>1\<^esub> (put\<^bsub>Y\<^sub>2\<^esub> (snd (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) 
                     (snd (ppe (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))) (snd (ppf (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) = 
             put\<^bsub>Y\<^sub>2\<^esub> (put\<^bsub>Y\<^sub>1\<^esub> (snd (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) (snd (ppf (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))) 
                     (snd (ppe (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))"
    by (metis "2")
  then have f8: "put\<^bsub>Y\<^sub>2\<^esub> (snd (put\<^bsub>X\<^sub>1 \<times>\<^sub>L Y\<^sub>1\<^esub> (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)) (ppf (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))) 
                         (snd (ppe (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) = 
                 put\<^bsub>Y\<^sub>1\<^esub> (put\<^bsub>Y\<^sub>2\<^esub> (snd (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) 
                         (snd (ppe (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))) (snd (ppf (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))"
    using f2 by (simp add: split_beta)
  have "put\<^bsub>X\<^sub>2 \<times>\<^sub>L Y\<^sub>2\<^esub> (put\<^bsub>X\<^sub>1 \<times>\<^sub>L Y\<^sub>1\<^esub> (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)) (ppf (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) = 
        (\<lambda>(c, f). (put\<^bsub>X\<^sub>2\<^esub> (fst (put\<^bsub>X\<^sub>1 \<times>\<^sub>L Y\<^sub>1\<^esub> (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)) 
        (ppf (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))) c, put\<^bsub>Y\<^sub>2\<^esub> (snd (put\<^bsub>X\<^sub>1 \<times>\<^sub>L Y\<^sub>1\<^esub> (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)) 
        (ppf (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))) f))"
    using f6 by (simp add: split_beta)
  then have f9: "put\<^bsub>X\<^sub>1 \<times>\<^sub>L Y\<^sub>1\<^esub> (put\<^bsub>X\<^sub>2 \<times>\<^sub>L Y\<^sub>2\<^esub> (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)) (ppe (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) 
                 (ppf (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)) = 
                  put\<^bsub>X\<^sub>2 \<times>\<^sub>L Y\<^sub>2\<^esub> (put\<^bsub>X\<^sub>1 \<times>\<^sub>L Y\<^sub>1\<^esub> (ppd (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)) (ppf (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) 
                 (ppe (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))"
    using f8 f7 f5 f2 by (simp add: split_beta)
  have "\<forall>l la b c. \<not> l \<bowtie> la \<or> get\<^bsub>l\<^esub> (put\<^bsub>la\<^esub> (b::'b) (c::'c)) = (get\<^bsub>l\<^esub> b::'a)"
    by (meson lens_indep_get)
  then have f10: "get\<^bsub>X\<^sub>1\<^esub> (put\<^bsub>X\<^sub>2\<^esub> (fst (ppb (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) 
                  (fst (ppc (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))) = get\<^bsub>X\<^sub>1\<^esub> (fst (ppb (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))"
    by (metis "1")
  have "\<forall>l la e f. \<not> l \<bowtie> la \<or> get\<^bsub>l\<^esub> (put\<^bsub>la\<^esub> (e::'e) (f::'f)) = (get\<^bsub>l\<^esub> e::'d)"
    by (meson lens_indep_get)
  then have "get\<^bsub>Y\<^sub>1\<^esub> (put\<^bsub>Y\<^sub>2\<^esub> (snd (ppb (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) (snd (ppc (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))) = 
             get\<^bsub>Y\<^sub>1\<^esub> (snd (ppb (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)))"
    by (metis "2")
  then have "get\<^bsub>X\<^sub>1 \<times>\<^sub>L Y\<^sub>1\<^esub> (put\<^bsub>X\<^sub>2 \<times>\<^sub>L Y\<^sub>2\<^esub> (ppb (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)) (ppc (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) = 
            (get\<^bsub>X\<^sub>1\<^esub> (fst (ppb (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))), get\<^bsub>Y\<^sub>1\<^esub> (snd (ppb (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))))"
    using f10 by (simp add: prod_lens_def split_beta)
  then have "get\<^bsub>X\<^sub>1 \<times>\<^sub>L Y\<^sub>1\<^esub> (put\<^bsub>X\<^sub>2 \<times>\<^sub>L Y\<^sub>2\<^esub> (ppb (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1)) (ppc (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))) = 
             get\<^bsub>X\<^sub>1 \<times>\<^sub>L Y\<^sub>1\<^esub> (ppb (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1))"
    by (metis (no_types) map_prod_simp prod.collapse prod_lens_def select_convs(1))
  then show ?thesis
    using f9 f4 f1 by (meson lens_indepI)
qed


lemma lens_plus_prod_exchange:
  "(X\<^sub>1 +\<^sub>L X\<^sub>2) \<times>\<^sub>L (Y\<^sub>1 +\<^sub>L Y\<^sub>2) \<approx>\<^sub>L (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) +\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2)"
proof (rule lens_equivI)
  show "(X\<^sub>1 +\<^sub>L X\<^sub>2) \<times>\<^sub>L (Y\<^sub>1 +\<^sub>L Y\<^sub>2) \<subseteq>\<^sub>L (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) +\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2)"
    apply (simp add: sublens_def)
    apply (rule_tac x="((fst\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L (fst\<^sub>L ;\<^sub>L snd\<^sub>L)) +\<^sub>L ((snd\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L (snd\<^sub>L ;\<^sub>L snd\<^sub>L))" in exI)
    apply (auto)
    apply (auto intro!: plus_vwb_lens comp_vwb_lens fst_vwb_lens snd_vwb_lens lens_indep_right_comp)
    apply (auto intro!: lens_indepI simp add: lens_comp_def lens_plus_def fst_lens_def snd_lens_def)
    apply (auto simp add: prod_lens_def lens_plus_def lens_comp_def fst_lens_def snd_lens_def prod.case_eq_if comp_def)[1]
    apply (rule ext, rule ext, auto simp add: prod.case_eq_if)
  done  
  show "(X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) +\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) \<subseteq>\<^sub>L (X\<^sub>1 +\<^sub>L X\<^sub>2) \<times>\<^sub>L (Y\<^sub>1 +\<^sub>L Y\<^sub>2)"
    apply (simp add: sublens_def)
    apply (rule_tac x="((fst\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L (fst\<^sub>L ;\<^sub>L snd\<^sub>L)) +\<^sub>L ((snd\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L (snd\<^sub>L ;\<^sub>L snd\<^sub>L))" in exI)
    apply (auto)
    apply (auto intro!: plus_vwb_lens comp_vwb_lens fst_vwb_lens snd_vwb_lens lens_indep_right_comp)
    apply (auto intro!: lens_indepI simp add: lens_comp_def lens_plus_def fst_lens_def snd_lens_def)
    apply (auto simp add: prod_lens_def lens_plus_def lens_comp_def fst_lens_def snd_lens_def prod.case_eq_if comp_def)[1]
    apply (rule ext, rule ext, auto simp add: prod_lens_def prod.case_eq_if)
  done
qed

text {* We require that range type of a lens function has cardinality of at least 2; this ensures
        that properties of independence are provable. *}

definition fun_lens :: "'a \<Rightarrow> ('b \<Longrightarrow> ('a \<Rightarrow> 'b))" where
[lens_defs]: "fun_lens x = \<lparr> lens_get = (\<lambda> f. f x), lens_put = (\<lambda> f u. f(x := u)) \<rparr>"

lemma fun_weak_lens: "weak_lens (fun_lens k)" (*legacy:I add this for match purpose*)
  by (unfold_locales, simp_all add: fun_lens_def)

lemma fun_wb_lens: "wb_lens (fun_lens x)" (*legacy:I add this for match purpose*)
  by (unfold_locales, simp_all add: fun_lens_def)

lemma fun_mwb_lens: "mwb_lens (fun_lens k)" (*legacy:I add this for match purpose*)
  by (unfold_locales, simp_all add: fun_lens_def)

lemma fun_vwb_lens: "vwb_lens (fun_lens k)"
  by (unfold_locales, simp_all add: fun_lens_def)

lemma fun_lens_indep:
  "x \<noteq> y \<longrightarrow> fun_lens x \<bowtie> fun_lens y  "
  unfolding  fun_lens_def
  by (simp add: fun_upd_twist lens_indep_def)

text {* The function range lens allows us to focus on a particular region on a functions range *}

definition fun_ran_lens :: "('c \<Longrightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> 'b) \<Longrightarrow> '\<alpha>) \<Rightarrow> (('a \<Rightarrow> 'c) \<Longrightarrow> '\<alpha>)" where
[lens_defs]: "fun_ran_lens X Y = \<lparr> lens_get = \<lambda> s. get\<^bsub>X\<^esub> \<circ> get\<^bsub>Y\<^esub> s
                                 , lens_put = \<lambda> s v. put\<^bsub>Y\<^esub> s (\<lambda> x::'a. put\<^bsub>X\<^esub> (get\<^bsub>Y\<^esub> s x) (v x)) \<rparr>"

lemma fun_ran_mwb_lens: 
  assumes 1:"mwb_lens X" and 2:"mwb_lens Y" 
  shows "mwb_lens (fun_ran_lens X Y)"
  using 1 2
  by (unfold_locales, auto simp add: fun_ran_lens_def)

lemma fun_ran_wb_lens: 
  assumes 1:"wb_lens X" and 2:"wb_lens Y" 
  shows "wb_lens (fun_ran_lens X Y)"
  using 1 2
  by (unfold_locales, auto simp add: fun_ran_lens_def)

lemma fun_ran_vwb_lens: 
  assumes 1:"vwb_lens X" and 2:"vwb_lens Y" 
  shows  "vwb_lens (fun_ran_lens X Y)"
  using 1 2
  by (unfold_locales, auto simp add: fun_ran_lens_def)

definition map_lens :: "'a \<Rightarrow> ('b \<Longrightarrow> ('a \<rightharpoonup> 'b))" where
[lens_defs]: "map_lens x = \<lparr> lens_get = (\<lambda> f. the (f x)), lens_put = (\<lambda> f u. f(x \<mapsto> u)) \<rparr>"

lemma map_mwb_lens: "mwb_lens (map_lens x)"
  by (unfold_locales, simp_all add: map_lens_def)

definition list_pad_out :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
"list_pad_out xs k = xs @ replicate (k + 1 - length xs) undefined"

definition list_augment :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
"list_augment xs k v = (list_pad_out xs k)[k := v]"

definition nth' :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" where
"nth' xs i = (if (length xs > i) then xs ! i else undefined)"

lemma list_update_append_lemma1: 
  assumes 1:"i < length xs" 
  shows"xs[i := v] @ ys = (xs @ ys)[i := v]"
  using 1
  by (simp add: list_update_append)

lemma list_update_append_lemma2: (* this lemma do not need the assumes 1:"i < length ys"*) 
  "xs @ ys[i := v] = (xs @ ys)[i + length xs := v]"
  by (simp add: list_update_append)

lemma nth'_0 [simp]: 
  "nth' (x # xs) 0 = x"
  by (simp add: nth'_def)

lemma nth'_Suc [simp]: 
  "nth' (x # xs) (Suc n) = nth' xs n"
  by (simp add: nth'_def)

lemma list_augment_0 [simp]:
  "list_augment (x # xs) 0 y = y # xs"
  by (simp add: list_augment_def list_pad_out_def)

lemma list_augment_Suc [simp]:
  "list_augment (x # xs) (Suc n) y = x # list_augment xs n y"
  by (simp add: list_augment_def list_pad_out_def)

lemma list_augment_twice:
  "list_augment (list_augment xs i u) j v = list_pad_out xs (max i j)[i := u, j := v]"
  apply (auto simp add: list_augment_def list_pad_out_def list_update_append_lemma1 replicate_add[THEN sym] max_def)
  apply (metis Suc_le_mono add.commute diff_diff_add diff_le_mono le_add_diff_inverse2)
done

lemma list_augment_commute:
  assumes 1:"i \<noteq> j" 
  shows "list_augment (list_augment \<sigma> j v) i u = list_augment (list_augment \<sigma> i u) j v"
  using 1
  by (simp add: list_augment_twice list_update_swap max.commute)

lemma nth_list_augment: 
  "list_augment xs k v ! k = v"
  by (simp add: list_augment_def list_pad_out_def)

lemma nth'_list_augment: 
  "nth' (list_augment xs k v) k = v"
  by (auto simp add: nth'_def nth_list_augment list_augment_def list_pad_out_def)

lemma list_augment_same_twice: 
  "list_augment (list_augment xs k u) k v = list_augment xs k v"
  by (simp add: list_augment_def list_pad_out_def)

lemma nth'_list_augment_diff: 
  assumes 1:"i \<noteq> j" 
  shows"nth' (list_augment \<sigma> i v) j = nth' \<sigma> j"
  using 1
  by (auto simp add: list_augment_def list_pad_out_def nth_append nth'_def)

definition list_lens :: "nat \<Rightarrow> ('a \<Longrightarrow> 'a list)" where
[lens_defs]: "list_lens i = \<lparr> lens_get = (\<lambda> xs. nth' xs i)
                            , lens_put = (\<lambda> xs x. list_augment xs i x) \<rparr>"

abbreviation "hd_lens \<equiv> list_lens 0"

definition tl_lens :: "'a list \<Longrightarrow> 'a list" where
[lens_defs]: "tl_lens = \<lparr> lens_get = (\<lambda> xs. tl xs)
                        , lens_put = (\<lambda> xs xs'. hd xs # xs') \<rparr>"

lemma list_mwb_lens: 
  "mwb_lens (list_lens x)"
  by (unfold_locales, simp_all add: list_lens_def 
      nth'_list_augment list_augment_same_twice)

lemma tail_lens_mwb: 
  "mwb_lens tl_lens"
  by (unfold_locales, simp_all add: tl_lens_def)

lemma list_lens_indep:
  assumes 1:"i \<noteq> j" 
  shows "list_lens i \<bowtie> list_lens j"
  using 1
  by (simp add: list_lens_def lens_indep_def list_augment_commute nth'_list_augment_diff)

lemma hd_tl_lens_indep [simp]:
  "hd_lens \<bowtie> tl_lens"
  apply (rule lens_indepI)
  apply (simp_all add: list_lens_def tl_lens_def)
  apply (metis hd_conv_nth hd_def length_greater_0_conv list.case(1) nth'_def nth'_list_augment)
  apply (metis (full_types) hd_conv_nth hd_def length_greater_0_conv list.case(1) nth'_def)
  apply (metis Nitpick.size_list_simp(2) One_nat_def add_Suc_right append.simps(1) 
               append_Nil2 diff_Suc_Suc diff_zero hd_Cons_tl list.inject list.size(4) 
               list_augment_0 list_augment_def list_augment_same_twice list_pad_out_def 
               nth_list_augment replicate.simps(1) replicate.simps(2) tl_Nil)
done

subsection {* Record field lenses *}

abbreviation (input) "fld_put f \<equiv> (\<lambda> \<sigma> u. f (\<lambda>_. u) \<sigma>)"

syntax "_FLDLENS" :: "id \<Rightarrow> ('a \<Longrightarrow> 'r)"  ("FLDLENS _")
translations "FLDLENS x" => "\<lparr> lens_get = x, lens_put = CONST fld_put (_update_name x) \<rparr>"

subsection {* Memory lenses *}

text {*In the sequel we prove that the operations @{text lookup} and
       @{text update} forms together a mainly well behaved lens since
       together they preserve the following lens laws:
       \begin{itemize}
          \item Put Get
          \item Put Put
       \end{itemize}*}

(*definition memory_lens :: "'\<alpha> \<Rightarrow> ('\<beta> \<Longrightarrow> ('\<alpha>, '\<beta>) memory)" where
[lens_defs]: "memory_lens x = \<lparr> lens_get = (\<lambda>\<sigma>. \<sigma> $ x), lens_put = (\<lambda>\<sigma> v. (\<sigma>(x :=\<^sub>$ v))) \<rparr>"

lemma memory_mwb_len:"mwb_lens (memory_lens x)"
  unfolding memory_lens_def
  by (unfold_locales, simp_all add: update_cancel update_share sharing_refl)
 
interpretation memory_len_laws: mwb_lens "memory_lens x"
 using memory_mwb_len
 by fast*)

(*A specification of updates*)

term"put\<^bsub>X\<^esub> \<sigma> ( get\<^bsub>X\<^esub> \<sigma> + 1)"

(*A specification about things that do not change using lenses.
  Such a specification is crucial when reasoning about global variables*)

term"\<forall> X Y. \<not>(X \<approx>\<^sub>L Y) \<longrightarrow> get\<^bsub>X\<^esub> \<sigma> = get\<^bsub>X\<^esub> \<sigma>'"

(*Another advantage of Lenses is also the theory contains the operator  \<bowtie>, expressing
  Lens independence. Such operator help to check dependencies on global variables in a 
  given state space*)


term"\<forall> X Y. \<not> (X \<bowtie> Y) \<longrightarrow> put\<^bsub>X\<^esub> \<sigma> val = put\<^bsub>Y\<^esub> \<sigma> val"


end