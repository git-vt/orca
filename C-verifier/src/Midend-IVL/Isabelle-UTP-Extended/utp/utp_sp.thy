theory utp_sp
imports "../hoare/HoareLogic/PartialCorrectness/utp_hoare"
    
begin

named_theorems sp

method sp_tac = (simp add: sp)

consts
  usp :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infix "sp" 60)
  
definition sp_upred :: "'\<alpha> cond \<Rightarrow> ('\<alpha>, '\<beta>) rel \<Rightarrow> '\<beta> cond" where
"sp_upred p Q = \<lfloor>(\<lceil>p\<rceil>\<^sub>> ;; Q) :: ('\<alpha>, '\<beta>) rel\<rfloor>\<^sub>>"

adhoc_overloading
  usp sp_upred
  
declare sp_upred_def [upred_defs]

lemma sp_false [sp]: "p sp false = false"
  by (rel_simp) 

lemma sp_true [sp]: "q \<noteq> false \<Longrightarrow> q sp true = true"
  by (rel_auto) 
    
lemma sp_assigns_r [sp]: 
  "vwb_lens x \<Longrightarrow> (p sp x :== e ) = (\<^bold>\<exists>v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> &x =\<^sub>u e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>)"
  apply (rel_simp) 
    apply transfer
  apply auto
   apply (rule_tac x = \<open>get\<^bsub>x\<^esub> y\<close> in exI)
    apply simp
  apply (metis vwb_lens.put_eq)
done

theorem sp_hoare_link:
  "\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u \<longleftrightarrow> (r \<sqsubseteq> p sp Q)"
  by rel_auto   

lemma "\<lbrace>p\<rbrace>C\<lbrace>p sp C\<rbrace>\<^sub>u"
  by rel_blast


theorem sp_eq_intro: "\<lbrakk>\<And>r. r sp P = r sp Q\<rbrakk> \<Longrightarrow> P = Q"
  by (rel_auto robust, fastforce+)    

end  
  