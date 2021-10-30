section \<open>Domain 0 - Zermelo Fraenkel set theory in HOL\<close>

theory ZF_HOL 
  imports "$ISABELLE_HOME/src/HOL/ZFC_in_HOL/ZFC_Typeclasses" 
          Model_locale begin

(*membership relation, defined as HOL set membership and the 'elements' coercion from V to V set *)
abbreviation mem where "mem a x \<equiv> a \<in> elts x"

(*empty set is a coerced version of the HOL empty set*)
thm zero_V_def

(*argument of union needs lifting, then result needs flattening *)
abbreviation union where "union x \<equiv> ZFC_in_HOL.set (Union (elts ` (elts x)))"

(*subset relation gained by showing that V is a distributive lattice*)
abbreviation subset where "subset x y \<equiv> x \<le> y"

(*V \<Rightarrow> V power set already defined in ZFC_in_HOL*)
thm VPow_def

thm succ_def

abbreviation repl where "repl P x \<equiv> ZFC_in_HOL.set ((\<lambda>a. (THE b. P a b)) ` {a . a \<in> elts x \<and> (\<exists>b. P a b)})"

interpretation GZF_HOL : GZF mem 0 "(\<lambda>x. True)" union subset VPow succ \<omega> repl
proof (unfold_locales, auto, rule exI)
  fix P :: "V \<Rightarrow> V \<Rightarrow> bool" and x a b assume "\<forall>a. mem a x \<longrightarrow> Uniq (P a)" "mem a x" "P a b" 
  moreover hence "The (P a) = b" unfolding Uniq_def by auto
  ultimately show "mem a x \<and> P a (The (P a))" "b \<in> (\<lambda>a. The (P a)) ` {a. mem a x \<and> Ex (P a)}" by auto
qed

thm GZF_HOL.un_iff
find_consts "V"


abbreviation ord where "ord x \<equiv> ZFC_in_HOL.Ord x"
abbreviation lt where "lt x y \<equiv> x < y \<and> ord x \<and> ord y" 

lemma succD : "ord (succ i) \<Longrightarrow> ord i"
  by (erule Ord_in_Ord, auto)


lemma lt_ord : "lt i j \<Longrightarrow> ord i \<and> ord j" by auto
lemma lt_mem : "lt i j \<Longrightarrow> mem i j" using lt_ord Ord_mem_iff_lt by auto
lemma mem_lt : assumes "ord j" shows "mem i j \<Longrightarrow> lt i j" using OrdmemD assms Ord_in_Ord by auto

(*Can't be proved automatically - might have to copy some of the development from Isabelle/ZF?*)
lemma succ_mem_iff : "i \<in> elts (succ j) \<longleftrightarrow> i \<in> elts j | i = j" 
  unfolding elts_succ by auto

lemma succ_iff : "lt i (succ j) \<longleftrightarrow> lt i j | i = j \<and> ord j"
proof
  assume "lt i (succ j)" hence mem:"mem i (succ j)" by (rule lt_mem)
  have "ord i" "ord (succ j)" using lt_ord[OF \<open>lt i (succ j)\<close>] by auto
  hence "ord j" using succD by auto
  
  from mem have "mem i j | i = j" using succ_mem_iff by auto
  thus "lt i j | i = j \<and> ord j" using Ord_mem_iff_lt \<open>ord i\<close> \<open>ord j\<close> by auto
next
  assume "lt i j | i = j \<and> ord j"
  thus "lt i (succ j)"
  proof
    assume "lt i j" hence "ord i" "ord j" by auto
    from \<open>lt i j\<close> have "mem i j" using Ord_mem_iff_lt by auto
    hence "mem i (succ j)" using succ_mem_iff by auto
    hence "i < succ j" using Ord_mem_iff_lt[OF \<open>ord i\<close> Ord_succ[OF \<open>ord j\<close>]] by auto
    thus "lt i (succ j)" using \<open>ord i\<close> \<open>ord j\<close>  by auto
  next
    assume h:"i = j \<and> ord j" 
    hence "ord i" "ord (succ j)" using Ord_succ by auto

    from h have "mem i (succ j)" using succ_mem_iff by auto
    thus "lt i (succ j)" using Ord_mem_iff_lt[OF \<open>ord i\<close> \<open>ord (succ j)\<close>] \<open>ord i\<close> \<open>ord (succ j)\<close> by auto
  qed
qed

lemma limit_iff : "\<forall>\<mu>. Limit \<mu> \<longleftrightarrow> (ord \<mu> \<and> lt 0 \<mu> \<and> (\<forall>\<beta>. lt \<beta> \<mu> \<longrightarrow> lt (succ \<beta>) \<mu>))" 
  proof (rule, rule)
    fix \<mu> assume "Limit \<mu>" hence def:"ord \<mu> \<and> mem 0 \<mu> \<and> (\<forall>y. mem y \<mu> \<longrightarrow> mem (ZFC_in_HOL.succ y) \<mu>)"
      unfolding Limit_def by simp
    hence 1: "ord \<mu>" and 2: "lt 0 \<mu>" using Ord_mem_iff_lt by auto
    have 3: "(\<forall>\<beta>. lt \<beta> \<mu> \<longrightarrow> lt (succ \<beta>) \<mu>)" 
    proof (rule, rule)
      fix \<beta> assume "lt \<beta> \<mu>" hence "ord \<beta>" "mem \<beta> \<mu>" using Ord_mem_iff_lt by auto
      hence "mem (succ \<beta>) \<mu>" using def by auto
      thus "lt (succ \<beta>) \<mu>" using Ord_mem_iff_lt Ord_succ[OF \<open>ord \<beta>\<close>] \<open>ord \<mu>\<close> by auto
    qed
    from 1 2 3 show "ord \<mu> \<and> lt 0 \<mu> \<and> (\<forall>\<beta>. lt \<beta> \<mu> \<longrightarrow> lt (succ \<beta>) \<mu>)" by auto
  next
    fix \<mu> assume h:"ord \<mu> \<and> lt 0 \<mu> \<and> (\<forall>\<beta>. lt \<beta> \<mu> \<longrightarrow> lt (ZFC_in_HOL.succ \<beta>) \<mu>)"
    thus "Limit \<mu>" unfolding Limit_def using lt_mem proof (auto)
      fix y assume "mem y \<mu>" moreover hence "ord y" "ord \<mu>"using Ord_in_Ord h by auto
      ultimately have "lt y \<mu>" using Ord_mem_iff_lt by auto
      hence "lt (succ y) \<mu>" using h by auto
      thus "mem (succ y) \<mu>" using lt_mem by auto
    qed
  qed

lemma lt_trans : "lt i j \<Longrightarrow> lt j k \<Longrightarrow> lt i k" by auto
lemma lt_notsym : "lt i j \<Longrightarrow> \<not> lt j i" by auto
lemma lt_linear : "ord i \<and> ord j \<Longrightarrow> lt i j | i = j | lt j i" using Ord_linear_lt by auto
lemma lt_induct : "ord a \<Longrightarrow> (\<And>x. ord x \<Longrightarrow> (\<And>y. lt y x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"
proof -
  assume "ord a" "(\<And>x. ord x \<Longrightarrow> (\<And>y. lt y x \<Longrightarrow> P y) \<Longrightarrow> P x)"
  hence "(\<And>x. ord x \<Longrightarrow> (\<And>y. mem y x \<Longrightarrow> P y) \<Longrightarrow> P x)" using lt_mem by auto
  thus ?thesis by (rule Ord_induct[OF \<open>ord a\<close>])
qed
thm lt_mem
lemma predset_def : "ord j \<Longrightarrow> mem i j \<longleftrightarrow> lt i j"
  by (rule, rule mem_lt, use lt_mem in auto)


(*Try using GZF_HOL.Lambda rather than VLambda*)
abbreviation tr3 where "tr3 G F A \<beta> \<equiv> transrec3 A (\<lambda>i. F (succ i)) (\<lambda>\<alpha> f. G \<alpha> (VLambda \<alpha> f)) \<beta>"
lemma rec0 : "tr3 G F A 0 = A" 
 by (rule transrec3_0)

lemma recsucc: "tr3 G F A (succ \<beta>) = F (succ \<beta>) (tr3 G F A \<beta>)"
  by (rule transrec3_succ)
thm GZF_HOL.upair_iff
thm GZF_HOL.sng_iff

lemma "vpair a b = GZF_HOL.kpair a b" proof
  fix x show "mem x \<langle>a, b\<rangle> = mem x (GZF_HOL.kpair a b) " 
  unfolding GZF_HOL.kpair_def using GZF_HOL.upair_iff vpair_def by auto
qed

lemma "VLambda x F = GZF_HOL.Lambda x F"
lemma reclim : "Limit \<mu> \<Longrightarrow> tr3 G F A \<mu> = G \<mu> (GZF_HOL.Lambda \<mu> (\<lambda>b. tr3 G F A b))"
  sorry

interpretation Ord_HOL : Ord mem 0 "(\<lambda>x. True)" union subset VPow succ \<omega> repl
                             ord lt 0 succ Limit "(\<lambda>x. x)" tr3 \<omega>
proof (unfold_locales)
  show "ord 0" by auto
  show "ord \<omega>" by auto
  show "\<forall>i j. lt i j \<longrightarrow> ord i \<and> ord j" using lt_ord by auto
  show "\<forall>i. ord (succ i) \<longleftrightarrow> ord i" using Ord_in_Ord by auto
  show "\<forall>i. \<not> lt i 0" by auto
  show "(\<forall>\<alpha> \<beta>. lt \<alpha> (succ \<beta>) \<longleftrightarrow> (lt \<alpha> \<beta> | \<alpha> = \<beta>  \<and> ord \<beta>))" using succ_iff by simp
  show "\<forall>\<mu>. Limit \<mu> \<longleftrightarrow> (ord \<mu> \<and> lt 0 \<mu> \<and> (\<forall>\<beta>. lt \<beta> \<mu> \<longrightarrow> lt (succ \<beta>) \<mu>))" by (rule limit_iff)
  

  
  


  
