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



abbreviation tr3 where "tr3 G F A \<beta> \<equiv> transrec3 A F (\<lambda>\<alpha> f. G \<alpha> (VLambda \<alpha> f)) \<beta>"
abbreviation ord where "ord x \<equiv> ZFC_in_HOL.Ord x"
abbreviation lt where "lt x y \<equiv> x < y \<and> ord x \<and> ord y" 
lemma succD : "ord (succ i) \<Longrightarrow> ord i"
  by (erule Ord_in_Ord, auto)


(*Can't be proved automatically - might have to copy some of the development from Isabelle/ZF?*)
lemma succ_iff : "i < succ j \<longleftrightarrow> i = j | (i < j & ord j)" sorry

interpretation Ord_HOL : Ord mem 0 "(\<lambda>x. True)" union subset VPow succ \<omega> repl
                             ord lt 0 succ Limit "(\<lambda>x. x)" tr3 \<omega>
proof (unfold_locales)
  show "ord 0" by auto
  show "ord \<omega>" by auto
  fix i j show "lt i j \<longrightarrow> ord i \<and> ord j" by auto
  fix i j show "ord (succ i) \<longleftrightarrow> ord i" using Ord_in_Ord by auto
  fix i show "\<not> lt i 0" by auto
  show "\<forall>\<beta>. ord \<beta> \<longrightarrow> (\<forall>\<alpha>. lt \<alpha> (succ \<beta>) \<longleftrightarrow> (\<alpha> = \<beta> \<or> lt \<alpha> \<beta>))" using Ord_in_Ord by auto

