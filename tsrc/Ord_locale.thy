theory Ord_locale
  imports GZF_locale HOL.Orderings begin


(*It would be nice to use the \<open>class.wellorder\<close> locale, but unfortunately
  this assumes that the entire type is well-ordered by leq and lt, 
  but we just want this to be true for the ordinal portion.
  We could assume an 'Ordinal' subtype and assume an instantiation of the wellorder class on there, 
  then I imagine that the types-to-sets stuff could port all of the theorems we would import from type class
  to the portion of 'd such that Ord x holds.
  But this is too much work just to avoid assuming the axioms manually.  *)


locale Ord = GZF Mem Emp Set Union Subset Pow Succ Inf Repl
    for Mem :: "'d \<Rightarrow> 'd \<Rightarrow> bool" (infixl \<open>\<in>\<close> 50)
    and Emp :: "'d" (\<open>\<emptyset>\<close>) and Set :: "'d \<Rightarrow> bool" 
    and Union :: "'d \<Rightarrow> 'd" (\<open>\<Union>_\<close> [90] 90)
    and Subset:: "['d,'d] \<Rightarrow> bool" (infixl \<open>\<subseteq>\<close> 50)
    and Pow ::  "'d \<Rightarrow> 'd" (\<open>\<P>\<close> 90)
    and Succ :: "'d \<Rightarrow> 'd"
    and Inf :: "'d"  \<comment> \<open>witness of Infinity\<close>
    and Repl :: "[['d,'d] \<Rightarrow> bool] \<Rightarrow> 'd \<Rightarrow>'d" (\<open>\<R>\<close> 90)  +
  fixes
    Ord :: "'d \<Rightarrow> bool" and
    lt :: "'d \<Rightarrow> 'd \<Rightarrow> bool" (infixl \<open><\<close> 50) and
    zero :: "'d" (\<open>0\<close>) and
    succ :: "'d \<Rightarrow> 'd" and
    Limit :: "'d \<Rightarrow> bool" and
    predSet :: "'d \<Rightarrow> 'd" and
    OrdRec :: "('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd" and
    omega :: "'d" (\<open>\<omega>\<close>)
  assumes 
    (*Axioms for the Ord predicate*)
    zero_ord [simp]: "Ord 0" and
    \<omega>_ord [simp]: "Ord \<omega>" and
    lt_ord_ax : "\<forall>\<alpha> \<beta>. \<alpha> < \<beta> \<longrightarrow> Ord \<alpha> \<and> Ord \<beta>" and
    ord_succ_iff_ax : "\<forall>\<beta>. Ord (succ \<beta>) \<longleftrightarrow> Ord \<beta>" and
    (*Definition of 0, succ, leq and Limit*)
    zero_def : "\<forall>\<alpha>. \<not> (\<alpha> < 0)" and
    succ_def : "(\<forall>\<alpha> \<beta>. \<alpha> < (succ \<beta>) \<longleftrightarrow> \<alpha> < \<beta> | \<alpha> = \<beta> \<and> Ord \<beta>)" and
    limit_def : "\<forall>\<mu>. Limit \<mu> \<longleftrightarrow> (Ord \<mu> \<and> 0 < \<mu> \<and> (\<forall>\<beta>. \<beta> < \<mu> \<longrightarrow> succ \<beta> < \<mu>))" and
    \<omega>_def : "Limit \<omega> \<and> (\<forall>\<mu>. Limit \<mu> \<longrightarrow> \<omega> < \<mu>)" and
    (*Characterisation of < as a wellorder*)
    lt_trans : "\<forall>i j k. i < j \<longrightarrow> j < k \<longrightarrow> i < k" and
    lt_notsym : "\<forall>i j. i < j \<longrightarrow> \<not> j < i" and
    lt_linear : "\<forall>i j. Ord i \<and> Ord j \<longrightarrow> i < j | i = j | j < i" and
    lt_induct : "\<forall>a. Ord a \<longrightarrow> (\<forall>x. Ord x \<longrightarrow> (\<forall>y. y < x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> P a" and

    predset_def : "\<forall>\<beta>. Ord \<beta> \<longrightarrow> Set (predSet \<beta>) \<and> (\<forall>\<alpha>. \<alpha> \<in> predSet \<beta> \<longleftrightarrow> \<alpha> < \<beta>)" and
    ordrec_0 : "\<forall>G F A. OrdRec G F A 0 = A" and 
    ordrec_succ : "\<forall>G F A b.  
      OrdRec G F A (succ b) = F (succ b) (OrdRec G F A b)" and
    ordrec_lim :  "\<forall>G F A z. Limit z \<longrightarrow> 
      OrdRec G F A z = G z (Lambda (predSet z) (\<lambda>\<beta>. OrdRec G F A \<beta>))" 

context Ord begin 

lemma lt_ord : "\<alpha> < \<beta> \<Longrightarrow> Ord \<alpha> \<and> Ord \<beta>" using lt_ord_ax by auto
lemma lt_ord1: "j<i ==> Ord(j)"
  using lt_ord by simp

lemma lt_ord2: "j<i ==> Ord(i)"
  using lt_ord by simp

lemma ord_succ_iff [iff] : "Ord (succ \<beta>) \<longleftrightarrow> Ord \<beta>" using ord_succ_iff_ax by auto
lemma limit_iff : "Limit \<mu> \<longleftrightarrow> Ord \<mu> \<and> 0 < \<mu> \<and> (\<forall>\<beta>. \<beta> < \<mu> \<longrightarrow> succ \<beta> < \<mu>)" using limit_def by auto
lemma succ_ord [intro]:
  assumes "Ord x" shows "Ord (succ x)"
  using assms by (auto)

lemma succ_ordD : "Ord (succ i) \<Longrightarrow> Ord i" 
  using ord_succ_iff by simp

lemma predset_set : "Ord \<beta> \<Longrightarrow> Set (predSet \<beta>)"
  using predset_def by auto

lemma predset_iff : assumes "Ord \<beta>" 
  shows "\<alpha> \<in> predSet \<beta> \<longleftrightarrow> \<alpha> < \<beta>"
  using predset_def assms by auto

lemma predsetI : 
  shows "\<alpha> < \<beta> \<Longrightarrow> \<alpha> \<in> predSet \<beta>"
  using predset_iff lt_ord by auto

lemma predsetE : assumes "Ord \<beta>"
  shows "\<alpha> \<in> predSet \<beta> \<Longrightarrow> \<alpha> < \<beta>"
  using predset_iff[OF assms] by simp 
  
lemma predset_mem_ord : assumes "Ord \<beta>"
  shows "\<alpha> \<in> predSet \<beta> \<Longrightarrow> Ord \<alpha>"
  using predset_iff[OF \<open>Ord \<beta>\<close>] lt_ord1 by auto

lemma succ_lt : "Ord \<beta> \<Longrightarrow> \<beta> < succ \<beta>" using succ_def by auto

lemma zero_lt : "\<not> (\<alpha> < 0)" by (simp add: zero_def)

definition one :: "'d" (\<open>1\<close>) where
  "1 \<equiv> succ 0"

definition three :: "'d" (\<open>3\<close>) where
  "3 \<equiv> succ (succ 1)"

lemma Ord_1 [simp]: "Ord 1"
  unfolding one_def using succ_ord by simp

lemma Ord_3 [simp]: "Ord 3"
  unfolding three_def using succ_ord by simp

lemma trans_induct [consumes 1, case_names step] : 
 "Ord i \<Longrightarrow> (\<And>x. Ord x \<Longrightarrow> (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P i"
  using lt_induct by auto


lemmas le_Ord2 = lt_ord2 [THEN succ_ordD]
(* i<0 ==> R *)
lemmas lt0E = zero_lt [THEN notE, elim!]

lemma lt_trans_pure [trans]: "\<lbrakk> i < j ; j < k \<rbrakk> \<Longrightarrow> i < k" using lt_trans by blast

lemma lt_asym : "\<lbrakk> i<j; \<not> P \<Longrightarrow> j<i \<rbrakk> \<Longrightarrow> P" using lt_notsym by auto

lemma lt_irrefl [elim!]: "i<i \<Longrightarrow> P"
  by (blast intro: lt_asym)

lemma lt_not_refl: "\<not> i<i"
  using lt_irrefl by auto

abbreviation leq (infixl \<open>\<le>\<close> 50) where "x \<le> y \<equiv> x < succ y"

lemma le_iff: "i \<le> j <-> i<j | (i=j & Ord(j))" using succ_def by auto

lemma leI: "i<j ==> i \<le> j"
  by (simp add: le_iff)

lemma le_eqI: "[| i=j;  Ord(j) |] ==> i \<le> j"
by (simp add: le_iff)

lemmas le_refl = refl [THEN le_eqI]

lemma le_refl_iff [iff]: "i \<le> i <-> Ord(i)"
by (simp (no_asm_simp) add: lt_not_refl le_iff)

lemma leCI: "(~ (i=j & Ord(j)) ==> i<j) ==> i \<le> j"
by (simp add: le_iff, blast)

lemma leE:
    "[| i \<le> j;  i<j ==> P;  [| i=j;  Ord(j) |] ==> P |] ==> P"
by (simp add: le_iff, blast)

lemma le_anti_sym: "[| i \<le> j;  j \<le> i |] ==> i=j"
apply (simp add: le_iff)
apply (blast elim: lt_asym)
done

lemma le0_iff [simp]: "i \<le> 0 \<longleftrightarrow> i=0"
 using zero_ord by (blast elim!: leE)

lemmas le0D = le0_iff [THEN iffD1, dest!]

lemma Ord_linear_lt:
  assumes "Ord i" "Ord j"
  obtains (lt) "i < j" | (eq) "i=j" | (gt) "j < i"
  using assms lt_linear by auto

lemma Ord_linear2:
 assumes o: "Ord(i)" "Ord(j)"
 obtains (lt) "i<j" | (ge) "j \<le> i"
apply (rule_tac i = i and j = j in Ord_linear_lt)
apply (blast intro: leI le_eqI sym o) +
done

lemma Ord_linear_le:
 assumes o: "Ord(i)" "Ord(j)"
 obtains (le) "i \<le> j" | (ge) "j \<le> i"
apply (rule_tac i = i and j = j in Ord_linear_lt)
apply (blast intro: leI le_eqI o) +
  done

lemma le_imp_not_lt: "j \<le> i ==> ~ i<j"
by (blast elim!: leE elim: lt_asym)

lemma not_lt_imp_le: "[| ~ i<j;  Ord(i);  Ord(j) |] ==> j \<le> i"
by (rule_tac i = i and j = j in Ord_linear2, auto)

lemma not_lt_iff_le: "[| Ord(i);  Ord(j) |] ==> ~ i<j <-> j \<le> i"
by (blast dest: le_imp_not_lt not_lt_imp_le)

lemma not_le_iff_lt: "[| Ord(i);  Ord(j) |] ==> ~ i \<le> j <-> j<i"
  by (use not_lt_iff_le in auto) 
    (*Proof edited. WAS: (simp (no_asm_simp) add: not_lt_iff_le [THEN iff_sym]) *)

lemma Ord_0_le: "Ord(i) ==> 0 \<le> i"
  by (erule not_lt_iff_le [THEN iffD1], auto)

lemma Ord_0_lt: "[| Ord(i);  i\<noteq>0 |] ==> 0<i"
apply (erule not_le_iff_lt [THEN iffD1])
apply (rule zero_ord, blast)
done

lemma Ord_0_lt_iff: "Ord(i) ==> i\<noteq>0 <-> 0<i"
by (blast intro: Ord_0_lt)

lemma all_lt_imp_le: "[| Ord(i);  Ord(j);  !!x. x<j ==> x<i |] ==> j \<le> i"
  by (blast intro: not_lt_imp_le dest: lt_irrefl)

lemma lt_trans1: "[| i \<le> j;  j<k |] ==> i<k"
by (blast elim!: leE intro: lt_trans_pure)

lemma lt_trans2: "[| i<j;  j \<le> k |] ==> i<k"
by (blast elim!: leE intro: lt_trans_pure)

lemma le_trans: "[| i \<le> j;  j \<le> k |] ==> i \<le> k"
by (blast intro: lt_trans1)

lemma succ_leI: "i<j ==> succ(i) \<le> j"
proof (rule not_lt_iff_le [THEN iffD1])
  assume "i < j"
  thus "Ord j" using lt_ord2 by auto
  from \<open>i < j\<close> have "Ord i" using lt_ord by simp
  thus "Ord (succ i)" using succ_ord by auto
  from \<open>i < j\<close> show "\<not> j \<le> i" by (blast elim: leE lt_asym)
qed

lemma succ_leE: "succ(i) \<le> j ==> i<j"
proof (rule not_le_iff_lt [THEN iffD1])
  assume "succ i \<le> j"
  thus "Ord j" using lt_ord2 by auto
  from \<open>succ i \<le> j\<close> show "Ord i" using lt_ord succ_ordD by auto
  from \<open>succ i \<le> j\<close> show "\<not> j \<le> i" by (blast elim: leE lt_asym)
qed
(*WAS: 
apply (rule not_le_iff_lt [THEN iffD1])
apply (blast elim: ltE leE lt_asym)+
done *)


lemma succ_le_iff [iff]: "succ(i) \<le> j <-> i<j"
by (blast intro: succ_leI succ_leE)

lemma succ_le_imp_le: "succ(i) \<le> succ(j) ==> i \<le> j"
  by (blast)

lemma lt_imp_0_lt: "j<i ==> 0<i"
by (blast intro: lt_trans1 Ord_0_le [OF lt_ord1])

lemma le_succ_iff: "i \<le> succ(j) <-> i \<le> j | i=succ(j) & Ord(i)"
apply (simp (no_asm) add: le_iff)
apply blast
done

lemma limit_ord: "Limit(i) ==> Ord(i)"
  unfolding limit_iff by auto
(*WAS: 
apply (unfold Limit_def)
apply (erule conjunct1)
done *)  

lemma Limit_has_0: "Limit(i) ==> 0 < i"
  unfolding limit_iff by auto
(*WAS:
apply (unfold Limit_def)
apply (erule conjunct2 [THEN conjunct1])
done *)  

lemma Limit_nonzero: "Limit(i) ==> i \<noteq> 0"
by (drule Limit_has_0, blast)

lemma Limit_has_succ: "[| Limit(i);  j<i |] ==> succ(j) < i"
by (unfold limit_iff, blast)

lemma Limit_succ_lt_iff [simp]: assumes "Limit(i)" 
  shows  "succ(j) < i <-> (j<i)"
proof 
  assume "succ j < i"
  moreover hence "j < succ j" using lt_ord succ_lt by auto
  ultimately show "j < i" using lt_trans_pure by auto
next
  assume "j < i" thus "succ j < i" using Limit_has_succ[OF assms] by simp
qed
(*WAS: 
apply (safe intro!: Limit_has_succ)
apply (frule lt_ord)
apply (blast intro: lt_trans)
done*)

lemma zero_not_Limit [iff]: "~ Limit(0)"
  using limit_iff by auto
(*WAS: by (simp add: Limit_def)*)

lemma Limit_has_1: "Limit(i) ==> 1 < i"
 unfolding one_def by (blast intro: Limit_has_0 Limit_has_succ)
(*WAS: by (blast intro: Limit_has_0 Limit_has_succ) *)

lemma increasing_LimitI: "[| 0<l; \<forall>x. x < l \<longrightarrow> (\<exists>y. y < l \<and> x < y) |] ==> Limit(l)"
(*WAS: "[| 0<l; \<forall>x\<in>l. \<exists>y\<in>l. x<y |] ==> Limit(l)"*)
  by (unfold limit_iff, simp add: lt_ord2, clarify, blast intro: lt_trans1 lt_ord2)
(*WAS: apply (unfold Limit_def, simp add: lt_ord2, clarify)
apply (drule_tac i=y in ltD)
apply (blast intro: lt_trans1 [OF _ ltI] lt_ord2)
done*)


lemma non_succ_LimitI:
  assumes i: "0<i" and nsucc: "\<And>y. succ(y) \<noteq> i"
  shows "Limit(i)"
proof -
  have Oi: "Ord(i)" using i by (simp add: lt_ord2)
  { fix y
    assume yi: "y<i"
    hence Osy: "Ord(succ(y))" by (simp add: lt_ord succ_ord)
    have "~ i \<le> y" using yi by (blast dest: le_imp_not_lt)
    hence "succ(y) < i" using nsucc [of y]
      by (blast intro: Ord_linear_lt [OF Osy Oi]) }
  thus ?thesis using i Oi by (auto simp add: limit_iff)
qed

lemma succ_LimitE [elim!]: "Limit(succ(i)) ==> P"
apply (rule lt_irrefl)
apply (rule Limit_has_succ, assumption)
apply (erule limit_ord [THEN succ_ordD, THEN le_refl])
done

lemma not_succ_Limit [simp]: "~ Limit(succ(i))"
by blast

lemma Limit_le_succD: "[| Limit(i);  i \<le> succ(j) |] ==> i \<le> j"
  by (blast elim!: leE)

lemma ord_cases_disj: "Ord(i) ==> i=0 | (\<exists>j. Ord(j) & i=succ(j)) | Limit(i)"
by (blast intro!: non_succ_LimitI Ord_0_lt)

lemma ord_cases:
 assumes i: "Ord(i)"
 obtains ("0") "i=0" | (succ) j where "Ord(j)" "i=succ(j)" | (limit) "Limit(i)"
by (insert ord_cases_disj [OF i], auto)

lemma trans_induct3_raw:
     "[| Ord(i);
         P(0);
         !!x. [| Ord(x);  P(x) |] ==> P(succ(x));
         !!x. [| Limit(x);  \<forall>y. y < x \<longrightarrow> P(y) |] ==> P(x)
      |] ==> P(i)"
apply (erule trans_induct)
apply (erule ord_cases, blast+)
done

lemma trans_induct3 [case_names 0 succ limit, consumes 1]:
  assumes "Ord(i)" "P(0)" 
    "(\<And>x. Ord(x) \<Longrightarrow> P(x) \<Longrightarrow> P(succ(x)))"
    "(\<And>x. Limit(x) \<Longrightarrow> (\<And>y. y < x \<Longrightarrow> P(y)) \<Longrightarrow> P(x))" 
    shows "P(i)"
  using trans_induct3_raw [of i P, OF assms] by simp 


lemma \<omega>_lim : "Limit \<omega>" using \<omega>_def by simp
lemma \<omega>_0 : "0 < \<omega>" using \<omega>_lim limit_def by auto
lemma \<omega>_succ : "\<beta> < \<omega> \<Longrightarrow> succ \<beta> < \<omega>" using \<omega>_lim limit_def by auto

(*Needs to come before the locale specification of Ops *)
abbreviation setseq where "setseq X \<equiv> rall (\<lambda>\<beta>. \<beta> < \<omega>) (\<lambda>\<beta>. Set (X \<beta>))"


end
end






    