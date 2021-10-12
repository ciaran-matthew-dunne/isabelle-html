theory Model_locale
  imports Ord_locale
  keywords "model_interpretation" "model_closed" :: thy_goal 
  begin


locale Model = Ord Mem Emp Set Union Subset Pow Succ Inf Repl
    for Mem :: "'d \<Rightarrow> 'd \<Rightarrow> bool" (infixl \<open>\<in>\<close> 50)
    and Emp :: "'d" (\<open>\<emptyset>\<close>) and Set :: "'d \<Rightarrow> bool" 
    and Union :: "'d \<Rightarrow> 'd" (\<open>\<Union>_\<close> [90] 90)
    and Subset:: "['d,'d] \<Rightarrow> bool" (infixl \<open>\<subseteq>\<close> 50)
    and Pow ::  "'d \<Rightarrow> 'd" (\<open>\<P>\<close> 90)
    and Succ :: "'d \<Rightarrow> 'd"
    and Inf :: "'d"  \<comment> \<open>witness of Infinity\<close>
    and Repl :: "[['d,'d] \<Rightarrow> bool] \<Rightarrow> 'd \<Rightarrow>'d" (\<open>\<R>\<close> 90)  +
  fixes
    set :: "'d" and ord :: "'d" and
    Ops :: "'d \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd" and
    Ignored :: "'d"
  assumes (*Consider abstracting the tag from the locale,
            because later we will want to keep the proofs,
            but not the tag*)
          (*Can we make a weak set theory?*)
    tags : "set < \<omega> \<and> ord < \<omega>" and
    ops_set_0 : "Ops set 0 x = \<emptyset>" and
    ops_set_succ : "\<forall>\<beta>. Ord \<beta> \<longrightarrow> Ops set (succ \<beta>) = Pow" and
    ops_set_lim : "\<forall>\<mu>. Limit \<mu> \<longrightarrow> Ops set \<mu> = Union" and
    ops_0_ord : "\<forall>\<beta>. Ord \<beta> \<longrightarrow> Ops ord \<beta> x = sng \<beta>" and 
    ops_setseq_ax : "\<forall>\<beta> x. setseq (\<lambda>\<alpha>. Ops \<alpha> \<beta> x)" and
    ig_set : "Set (Ignored)"
  
context Model begin 

subsection \<open>Tagging operations - currently implemented with Kuratowski pairs\<close>

abbreviation Tag :: "'d \<Rightarrow> 'd \<Rightarrow> 'd" (infixl \<open>\<triangleright>\<close> 70) where
  "n \<triangleright> x \<equiv> kpair n x"

abbreviation TagOf :: "'d \<Rightarrow> 'd" where
  "TagOf x \<equiv> \<tau> x"

abbreviation ObjOf :: "'d \<Rightarrow> 'd" where
  "ObjOf x \<equiv> \<pi> x"

subsection \<open>Tag all members of a set\<close>

definition TagSetMems :: "'d \<Rightarrow> 'd \<Rightarrow> 'd" where 
  "TagSetMems \<beta> x \<equiv> RepFun (\<lambda>a. \<beta> \<triangleright> a) x"

lemma tmap_set : "Set x \<Longrightarrow> Set (TagSetMems \<beta> x)"
  unfolding TagSetMems_def by (rule repfun_set)

lemma tmap_iff : assumes "Set x" shows
  "b \<in> x \<longleftrightarrow> \<beta> \<triangleright> b \<in> TagSetMems \<beta> x"
  unfolding TagSetMems_def  
  by (simp add: repfun_iff[OF assms],
      blast elim: pair_inject)

lemma tmapI : "b \<in> x \<Longrightarrow> \<beta> \<triangleright> b \<in> TagSetMems \<beta> x"
  using setI tmap_iff by auto 

lemma tmapD : assumes "Set x" 
  shows "b \<in> TagSetMems \<beta> x \<Longrightarrow> bex x (\<lambda>b'. b = (\<beta> \<triangleright> b'))"
  unfolding TagSetMems_def by (auto elim: repfunE[OF assms])

lemma tmapE : assumes "Set x"
  shows " \<lbrakk> b \<in> TagSetMems \<beta> x ; 
    \<And>b'.\<lbrakk> b' \<in> x ; b = (\<beta> \<triangleright> b') \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P "
  unfolding TagSetMems_def  by (rule repfunE[OF assms])


subsection \<open>Disjoint Union of a sequence of sets\<close>

definition disj :: "['d \<Rightarrow> 'd] \<Rightarrow> 'd" (\<open>\<Uplus>\<close>) where
 "\<Uplus> X \<equiv> \<Union> RepFun (\<lambda>b. TagSetMems b (X b)) (predSet \<omega>)" 

lemma disj_set : "Set (\<Uplus> X)" unfolding disj_def
  by (rule union_set[OF repfun_set[OF predset_set[OF \<omega>_ord]]])

lemma disj_iff : assumes "setseq X" 
  shows "b \<in> \<Uplus> X \<longleftrightarrow> (rex (\<lambda>\<beta>. \<beta> < \<omega>) (\<lambda>\<beta>. bex (X \<beta>) (\<lambda>b'. b = (\<beta> \<triangleright> b'))))"
  unfolding disj_def 
proof (simp add: repfun_union[OF predset_set[OF \<omega>_ord]], rule)
  assume "bex (predSet \<omega>) (\<lambda>\<beta>. b \<in> TagSetMems \<beta> (X \<beta>))"
  then obtain \<beta> where "\<beta> < \<omega>" "b \<in> TagSetMems \<beta> (X \<beta>)" using predset_iff[OF \<omega>_ord] by auto
  thus "rex (\<lambda>\<beta>. \<beta> < \<omega>) (\<lambda>\<beta>. bex (X \<beta>) (\<lambda>b'. b = (\<beta> \<triangleright> b')))" unfolding rex_def
    using assms \<open>\<beta> < \<omega>\<close> by (blast elim: tmapE)
next
  assume "rex (\<lambda>\<beta>. \<beta> < \<omega>) (\<lambda>\<beta>. bex (X \<beta>) (\<lambda>b'. b = (\<beta> \<triangleright> b')))"
  then obtain \<beta> and b' where "\<beta> < \<omega>" "b = (\<beta> \<triangleright> b')" "b' \<in> X \<beta>" by auto
  hence "\<beta> \<in> predSet \<omega>" and "b \<in> TagSetMems \<beta> (X \<beta>)" 
    using predset_iff[OF \<omega>_ord] tmap_iff assms \<open>\<beta> < \<omega>\<close> by auto
  thus "bex (predSet \<omega>) (\<lambda>\<beta>. b \<in> TagSetMems \<beta> (X \<beta>))" by auto
qed

(*Weaker version*)
lemma disj_iff' : assumes "setseq X" 
  shows "\<beta> \<triangleright> b' \<in> \<Uplus> X \<longleftrightarrow> \<beta> < \<omega> \<and> b' \<in> X \<beta>"
  by (simp add: disj_iff[OF assms], 
      auto elim: pair_inject)

lemma disjI : "\<lbrakk> \<beta> < \<omega> ; b' \<in> X \<beta> \<rbrakk> \<Longrightarrow> \<beta> \<triangleright> b' \<in> \<Uplus> X"
  unfolding disj_def using 
    repfun_union[OF predset_set[OF \<omega>_ord]] 
    predset_iff[OF \<omega>_ord] 
  by (blast intro: tmapI)
  
lemma disjE : assumes "setseq X" 
  shows "\<lbrakk> b \<in> \<Uplus> X ; \<And>\<beta> b'. \<lbrakk> b = (\<beta> \<triangleright> b') ; \<beta> < \<omega> ; b' \<in> X \<beta>\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using disj_iff[OF assms] by auto


subsection \<open>Subset of a tagged set with tag \<beta>\<close>

definition Part :: "'d \<Rightarrow> 'd \<Rightarrow> 'd" where
 "Part \<beta> x \<equiv> Collect (\<lambda>b. (\<exists>b'. b = (\<beta> \<triangleright> b'))) x"

lemma part_set : assumes "Set x" 
  shows "Set (Part \<beta> x)" unfolding Part_def by (rule collect_set[OF assms])

lemma part_iff : assumes "Set x" 
  shows "b \<in> Part \<beta> x \<longleftrightarrow> b \<in> x \<and> (\<exists>b'. b = (\<beta> \<triangleright> b'))"
  unfolding Part_def using collect_iff[OF assms] by auto

lemma partI : "\<lbrakk> b = (\<beta> \<triangleright> b'); b \<in> x \<rbrakk> \<Longrightarrow> b \<in> Part \<beta> x "
  using part_iff setI by auto

lemma partD1 : assumes "Set x" shows "b \<in> Part \<beta> x \<Longrightarrow> \<tau> b = \<beta>"
  using part_iff[OF \<open>Set x\<close>] fst_eq by auto

lemma partD2 : assumes "Set x" shows "b \<in> Part \<beta> x \<Longrightarrow> b \<in> x" 
  using part_iff[OF \<open>Set x\<close>] by auto

lemma partE : assumes "Set x" 
  shows "\<lbrakk> b \<in> Part \<beta> x ; \<And>b'. \<lbrakk> b \<in> x ; b = (\<beta> \<triangleright> b') \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using part_iff[OF assms] by auto

lemma partD_pair : assumes "Set x" 
  shows "\<alpha> \<triangleright> b \<in> Part \<beta> x \<Longrightarrow> \<alpha> = \<beta>"
  using part_iff[OF assms] pair_inject by auto

lemma part_subset :
  shows "x \<subseteq> y \<Longrightarrow> Part \<alpha> x \<subseteq> Part \<alpha> y"
proof - 
  assume "x \<subseteq> y" hence "Set x" "Set y" using subset_set by simp_all
  hence "Set (Part \<alpha> x)" "Set (Part \<alpha> y)" using part_set by simp_all
  thus "Part \<alpha> x \<subseteq> Part \<alpha> y" 
  proof
    fix a assume "a \<in> Part \<alpha> x" thus "a \<in> Part \<alpha> y" 
      using \<open>x \<subseteq> y\<close> by (auto intro: partI elim: partE[OF \<open>Set x\<close>])
  qed
qed

lemma part_union : assumes "Set x" "Set y" shows "Part \<alpha> (x \<union> y) = Part \<alpha> x \<union> Part \<alpha> y"
proof (rule equality_iffI[OF part_set[OF un_set] un_set], simp add: un_iff, rule)
  fix a assume "a \<in> Part \<alpha> (x \<union> y)" 
  thus "a \<in> Part \<alpha> x \<or> a \<in> Part \<alpha> y" 
  proof (rule partE[OF un_set])
    fix a' assume "a \<in> x \<union> y" "a = (\<alpha> \<triangleright> a')"
    from \<open>a \<in> x \<union> y\<close> show "a \<in> Part \<alpha> x \<or> a \<in> Part \<alpha> y" 
      by (auto elim: unE intro: partI[OF \<open>a = (\<alpha> \<triangleright> a')\<close>])
  qed
next
  fix a assume "a \<in> Part \<alpha> x \<or> a \<in> Part \<alpha> y"
  thus "a \<in> Part \<alpha> (x \<union> y)" proof
    assume "a \<in> Part \<alpha> x" thus "a \<in> Part \<alpha> (x \<union> y)" 
      using part_subset[OF un_subset1[OF \<open>Set x\<close>]] by auto
  next
    assume "a \<in> Part \<alpha> y" thus "a \<in> Part \<alpha> (x \<union> y)" 
      using part_subset[OF un_subset2[OF \<open>Set y\<close>]] by auto
  qed
qed

lemma part_disj_iff : assumes "setseq X" 
  shows "b \<in> Part \<beta> (\<Uplus> X) \<longleftrightarrow> (\<beta> < \<omega> \<and> bex (X \<beta>) (\<lambda>b'. b = (\<beta> \<triangleright> b')))"  
  by (simp add: part_iff[OF disj_set] disj_iff[OF \<open>setseq X\<close>], 
      auto elim: pair_inject)

lemma part_disjI : "\<lbrakk> b = (\<beta> \<triangleright> b') ; b' \<in> X \<beta> ; \<beta> < \<omega> \<rbrakk> \<Longrightarrow> b \<in> Part \<beta> (\<Uplus> X)"  
  by (auto intro: partI disjI)

lemma part_disjE : assumes "setseq X" shows 
  "\<lbrakk> b \<in> Part \<beta> (\<Uplus> X) ; \<And>b'. \<lbrakk> b = (\<beta> \<triangleright> b') ; \<beta> < \<omega> ; b' \<in> X \<beta>  \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using part_disj_iff[OF assms] by auto
  
lemma set_tag : "set < \<omega>" by (simp add: tags)
lemma ord_tag : "ord < \<omega>" by (simp add: tags)

subsection \<open>Tier -- model building operator\<close>

definition Tier :: "'d \<Rightarrow> 'd" where
 "Tier \<equiv> OrdRec (\<lambda>\<mu> x. \<Uplus> (\<lambda>\<alpha>. Ops \<alpha> \<mu> x)) 
                (\<lambda>\<beta> x. x \<union> \<Uplus> (\<lambda>\<alpha>. Ops \<alpha> \<beta> (x - Ignored))) 
                (\<Uplus> (\<lambda>\<alpha>. Ops \<alpha> 0 \<emptyset>))"

lemma ops_setseq : "setseq (\<lambda>\<alpha>. Ops \<alpha> \<beta> x)"
  by (simp add: ops_setseq_ax)

thm disj_iff'[OF ops_setseq]  

subsection \<open>General lemmas about the structure of Tier\<close>

lemma tier_0 : "Tier 0 = \<Uplus> (\<lambda>a. Ops a 0 \<emptyset>)" 
  unfolding Tier_def using ordrec_0 by simp

lemma tier0_iff : "x \<in> Tier 0 \<longleftrightarrow> rex (\<lambda>\<alpha>. \<alpha> < \<omega>) (\<lambda>\<alpha>. bex (Ops \<alpha> 0 \<emptyset>) (\<lambda>x'. x = (\<alpha> \<triangleright> x')))"
  unfolding tier_0 by (simp add: disj_iff[OF ops_setseq])

lemma tier0_iff' : "\<alpha> \<triangleright> x' \<in> Tier 0 \<longleftrightarrow> \<alpha> < \<omega> \<and> x' \<in> Ops \<alpha> 0 \<emptyset> "
  using tier0_iff by (auto elim: pair_inject)

lemma tier_succ : assumes "Ord \<beta>"
  shows "Tier (succ \<beta>) = Tier \<beta> \<union> \<Uplus> (\<lambda>a. Ops a (succ \<beta>) (Tier \<beta> - Ignored))"
  unfolding Tier_def using ordrec_succ assms by simp

lemma tier_succ_iff : assumes "Ord \<beta>" 
  shows "x \<in> Tier (succ \<beta>) \<longleftrightarrow> x \<in> Tier \<beta> \<or> (rex (\<lambda>\<alpha>. \<alpha> < \<omega>) (\<lambda>\<alpha>. bex (Ops \<alpha> (succ \<beta>) (Tier \<beta> - Ignored)) (\<lambda>x'. x = (\<alpha> \<triangleright> x'))))"
  unfolding tier_succ[OF assms] un_iff disj_iff[OF ops_setseq] by simp

lemma tier_succ_iff' : assumes "Ord \<beta>"
  shows "\<alpha> \<triangleright> x' \<in> Tier (succ \<beta>) \<longleftrightarrow> (\<alpha> \<triangleright> x') \<in> Tier \<beta> \<or> (\<alpha> < \<omega> \<and> x' \<in> Ops \<alpha> (succ \<beta>) (Tier \<beta> - Ignored))"
  using tier_succ_iff[OF assms] by (auto elim: pair_inject)

lemma tier_limit : assumes "Limit \<mu>" 
  shows "Tier \<mu> = \<Uplus> (\<lambda>a. Ops a \<mu> (Lambda (predSet \<mu>) (\<lambda>\<beta>. Tier \<beta>)))"
  unfolding Tier_def using ordrec_lim assms by auto

lemma tier_limit_iff : assumes "Limit \<mu>"
  shows "x \<in> Tier \<mu> \<longleftrightarrow> rex (\<lambda>\<alpha>. \<alpha> < \<omega>) (\<lambda>\<alpha>. bex (Ops \<alpha> \<mu> (Lambda (predSet \<mu>) (\<lambda>\<beta>. Tier \<beta>))) (\<lambda>x'. x = (\<alpha> \<triangleright> x')))"
  unfolding tier_limit[OF assms] disj_iff[OF ops_setseq] by simp

lemma tier_limit_iff' : assumes "Limit \<mu>"
  shows "\<alpha> \<triangleright> x' \<in> Tier \<mu> \<longleftrightarrow> \<alpha> < \<omega> \<and> x' \<in> Ops \<alpha> \<mu> (Lambda (predSet \<mu>) (\<lambda>\<beta>. Tier \<beta>))"
  using tier_limit_iff[OF assms] by (auto elim: pair_inject)

lemma tier_set : assumes "Ord \<beta>" shows "Set (Tier \<beta>)"
  by (rule ord_cases[OF assms], simp_all add: disj_set un_set tier_0 tier_succ tier_limit)

corollary tier0_set : "Set (Tier 0)" by (rule tier_set[OF zero_ord])
corollary tiersucc_set : "Ord \<beta> \<Longrightarrow> Set (Tier (succ \<beta>))" by (rule tier_set[OF succ_ord])
corollary tierlimit_set : "Limit \<mu> \<Longrightarrow> Set (Tier \<mu>)" by (rule tier_set[OF limit_ord])

subsection \<open>Parts of Tier\<close>

lemma part_tier0_iff : "x \<in> Part \<alpha> (Tier 0) \<longleftrightarrow> \<alpha> < \<omega> \<and> bex (Ops \<alpha> 0 \<emptyset>) (\<lambda>x'. x = (\<alpha> \<triangleright> x'))"
  by (simp add: part_iff[OF tier0_set] tier0_iff, auto elim: pair_inject)

lemma part_tier0I : "\<lbrakk> \<alpha> < \<omega> ; x' \<in> Ops \<alpha> 0 \<emptyset> ; x = \<alpha> \<triangleright> x' \<rbrakk> \<Longrightarrow> x \<in> Part \<alpha> (Tier 0)"
  using part_tier0_iff by auto

lemma part_tier0E : "\<lbrakk> x \<in> Part \<alpha> (Tier 0) ; \<And>x'. \<lbrakk> x' \<in> Ops \<alpha> 0 \<emptyset> ; x = \<alpha> \<triangleright> x' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using part_tier0_iff by auto

(* A strong but ugly lemma for the successor case *)
lemma part_tiersucc_iff : assumes "Ord \<beta>" shows "x \<in> Part \<alpha> (Tier (succ \<beta>)) \<longleftrightarrow>
  (x \<in> Part \<alpha> (Tier \<beta>) \<or> (\<alpha> < \<omega> \<and> bex (Ops \<alpha> (succ \<beta>) (Tier \<beta> - Ignored)) (\<lambda>x'. x = (\<alpha> \<triangleright> x'))))"
  by (simp add: tier_succ[OF assms] 
                part_union[OF tier_set[OF assms] disj_set] 
                un_iff part_disj_iff[OF ops_setseq])

lemma part_tiersuccI1 : assumes "Ord \<beta>" 
  shows "\<lbrakk> \<alpha> < \<omega> ; x' \<in> Ops \<alpha> (succ \<beta>) (Tier \<beta> - Ignored); x = \<alpha> \<triangleright> x'\<rbrakk> 
        \<Longrightarrow> x \<in> Part \<alpha> (Tier (succ \<beta>))"
  using part_tiersucc_iff[OF assms] by auto

lemma part_tiersuccI2 : assumes "Ord \<beta>" 
  shows "x \<in> Part \<alpha> (Tier \<beta>) \<Longrightarrow> x \<in> Part \<alpha> (Tier (succ \<beta>))"
  using part_tiersucc_iff[OF assms] by auto

lemma part_tiersuccE : assumes "Ord \<beta>" shows "\<lbrakk> x \<in> Part \<alpha> (Tier (succ \<beta>)) ;
        x \<in> Part \<alpha> (Tier \<beta>)  \<Longrightarrow> P ; 
  \<And>x'.\<lbrakk> x' \<in> Ops \<alpha> (succ \<beta>) (Tier \<beta> - Ignored) ; x = \<alpha> \<triangleright> x' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using part_tiersucc_iff[OF assms] by auto


lemma part_tierlim_iff : assumes "Limit \<mu>"
  shows "x \<in> Part \<alpha> (Tier \<mu>) \<longleftrightarrow> \<alpha> < \<omega> \<and> bex (Ops \<alpha> \<mu> (Lambda (predSet \<mu>) (\<lambda>\<beta>. Tier \<beta>))) (\<lambda>x'. x = (\<alpha> \<triangleright> x'))"
  unfolding part_iff[OF tierlimit_set[OF \<open>Limit \<mu>\<close>]] tier_limit_iff[OF \<open>Limit \<mu>\<close>]
  by (auto elim: pair_inject)

lemma part_tierlimI : assumes "Limit \<mu>" 
  shows "\<lbrakk> \<alpha> < \<omega> ; x' \<in> Ops \<alpha> \<mu> (Lambda (predSet \<mu>) (\<lambda>\<beta>. Tier \<beta>)); x = \<alpha> \<triangleright> x'\<rbrakk> 
        \<Longrightarrow> x \<in> Part \<alpha> (Tier \<mu>)"
  using part_tierlim_iff[OF assms] by auto

lemma part_tierlimitE : assumes "Limit \<mu>" shows "\<lbrakk> x \<in> Part \<alpha> (Tier \<mu>) ;
  \<And>x'.\<lbrakk> x' \<in> Ops \<alpha> \<mu> (Lambda (predSet \<mu>) (\<lambda>\<beta>. Tier \<beta>)) ; x = \<alpha> \<triangleright> x' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using part_tierlim_iff[OF assms] by auto

subsection \<open>Structure of the 'set' part of Tier\<close>

lemma tier_set_0 : "Part set (Tier 0) = \<emptyset>"
  by (rule equals0I[OF part_set[OF tier0_set]], unfold part_tier0_iff ops_set_0, auto)

thm part_tiersucc_iff
thm powI
lemma tier_set_succ : assumes "Ord \<beta>" 
  shows "Part set (Tier (succ \<beta>)) = Pow (Tier \<beta>)"
  sorry

lemma subset_succ_iff : assumes "Ord \<beta>" shows
  "x \<subseteq> Tier \<beta> \<longleftrightarrow> set \<triangleright> x \<in> Tier (succ \<beta>)"
  sorry

definition inModel :: "'d \<Rightarrow> bool" (\<open>M\<close>) where
  "inModel x \<equiv> rex Ord (\<lambda>\<alpha>. x \<in> Tier \<alpha>)"

lemma modelI [intro] : "\<lbrakk>Ord i ; x \<in> Tier i\<rbrakk> \<Longrightarrow> M x" 
  unfolding inModel_def by (rule rexI)

definition mall :: "('d \<Rightarrow> bool) \<Rightarrow> bool" where
  "mall P \<equiv> rall inModel P"

definition "mex P \<equiv> rex inModel P"
definition "muniq P \<equiv> mall (\<lambda>y. mall (\<lambda>z. P y \<and> P z \<longrightarrow> y = z))"
definition "mrall P Q \<equiv> mall (\<lambda>x. P x \<longrightarrow> Q x)" 
definition "mrex P Q \<equiv> mex (\<lambda>x. P x \<and> Q x)" 
definition "fun_mall P \<equiv> (\<forall>F. (\<forall>x. M x \<longrightarrow> M (F x)) \<longrightarrow> P F)"
definition "binfun_mall P \<equiv> (\<forall>F. (\<forall>x y. M x \<and> M y \<longrightarrow> M (F x y)) \<longrightarrow> P F)"

(*Model versions of GZF constants
  Higher-order parameters of model operators MUST be restricted to the model,
  otherwise it is painful to prove transfer rules.*)
definition forceM where "forceM x \<equiv> if M x then x else set \<triangleright> \<emptyset>"
definition "mEmp \<equiv> set \<triangleright> \<emptyset>" 
definition "mSet x \<equiv> TagOf x = set"
definition "mMem x y \<equiv> mSet x \<and> (x \<in> (ObjOf y))" 
definition "mSubset x y \<equiv> mSet x \<and> mSet y \<and> (\<forall>a. mMem a x \<longrightarrow> mMem a y)"
definition "mPow x \<equiv> set \<triangleright> (TagSetMems set  (Pow (ObjOf x)))"
definition "mUnion x \<equiv> set \<triangleright> (\<Union> (RepFun ObjOf (ObjOf x)))"
definition "mSucc x \<equiv> mUnion (set \<triangleright> (upair x (set \<triangleright> (sng x))))"
abbreviation "\<Theta> n \<equiv> OrdRec (\<lambda>_ x. set \<triangleright> x) (\<lambda>_ x. mSucc x) (set \<triangleright> \<emptyset>) n"
definition "mInf \<equiv> set \<triangleright> (\<Theta> \<omega>)"
definition "mRepl P x \<equiv> set \<triangleright> (Replace (\<lambda>a b. P (forceM a) (forceM b)) (ObjOf x))"

(*Model versions of Ord constants*)
definition "mOrd_conv \<beta> \<equiv> ord \<triangleright> \<beta>"
definition "mOrd \<B> \<equiv> TagOf \<B> = ord"
definition "mpredSet \<B> \<equiv> set \<triangleright> (TagSetMems ord (predSet (ObjOf \<B>)))"
definition "mOrdRec L F A \<B> \<equiv> OrdRec (\<lambda>a b. L (forceM a) (forceM b)) (\<lambda>a b. F (forceM a) (forceM b)) A (ObjOf \<B>)"
definition "mlt \<A> \<B> \<equiv> (ObjOf \<A>) < (ObjOf \<B>)"
definition "mzero \<equiv> ord \<triangleright> 0" 
definition "mone \<equiv> ord \<triangleright> set"
definition "msucc \<B> \<equiv> ord \<triangleright> (succ (ObjOf \<B>))"
definition "mLimit \<B> \<equiv> Limit (ObjOf \<B>)"
definition "momega \<equiv> ord \<triangleright> \<omega>"

ML_file \<open>translate_locale.ML\<close>

model_interpretation trans_gzf : mGZF
  sorry

model_interpretation trans_ord : mOrd 
  sorry


ML \<open>Goal.prove\<close>

ML_file \<open>model_closed.ML\<close>

model_closed closed_gzf : mGZF
  sorry

model_closed closed_ord : mOrd
  sorry

lemma forceM_elim [simp] : "M (forceM x)"
  using forceM_def closed_gzf(1) unfolding mEmp_def by auto

lemma forceM_eq : "M x \<Longrightarrow> forceM x = x"
  unfolding forceM_def by auto

end
end






    