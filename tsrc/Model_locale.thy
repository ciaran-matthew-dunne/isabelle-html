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
    ops_setseq_ax : "\<forall>\<beta> x. setseq (\<lambda>\<alpha>. Ops \<alpha> \<beta> x)" and
    ig_set : "Set (Ignored)" and

    tags : "set < \<omega> \<and> ord < \<omega>" and
    ops_set_0_ax : "Ops set 0 x = \<emptyset>" and
    ops_set_succ_ax : "\<forall>\<beta>. Ord \<beta> \<longrightarrow> Ops set (succ \<beta>) = Pow" and
    ops_set_lim_ax : "\<forall>\<mu>. Limit \<mu> \<longrightarrow> Ops set \<mu> f = \<emptyset>" and
    ops_ord_ax : "\<forall>\<beta>. Ord \<beta> \<longrightarrow> Ops ord \<beta> x = sng \<beta>"

  
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

lemma partI' : "\<alpha> \<triangleright> b \<in> x \<Longrightarrow> \<alpha> \<triangleright> b \<in> Part \<alpha> x"
  using partI by auto

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
 "Tier \<equiv> OrdRec (\<lambda>\<mu> f. (\<Union> (f[predSet \<mu>])) \<union> \<Uplus> (\<lambda>\<alpha>. Ops \<alpha> \<mu> f - Ignored)) 
                (\<lambda>\<beta> x. x \<union> \<Uplus> (\<lambda>\<alpha>. Ops \<alpha> \<beta> (x - Ignored))) 
                (\<Uplus> (\<lambda>\<alpha>. Ops \<alpha> 0 \<emptyset>))"

lemma no_set_ignored : "set \<triangleright> x' \<notin> Ignored" sorry
lemma no_ord_ignored : "ord \<triangleright> b' \<notin> Ignored" sorry

lemma ops_setseq : "setseq (\<lambda>\<alpha>. Ops \<alpha> \<beta> x)"
  by (simp add: ops_setseq_ax)

lemma ops_ig_setseq : "setseq (\<lambda>\<alpha>. Ops \<alpha> \<beta> x - Ignored)"
  using ops_setseq diff_set by blast

lemma ops_set : "\<alpha> < \<omega> \<Longrightarrow> Set (Ops \<alpha> \<beta> x)"
  using ops_setseq by auto

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

lemma tier_succI1 : assumes "Ord \<beta>"
  shows "x \<in> Tier \<beta> \<Longrightarrow> x \<in> Tier (succ \<beta>)"
  unfolding tier_succ_iff[OF assms] by simp

lemma tier_succI2 : assumes "Ord \<beta>"
  shows "\<lbrakk> \<alpha> < \<omega>;  x = \<alpha> \<triangleright> x'; x' \<in> Ops \<alpha> (succ \<beta>) (Tier \<beta> - Ignored) \<rbrakk> \<Longrightarrow> x \<in> Tier (succ \<beta>)"
  using tier_succ_iff[OF assms] by auto
 
lemma tier_succE : assumes "Ord \<beta>"
  shows "\<lbrakk> x \<in> Tier (succ \<beta>); x \<in> Tier \<beta> \<Longrightarrow> P; 
   \<And>\<alpha> x'.\<lbrakk> \<alpha> < \<omega>; x = \<alpha> \<triangleright> x'; x' \<in> Ops \<alpha> (succ \<beta>) (Tier \<beta> - Ignored)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using tier_succ_iff[OF assms] by blast

lemma tier_succ_iff' : assumes "Ord \<beta>"
  shows "\<alpha> \<triangleright> x' \<in> Tier (succ \<beta>) \<longleftrightarrow> (\<alpha> \<triangleright> x') \<in> Tier \<beta> \<or> (\<alpha> < \<omega> \<and> x' \<in> Ops \<alpha> (succ \<beta>) (Tier \<beta> - Ignored))"
  using tier_succ_iff[OF assms] by (auto elim: pair_inject)

lemma tier_limit : assumes "Limit \<mu>" 
  shows "Tier \<mu> = (\<Union> RepFun Tier (predSet \<mu>)) \<union> 
                (\<Uplus> (\<lambda>\<alpha>. Ops \<alpha> \<mu> (Lambda (predSet \<mu>) (\<lambda>\<beta>. Tier \<beta>)) - Ignored))"
  unfolding Tier_def by (simp add: ordrec_lim assms image_domain) 

lemma tier_lim_iff : assumes "Limit \<mu>"
  shows "x \<in> Tier \<mu> \<longleftrightarrow> (rex (\<lambda>\<beta>. \<beta> < \<mu>) (\<lambda>\<beta>. x \<in> Tier \<beta>)) 
                     \<or> (rex (\<lambda>\<alpha>. \<alpha> < \<omega>) (\<lambda>\<alpha>. bex (Ops \<alpha> \<mu> (Lambda (predSet \<mu>) Tier) - Ignored) (\<lambda>x'. x = \<alpha> \<triangleright> x')))"
  unfolding tier_limit[OF assms] repfun_union[OF predset_set[OF limit_ord[OF assms]]] 
            un_iff disj_iff[OF ops_ig_setseq] predset_iff[OF limit_ord[OF assms]] rex_def bex_def by auto

(*lemma tier_limit_ops_subset : assumes "Limit \<mu>" 
  shows "\<alpha> < \<omega> \<Longrightarrow> Ops \<alpha> \<mu> (Lambda (predSet \<mu>) (\<lambda>\<beta>. Tier \<beta>)) - Ignored \<subseteq> Tier \<mu>"
proof -
  let ?O = "(\<lambda>a. Ops a \<mu> (Lambda (predSet \<mu>) (\<lambda>\<beta>. Tier \<beta>)) - Ignored)"
  assume "\<alpha> < \<omega>" hence "?O \<alpha> \<subseteq> (\<Union> RepFun ?O (predSet \<omega>))"
    using repfun_union_subset[OF predsetI] subset_refl[OF diff_set[OF ops_set]] by auto
  thus "?O \<alpha> \<subseteq> Tier \<mu>"  unfolding tier_limit[OF assms]
    using subset_trans[OF _ un_subset2[OF union_set[OF repfun_set[OF predset_set[OF \<omega>_ord]]]]] by auto
qed*)

lemma tier_limI1 : assumes "Limit \<mu>" 
  shows "\<beta> < \<mu> \<Longrightarrow> x \<in> Tier \<beta> \<Longrightarrow> x \<in> Tier \<mu>"
  unfolding tier_lim_iff[OF assms] by auto

lemma tier_limI2 : assumes "Limit \<mu>"
  shows "\<alpha> < \<omega> \<Longrightarrow> x \<in> Ops \<alpha> \<mu> (Lambda (predSet \<mu>) Tier) \<Longrightarrow> x \<notin> Ignored \<Longrightarrow> \<alpha> \<triangleright> x \<in> Tier \<mu>"
  unfolding tier_lim_iff[OF assms] by (auto intro: diffI)

lemma tier_limE : assumes "Limit \<mu>" shows "\<lbrakk> x \<in> Tier \<mu> ;
  \<And>\<beta>. \<lbrakk> \<beta> < \<mu> ; x \<in> Tier \<beta> \<rbrakk> \<Longrightarrow> P ;
  \<And>\<alpha> x'. \<lbrakk> \<alpha> < \<omega> ; x = \<alpha> \<triangleright> x' ; x' \<in> Ops \<alpha> \<mu> (Lambda (predSet \<mu>) Tier); x' \<notin> Ignored \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding tier_lim_iff[OF assms] using diffE[OF ops_set] by blast

lemma tier_set : assumes "Ord \<beta>" shows "Set (Tier \<beta>)"
  by (rule ord_cases[OF assms], 
      simp_all add: disj_set un_set union_set[OF repfun_set[OF predset_set]] 
                    tier_0 tier_succ tier_limit)
  
corollary tier0_set : "Set (Tier 0)" by (rule tier_set[OF zero_ord])
corollary tiersucc_set : "Ord \<beta> \<Longrightarrow> Set (Tier (succ \<beta>))" by (rule tier_set[OF succ_ord])
corollary tierlimit_set : "Limit \<mu> \<Longrightarrow> Set (Tier \<mu>)" by (rule tier_set[OF limit_ord])

lemma tier_subset : assumes "Ord \<beta>" shows "Tier \<beta> \<subseteq> Tier (succ \<beta>)"
  using tier_succ[OF \<open>Ord \<beta>\<close>] un_subset1[OF tier_set[OF \<open>Ord \<beta>\<close>]] by auto

lemma tier_limit_union : assumes "Limit \<mu>"
  shows "\<Union> RepFun Tier (predSet \<mu>) \<subseteq> Tier \<mu>"
  unfolding tier_limit[OF assms] 
  using un_subset1[OF union_set[OF repfun_set[OF predset_set[OF limit_ord[OF assms]]]]] 
  by auto

lemma tier_limit_subset : assumes "Limit \<mu>"
  shows "\<beta> < \<mu> \<Longrightarrow> Tier \<beta> \<subseteq> Tier \<mu>" 
  using repfun_union_subset[OF predsetI] subset_refl[OF tier_set[OF lt_ord1]] 
        subset_trans[OF _ tier_limit_union[OF assms]] 
  by auto

lemma tier_increasing' : assumes "Ord \<beta>" shows "\<alpha> < \<beta> \<Longrightarrow> Tier \<alpha> \<subseteq> Tier \<beta>"
proof (induct rule: trans_induct3[OF \<open>Ord \<beta>\<close>])
  case 1
  then show ?case using zero_def by auto
next
  case IH:(2 \<beta>)
  from \<open>\<alpha> \<le> \<beta>\<close> have "\<alpha> < \<beta> | \<alpha> = \<beta>" using le_iff by auto
  thus ?case proof (rule)
    assume "\<alpha> < \<beta>" hence "Tier \<alpha> \<subseteq> Tier \<beta>" using IH(2) by simp 
    thus "Tier \<alpha> \<subseteq> Tier (succ \<beta>)" using subset_trans[OF _ tier_subset[OF \<open>Ord \<beta>\<close>]] by auto
  next
    assume "\<alpha> = \<beta>" thus "Tier \<alpha> \<subseteq> Tier (succ \<beta>)" using tier_subset[OF \<open>Ord \<beta>\<close>] by auto
  qed
next
  case IH:(3 \<mu>)
  from tier_limit_subset[OF IH(1) IH(3)] show ?case by simp
qed

lemma tier_increasing : assumes "\<alpha> < \<beta>" shows "Tier \<alpha> \<subseteq> Tier \<beta>"
  using tier_increasing'[OF lt_ord2[OF assms] assms] by auto

lemma greatest_tier : assumes "Ord \<alpha>" "Ord \<beta>" 
  shows "\<lbrakk> x \<in> Tier \<alpha> ; y \<in> Tier \<beta> \<rbrakk> \<Longrightarrow> (\<exists>\<gamma>. x \<in> Tier \<gamma> \<and> y \<in> Tier \<gamma>)"
proof -
  assume xy: "x \<in> Tier \<alpha>" "y \<in> Tier \<beta>"
  show "(\<exists>\<gamma>. x \<in> Tier \<gamma> \<and> y \<in> Tier \<gamma>)" 
  proof (rule Ord_linear_lt[OF assms], rule_tac [1] exI, rule_tac [2] exI, rule_tac [3] exI)
    assume "\<alpha> < \<beta>" thus "x \<in> Tier \<beta> \<and> y \<in> Tier \<beta>" 
      using subsetD[OF tier_increasing] xy by auto
  next
    assume "\<alpha> = \<beta>" thus "x \<in> Tier \<beta> \<and> y \<in> Tier \<beta>" using xy by simp
  next
    assume "\<beta> < \<alpha>" thus "x \<in> Tier \<alpha> \<and> y \<in> Tier \<alpha>" 
      using subsetD[OF tier_increasing] xy by auto
  qed
qed


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
  shows "x \<in> Part \<alpha> (Tier \<mu>) \<longleftrightarrow> (rex (\<lambda>\<beta>. \<beta> < \<mu>) (\<lambda>\<beta>. x \<in> Part \<alpha> (Tier \<beta>))) 
             \<or> (\<alpha> < \<omega> \<and> bex (Ops \<alpha> \<mu> (Lambda (predSet \<mu>) Tier) - Ignored) (\<lambda>x'. x = \<alpha> \<triangleright> x')) "
proof
  assume "x \<in> Part \<alpha> (Tier \<mu>)"
  then obtain x' where "x \<in> Tier \<mu>" "x = \<alpha> \<triangleright> x'" using partE[OF tierlimit_set[OF assms]] by auto
  show "(rex (\<lambda>\<beta>. \<beta> < \<mu>) (\<lambda>\<beta>. x \<in> Part \<alpha> (Tier \<beta>))) \<or>
         (\<alpha> < \<omega> \<and> bex (Ops \<alpha> \<mu> (Lambda (predSet \<mu>) Tier) - Ignored) (\<lambda>x'. x = \<alpha> \<triangleright> x'))"
  proof (rule tier_limE[OF assms(1) \<open>x \<in> Tier \<mu>\<close>], rule disjI1)
    fix \<beta> assume "\<beta> < \<mu>" "x \<in> Tier \<beta>"
    thus "(rex (\<lambda>\<beta>. \<beta> < \<mu>) (\<lambda>\<beta>. x \<in> Part \<alpha> (Tier \<beta>)))" using partI[OF \<open>x = \<alpha> \<triangleright> x'\<close>] by auto
  next
    fix \<alpha>' x'' assume "\<alpha>' < \<omega>" "x = \<alpha>' \<triangleright> x''" "x'' \<in> Ops \<alpha>' \<mu> (Lambda (predSet \<mu>) Tier)" "x'' \<notin> Ignored"
    moreover hence "\<alpha> = \<alpha>'" "x' = x''" using \<open>x = \<alpha> \<triangleright> x'\<close> by (auto elim: pair_inject) 
    ultimately have "\<alpha> < \<omega> \<and> bex (Ops \<alpha> \<mu> (Lambda (predSet \<mu>) Tier) - Ignored) (\<lambda>x'. x = \<alpha> \<triangleright> x')"
      using diffI by auto
    thus "(rex (\<lambda>\<beta>. \<beta> < \<mu>) (\<lambda>\<beta>. x \<in> Part \<alpha> (Tier \<beta>))) \<or>
          (\<alpha> < \<omega> \<and> bex (Ops \<alpha> \<mu> (Lambda (predSet \<mu>) Tier) - Ignored) (\<lambda>x'. x = \<alpha> \<triangleright> x'))" by simp
  qed
next
  assume "(rex (\<lambda>\<beta>. \<beta> < \<mu>) (\<lambda>\<beta>. x \<in> Part \<alpha> (Tier \<beta>))) \<or>
        (\<alpha> < \<omega> \<and> bex (Ops \<alpha> \<mu> (Lambda (predSet \<mu>) Tier) - Ignored) (\<lambda>x'. x = \<alpha> \<triangleright> x'))"
  thus "x \<in> Part \<alpha> (Tier \<mu>)" proof
    assume "rex (\<lambda>\<beta>. \<beta> < \<mu>) (\<lambda>\<beta>. x \<in> Part \<alpha> (Tier \<beta>))"
    then obtain \<beta> where "\<beta> < \<mu>" "x \<in> Part \<alpha> (Tier \<beta>)" by auto 
    then obtain x' where "x \<in> Tier \<beta>" "x = \<alpha> \<triangleright> x'" using partE[OF tier_set[OF lt_ord1]] by blast
    thus "x \<in> Part \<alpha> (Tier \<mu>)" using tier_limI1[OF assms \<open>\<beta> < \<mu>\<close>] partI by auto
  next
    assume "\<alpha> < \<omega> \<and> bex (Ops \<alpha> \<mu> (Lambda (predSet \<mu>) Tier) - Ignored) (\<lambda>x'. x = \<alpha> \<triangleright> x')"
    then obtain x' where "x = \<alpha> \<triangleright> x'" "\<alpha> < \<omega>" "x' \<in> Ops \<alpha> \<mu> (Lambda (predSet \<mu>) Tier)" "x' \<notin> Ignored"
      using diff_iff[OF ops_set] by auto
    thus "x \<in> Part \<alpha> (Tier \<mu>)" using partI tier_limI2[OF assms] by auto
  qed
qed

lemma part_tierlimI : assumes "Limit \<mu>" 
  shows "\<lbrakk> \<alpha> < \<omega> ; x' \<in> Ops \<alpha> \<mu> (Lambda (predSet \<mu>) Tier); x' \<notin> Ignored; x = \<alpha> \<triangleright> x'\<rbrakk>  
          \<Longrightarrow> x \<in> Part \<alpha> (Tier \<mu>) "
  using part_tierlim_iff[OF assms] diffI by auto

lemma part_tierlimE : assumes "Limit \<mu>" 
  shows "\<lbrakk> x \<in> Part \<alpha> (Tier \<mu>) ; 
    \<And>\<beta>. \<lbrakk> \<beta> < \<mu>; x \<in> Part \<alpha> (Tier \<beta>) \<rbrakk> \<Longrightarrow> P ;
    \<And>x'. \<lbrakk> x = \<alpha> \<triangleright> x'; x' \<in> Ops \<alpha> \<mu> (Lambda (predSet \<mu>) Tier); x' \<notin> Ignored \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using part_tierlim_iff[OF assms] diff_iff[OF ops_set] by auto

lemma tier_tagged : assumes "Ord \<beta>" 
  shows "x \<in> Tier \<beta> \<Longrightarrow> (\<exists>\<alpha> x'. \<alpha> < \<omega> \<and> x = \<alpha> \<triangleright> x')" 
proof (induct rule: trans_induct3[OF assms])
  case 1
  then show ?case using tier0_iff unfolding bex_def rex_def by auto
next
  case IH:(2 \<beta>)
  show ?case by (rule tier_succE[OF IH(1,3)], use IH(2) in auto)
next
  case IH:(3 \<mu>)
  show ?case by (rule tier_limE[OF IH(1,3)], use IH(2) in auto)
qed

lemma part_succ_subset : assumes "Ord \<beta>" 
  shows "Part \<alpha> (Tier \<beta>) \<subseteq> Part \<alpha> (Tier (succ \<beta>))"
  by (rule part_subset[OF tier_subset[OF assms]])
  

subsection \<open>Structure of the 'set' part of Tier\<close>

thm ops_set_0_ax
lemma ops_set_succ : "Ord \<beta> \<Longrightarrow> Ops set (succ \<beta>) x = Pow x" using ops_set_succ_ax by simp
lemma ops_set_lim : "Limit \<mu> \<Longrightarrow> Ops set \<mu> f = \<emptyset>" using ops_set_lim_ax by simp

lemma set_limit_iff : assumes "Limit \<mu>" 
  shows "x \<in> Part set (Tier \<mu>) \<longleftrightarrow> rex (\<lambda>\<beta>. \<beta> < \<mu>) (\<lambda>\<beta>. x \<in> Part set (Tier \<beta>))"
  unfolding part_tierlim_iff[OF assms] using ops_set_lim[OF assms] emp diff_iff[OF emp_set] by auto

lemma set_limI : assumes "Limit \<mu>" 
  shows "\<lbrakk> \<beta> < \<mu> ; x \<in> Part set (Tier \<beta>) \<rbrakk> \<Longrightarrow> x \<in> Part set (Tier \<mu>)"
  using set_limit_iff[OF assms] by auto

lemma set_limE : assumes "Limit \<mu>" 
  shows "\<lbrakk> x \<in> Part set (Tier \<mu>) ; \<And>\<beta> x'. \<lbrakk> \<beta> < \<mu> ; x \<in> Tier \<beta> ; x = set \<triangleright> x' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using set_limit_iff[OF assms] part_iff[OF tier_set] lt_ord1 limit_ord[OF assms] by auto

lemma set_0 : "Part set (Tier 0) = \<emptyset>"
  by (rule equals0I[OF part_set[OF tier0_set]], unfold part_tier0_iff ops_set_0_ax, auto)

lemma set_succ_iff : assumes "Ord \<beta>" shows
  "x \<in> Part set (Tier (succ \<beta>)) \<longleftrightarrow> (\<exists>x'. x' \<subseteq> (Tier \<beta> - Ignored) \<and> x = set \<triangleright> x')"
proof (induct rule: trans_induct3[OF assms])
  case 1
  then show ?case proof (rule)
    assume "x \<in> Part set (Tier (succ 0))"
    thus "\<exists>x'. x' \<subseteq> Tier 0 - Ignored \<and> x = set \<triangleright> x'"
    proof (rule part_tiersuccE[OF zero_ord])
      from set_0 show "x \<in> Part set (Tier 0) \<Longrightarrow> \<exists>x'. x' \<subseteq> Tier 0 - Ignored \<and> x = set \<triangleright> x'" by auto
    next
      fix x' assume "x' \<in> Ops set (succ 0) (Tier 0 - Ignored)" "x = set \<triangleright> x'"
      hence "x' \<in> Pow (Tier 0 - Ignored)" using ops_set_succ assms by simp
      hence "x' \<subseteq> Tier 0 - Ignored" using powD[OF diff_set[OF tier0_set]] by simp
      thus "\<exists>x'. x' \<subseteq> Tier 0 - Ignored \<and> x = set \<triangleright> x'" using \<open>x = set \<triangleright> x'\<close> by auto
    qed
  next
    assume "\<exists>x'. x' \<subseteq> Tier 0 - Ignored \<and> x = set \<triangleright> x'"
    thus "x \<in> Part set (Tier (succ 0))" 
      using part_tiersuccI1[OF zero_ord set_tag]
            ops_set_succ powI by auto
  qed
next
  case IH:(2 \<beta>)
  show ?case proof (rule)
    assume "x \<in> Part set (Tier (succ (succ \<beta>)))"
    thus "\<exists>x'. x' \<subseteq> Tier (succ \<beta>) - Ignored \<and> x = set \<triangleright> x'"
    proof (rule part_tiersuccE[OF succ_ord[OF \<open>Ord \<beta>\<close>]])
      assume "x \<in> Part set (Tier (succ \<beta>))"
      then obtain x' where "x' \<subseteq> Tier \<beta> - Ignored" "x = set \<triangleright> x'" using IH(2) by auto
      moreover hence "x' \<subseteq> Tier (succ \<beta>) - Ignored" using diff_subset1[OF tier_subset[OF IH(1)]] by simp
      ultimately show "\<exists>x'. x' \<subseteq> Tier (succ \<beta>) - Ignored \<and> x = set \<triangleright> x'" by auto
    next
      fix x' assume "x' \<in> Ops set (succ (succ \<beta>)) (Tier (succ \<beta>) - Ignored)" "x = set \<triangleright> x'"
      thus "\<exists>x'. x' \<subseteq> Tier (succ \<beta>) - Ignored \<and> x = set \<triangleright> x'" 
        using ops_set_succ[OF succ_ord[OF IH(1)]] 
              powD[OF diff_set[OF tiersucc_set[OF IH(1)]]] by auto
    qed
  next
    assume "\<exists>x'. x' \<subseteq> Tier (succ \<beta>) - Ignored \<and> x = set \<triangleright> x'"
    then obtain x' where "x' \<subseteq> Tier (succ \<beta>) - Ignored" "x = set \<triangleright> x'" by auto
    thus "x \<in> Part set (Tier (succ (succ \<beta>)))" 
      using part_tiersuccI1[OF succ_ord[OF \<open>Ord \<beta>\<close>] set_tag]
            ops_set_succ succ_ord[OF \<open>Ord \<beta>\<close>] powI by auto
  qed
next
  case IH:(3 \<mu>)
  show ?case proof
    assume "x \<in> Part set (Tier (succ \<mu>))"
    thus "\<exists>x'. x' \<subseteq> Tier \<mu> - Ignored \<and> x = set \<triangleright> x'"
    proof (rule part_tiersuccE[OF limit_ord[OF IH(1)]])
      assume "x \<in> Part set (Tier \<mu>)"
      then obtain \<beta> x' where "\<beta> < \<mu>" "x \<in> Tier \<beta>" "x = set \<triangleright> x'" using set_limE[OF IH(1)] by auto
      hence "x \<in> Part set (Tier (succ \<beta>))" using tier_subset[OF lt_ord1[OF \<open>\<beta> < \<mu>\<close>]] subsetD partI by auto
      hence "x' \<subseteq> Tier \<beta> - Ignored" using IH(2)[OF \<open>\<beta> < \<mu>\<close>] \<open>x = set \<triangleright> x'\<close> by (auto elim: pair_inject)
      hence "x' \<subseteq> Tier \<mu> - Ignored" using diff_subset1[OF tier_limit_subset[OF IH(1) \<open>\<beta> < \<mu>\<close>]] by simp
      thus "\<exists>x'. x' \<subseteq> Tier \<mu> - Ignored \<and> x = set \<triangleright> x'" using \<open>x = set \<triangleright> x'\<close> by auto
    next
      fix x' assume "x' \<in> Ops set (succ \<mu>) (Tier \<mu> - Ignored)" "x = set \<triangleright> x'"
      hence "x' \<in> Pow (Tier \<mu> - Ignored)" unfolding ops_set_succ[OF limit_ord[OF IH(1)]] by simp
      thus "\<exists>x'. x' \<subseteq> Tier \<mu> - Ignored \<and> x = set \<triangleright> x'" using \<open>x = set \<triangleright> x'\<close> powD[OF diff_set[OF tierlimit_set[OF IH(1)]]] by auto
    qed
  next
    assume "\<exists>x'. x' \<subseteq> Tier \<mu> - Ignored \<and> x = set \<triangleright> x'"
    then obtain x' where "x' \<subseteq> Tier \<mu> - Ignored" "x = set \<triangleright> x'" by blast
    hence "x' \<in> Pow (Tier \<mu> - Ignored)" using powI by simp
    hence "x' \<in> Ops set (succ \<mu>) (Tier \<mu> - Ignored)" unfolding ops_set_succ[OF limit_ord[OF IH(1)]] by simp
    thus "x \<in> Part set (Tier (succ \<mu>))" using part_tiersucc_iff[OF limit_ord[OF IH(1)]] \<open>x = set \<triangleright> x'\<close> set_tag by auto 
  qed
qed

lemma set_succ_iff' : assumes "Ord \<beta>"
  shows "set \<triangleright> x' \<in> Tier (succ \<beta>) \<longleftrightarrow> x' \<subseteq> (Tier \<beta> - Ignored)"
proof
  let ?x = "set \<triangleright> x'"
  assume "?x \<in> Tier (succ \<beta>)" hence "?x \<in> Part set (Tier (succ \<beta>))" using partI by auto
  thus "x' \<subseteq> (Tier \<beta> - Ignored)" using set_succ_iff[OF assms] by (auto elim: pair_inject)
next
  assume "x' \<subseteq> (Tier \<beta> - Ignored)" thus "set \<triangleright> x' \<in> Tier (succ \<beta>)" 
    using set_succ_iff[OF assms] partD2[OF tiersucc_set[OF assms]] by (blast elim: pair_inject)
qed

lemma set_succI : assumes "Ord \<beta>"
  shows "\<lbrakk> x = set \<triangleright> x' ; x' \<subseteq> Tier \<beta> - Ignored\<rbrakk> \<Longrightarrow> x \<in> Part set (Tier (succ \<beta>))"
  using set_succ_iff[OF assms] by auto

lemma set_succI' : assumes "Ord \<beta>" 
  shows "x' \<subseteq> Tier \<beta> - Ignored \<Longrightarrow> set \<triangleright> x' \<in> Tier (succ \<beta>)"
  using set_succ_iff'[OF assms] by simp

lemma set_succE : assumes "Ord \<beta>"
  shows "\<lbrakk> x \<in> Part set (Tier (succ \<beta>)) ; 
    \<And>x'. \<lbrakk> x = set \<triangleright> x'; x' \<subseteq> Tier \<beta> - Ignored \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using set_succ_iff[OF assms] by auto

lemma set_succE2 : assumes "Ord \<beta>"
  shows "\<lbrakk> x \<in> Part set (Tier (succ \<beta>)) ; 
    \<And>x'. \<lbrakk> x = set \<triangleright> x'; x' \<subseteq> Tier \<beta> \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using set_succ_iff[OF assms] diff_subset2[OF tier_set[OF assms]] by auto

lemma set_succD_ig : assumes "Ord \<beta>"
  shows "set \<triangleright> x' \<in> Tier (succ \<beta>) \<Longrightarrow> x' \<subseteq> Tier \<beta> - Ignored"
  using set_succ_iff'[OF assms] by simp

lemma set_succD : assumes "Ord \<beta>"
  shows "set \<triangleright> x' \<in> Tier (succ \<beta>) \<Longrightarrow> x' \<subseteq> Tier \<beta>"
  using set_succ_iff'[OF assms] diff_subset2[OF tier_set[OF assms]] by simp

subsection \<open>Structure of the 'ord' part of Tier\<close>

thm ops_ord_ax
lemma ops_ord : "Ord \<beta> \<Longrightarrow> Ops ord \<beta> x = sng \<beta>" using ops_ord_ax by simp

lemma ord_0 : "Part ord (Tier 0) = sng (ord \<triangleright> 0)"
  by (rule equality_iffI[OF part_set[OF tier0_set] sng_set], 
      use part_tier0_iff ord_tag ops_ord[OF zero_ord] sng_iff in auto)
lemma ord_succ_iff : assumes "Ord \<beta>" 
  shows "b \<in> Part ord (Tier (succ \<beta>)) \<longleftrightarrow> b \<in> Part ord (Tier \<beta>) \<or> b = ord \<triangleright> (succ \<beta>)"
  using part_tiersucc_iff[OF assms, where ?\<alpha> = ord] sng_iff ord_tag unfolding ops_ord[OF succ_ord[OF \<open>Ord \<beta>\<close>]] by auto
lemma ord_lim_iff : assumes "Limit \<mu>"
  shows "b \<in> Part ord (Tier \<mu>) \<longleftrightarrow> (rex (\<lambda>\<beta>. \<beta> < \<mu>) (\<lambda>\<beta>. b \<in> Part ord (Tier \<beta>)) \<or> b = ord \<triangleright> \<mu>)"
  using part_tierlim_iff[OF assms, where ?\<alpha> = ord] ord_tag no_ord_ignored unfolding ops_ord[OF limit_ord[OF assms]] sorry


definition inModel :: "'d \<Rightarrow> bool" (\<open>M\<close>) where
  "inModel x \<equiv> rex Ord (\<lambda>\<beta>. x \<in> Tier \<beta>)"

lemma mI [intro] : "\<lbrakk> Ord \<beta> ; x \<in> Tier \<beta> \<rbrakk> \<Longrightarrow> M x" 
  unfolding inModel_def by (rule rexI)

lemma mI' : "\<lbrakk> Ord \<beta>; x' \<subseteq> Tier \<beta> - Ignored \<rbrakk> \<Longrightarrow> M (set \<triangleright> x')"
  using set_succI' mI[OF succ_ord] by auto

lemma mE [elim]: "\<lbrakk> M x ; \<And>\<beta>. \<lbrakk> Ord \<beta> ; x \<in> Tier \<beta> \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding inModel_def by auto


lemma minduct3: assumes "M x" "x \<in> Tier 0 \<Longrightarrow> P" 
    "(\<And>\<beta>. Ord \<beta> \<Longrightarrow> (x \<in> Tier \<beta> \<Longrightarrow> P) \<Longrightarrow> x \<in> Tier (succ \<beta>) \<Longrightarrow> P)"
    "(\<And>\<mu>. Limit \<mu> \<Longrightarrow> (\<And>\<beta>. \<beta> < \<mu> \<Longrightarrow> x \<in> Tier \<beta> \<Longrightarrow> P) \<Longrightarrow> x \<in> Tier \<mu> \<Longrightarrow> P)" 
    shows "P"
proof -
  from assms(1) obtain \<beta> where "Ord \<beta>" "x \<in> Tier \<beta>" by auto
  thus ?thesis by (induct rule: trans_induct3, use assms(2,3,4) in auto)
qed

lemma m_tag : assumes "M x" shows "TagOf x = \<alpha> \<longleftrightarrow> (\<exists>x'. x = \<alpha> \<triangleright> x')"
proof (rule mE[OF assms])
  fix \<beta> assume"Ord \<beta>" "x \<in> Tier \<beta>"
  show "TagOf x = \<alpha> \<longleftrightarrow> (\<exists>x'. x = \<alpha> \<triangleright> x')"
  proof
    assume "TagOf x = \<alpha>" then obtain \<alpha>' x' where "x = \<alpha>' \<triangleright> x'" 
      using tier_tagged[OF \<open>Ord \<beta>\<close> \<open>x \<in> Tier \<beta>\<close>] by auto
    thus "\<exists>x'. x = \<alpha> \<triangleright> x'" using \<open>TagOf x = \<alpha>\<close> fst_eq by auto
  next
    assume "\<exists>x'. x = \<alpha> \<triangleright> x'" thus "TagOf x = \<alpha>" using fst_eq by auto
  qed
qed

lemma m_part : assumes "M x" shows "TagOf x = \<alpha> \<longleftrightarrow> (rex Ord (\<lambda>\<beta>. x \<in> Part \<alpha> (Tier \<beta>)))"
proof 
  assume "TagOf x = \<alpha>" 
  then obtain \<beta> x' where "Ord \<beta>" "x \<in> Tier \<beta>" "x = \<alpha> \<triangleright> x'" using assms m_tag mE by blast
  thus "rex Ord (\<lambda>\<beta>. x \<in> Part \<alpha> (Tier \<beta>))" using partI by blast
next
  assume "rex Ord (\<lambda>\<beta>. x \<in> Part \<alpha> (Tier \<beta>))" 
  then obtain \<beta> where "Ord \<beta>" "x \<in> Part \<alpha> (Tier \<beta>)" by auto
  thus "TagOf x = \<alpha>" using partD1[OF tier_set] by auto
qed

lemma m_part_succ : assumes "M x" shows "TagOf x = \<alpha> \<longleftrightarrow> (rex Ord (\<lambda>\<beta>. x \<in> Part \<alpha> (Tier (succ \<beta>))))"
  unfolding m_part[OF assms]
proof (auto)
  assume "rex Ord (\<lambda>\<beta>. x \<in> Part \<alpha> (Tier \<beta>))"
  then obtain \<beta> where "Ord \<beta>" "x \<in> Part \<alpha> (Tier \<beta>)" by auto
  hence "x \<in> Part \<alpha> (Tier (succ \<beta>))" using part_succ_subset by auto
  thus "rex Ord (\<lambda>\<beta>. x \<in> Part \<alpha> (Tier (succ \<beta>)))" using succ_ord[OF \<open>Ord \<beta>\<close>] by auto
qed


definition mall :: "('d \<Rightarrow> bool) \<Rightarrow> bool" (binder \<open>m\<forall>\<close> 10) where
  "mall P \<equiv> rall M P"

lemma mallI [intro]: "(\<And>x. M x \<Longrightarrow> P x) \<Longrightarrow> m\<forall>x. P x"
  unfolding mall_def by auto

lemma mspec : "\<lbrakk> m\<forall>x. P x ; M x \<rbrakk> \<Longrightarrow> P x"
  unfolding mall_def by auto

lemma mallE [elim] : "\<lbrakk> m\<forall>x. P x ; P x \<Longrightarrow> Q ; \<not> M x \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  unfolding mall_def by auto


definition mex (binder \<open>m\<exists>\<close> 10) 
  where "mex P \<equiv> rex inModel P" 

lemma mexI [intro]: "P x \<Longrightarrow> M x \<Longrightarrow> m\<exists>x. P x"
  unfolding mex_def by auto

lemma mexE [elim]: "\<lbrakk> m\<exists>x. P x ; \<And>x. \<lbrakk> M x ; P x \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  unfolding mex_def by auto

definition muniq (binder \<open>m\<exists>\<^sub>\<le>\<^sub>1\<close> 10) 
  where "muniq P \<equiv> mall (\<lambda>y. mall (\<lambda>z. P y \<and> P z \<longrightarrow> y = z))"

definition mrall (binder \<open>mr\<forall>\<close> 10) 
  where "mrall P Q \<equiv> mall (\<lambda>x. P x \<longrightarrow> Q x)"

definition mrex (binder \<open>mr\<exists>\<close> 10)
  where "mrex P Q \<equiv> mex (\<lambda>x. P x \<and> Q x)" 

definition fun_mall 
  where "fun_mall P \<equiv> (\<forall>F. (\<forall>x. M x \<longrightarrow> M (F x)) \<longrightarrow> P F)"

definition binfun_mall 
  where "binfun_mall P \<equiv> (\<forall>F. (\<forall>x y. M x \<and> M y \<longrightarrow> M (F x y)) \<longrightarrow> P F)"

(*Model versions of GZF constants
  Higher-order parameters of model operators MUST be restricted to the model,
  otherwise it is painful to prove transfer rules.*)

definition "mSet x \<equiv> TagOf x = set"
lemma tag_mset [simp]: "mSet (set \<triangleright> x')" unfolding mSet_def fst_eq by simp

lemma mset_eq : assumes "M x" shows "mSet x \<longleftrightarrow> (\<exists>x'. x = set \<triangleright> x')"
  unfolding mSet_def by (rule m_tag[OF assms])

lemma mset_part_tier : assumes "M x" 
  shows "mSet x \<longleftrightarrow> (rex Ord (\<lambda>\<beta>. x \<in> Part set (Tier \<beta>)))"
  unfolding mSet_def using m_part[OF assms] by auto

lemma mset_part_tier_succ : assumes "M x"
  shows "mSet x \<longleftrightarrow> (rex Ord (\<lambda>\<beta>. x \<in> Part set (Tier (succ \<beta>))))"
  unfolding mSet_def using m_part_succ[OF assms] by auto

lemma msetI : assumes "M x" "Ord \<beta>" shows "x \<in> Part set (Tier \<beta>) \<Longrightarrow> mSet x"
   unfolding mset_part_tier[OF assms(1)] by (insert assms(2), auto)

lemma msetI' : "x = set \<triangleright> x' \<Longrightarrow> mSet x" unfolding mSet_def by simp

lemma mset_partE1 : assumes "M x" 
  shows "\<lbrakk> mSet x ; \<And>\<beta>. \<lbrakk> Ord \<beta>; x \<in> Part set (Tier \<beta>)\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using mset_part_tier[OF assms] by auto

lemma msetE1 : assumes "M x" 
  shows "\<lbrakk> mSet x ; \<And>\<beta>. \<lbrakk> Ord \<beta>; x \<in> Tier \<beta> \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using mset_part_tier[OF assms] partD2[OF tier_set] by auto

lemma mset_part_succE1 : assumes "M x" 
  shows "\<lbrakk> mSet x ; \<And>\<beta>. \<lbrakk> Ord \<beta>; x \<in> Part set (Tier (succ \<beta>))\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using mset_part_tier_succ[OF assms] by auto

lemma mset_succE1 : assumes "M x" 
  shows "\<lbrakk> mSet x ; \<And>\<beta>. \<lbrakk> Ord \<beta>; x \<in> Tier (succ \<beta>)\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using mset_part_tier_succ[OF assms] partD2[OF tier_set] by auto

lemma msetE2_ig : assumes "M x" "x = set \<triangleright> x'" 
  "\<And>\<beta>. \<lbrakk> Ord \<beta>; x \<in> Tier (succ \<beta>); x' \<subseteq> Tier \<beta> - Ignored \<rbrakk> \<Longrightarrow> P"
shows "P"
proof -
  from assms(1,2) have "mSet x" by simp
  then obtain \<beta> where "Ord \<beta>" "x \<in> Tier (succ \<beta>)" using mset_succE1[OF assms(1)] by auto
  moreover hence "x' \<subseteq> Tier \<beta> - Ignored" using set_succD_ig assms(2) by auto
  ultimately show "P" using assms(3) by simp
qed

lemma msetE2 : assumes "M x" "x = set \<triangleright> x'" 
  "\<And>\<beta>. \<lbrakk> Ord \<beta>; x \<in> Tier (succ \<beta>); x' \<subseteq> Tier \<beta> \<rbrakk> \<Longrightarrow> P"
shows "P"
proof -
  from assms(1,2) have "mSet x" by simp
  then obtain \<beta> where "Ord \<beta>" "x \<in> Tier (succ \<beta>)" using mset_succE1[OF assms(1)] by auto
  moreover hence "x' \<subseteq> Tier \<beta>" using assms(2) set_succD by auto
  ultimately show "P" using assms(3) by simp
qed

lemma msetE3_ig: assumes "M x" shows "\<lbrakk> mSet x; 
    \<And>\<beta> x'. \<lbrakk> Ord \<beta>; x \<in> Tier (succ \<beta>) ; x = set \<triangleright> x' ; x' \<subseteq> Tier \<beta> - Ignored \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
proof -
  assume "mSet x" and H:"(\<And>\<beta> x'. Ord \<beta> \<Longrightarrow> x \<in> Tier (succ \<beta>) \<Longrightarrow> x = set \<triangleright> x' \<Longrightarrow> x' \<subseteq> Tier \<beta> - Ignored \<Longrightarrow> P)"
  from \<open>mSet x\<close> obtain \<beta> where "Ord \<beta>" "x \<in> Part set (Tier (succ \<beta>))" using mset_part_tier_succ[OF assms] by auto
  then obtain x' where "x \<in> Tier (succ \<beta>)" "x = set \<triangleright> x'" "x' \<subseteq> Tier \<beta> - Ignored" 
    using set_succ_iff partD2[OF tiersucc_set] by blast
  thus "P" using H[OF \<open>Ord \<beta>\<close>] by auto
qed

lemma msetE3: assumes "M x" shows "\<lbrakk> mSet x; 
    \<And>\<beta> x'. \<lbrakk> Ord \<beta>; x \<in> Tier (succ \<beta>) ; x = set \<triangleright> x' ; x' \<subseteq> Tier \<beta> \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using  diff_subset2[OF tier_set] by (auto elim: msetE3_ig[OF assms])

lemma msetE4 : assumes "M x" shows "\<lbrakk> mSet x; 
    \<And>x'. \<lbrakk> x = set \<triangleright> x'\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using msetE3[OF assms] by auto

lemma mset_obj_set' : assumes "M x" shows "x = set \<triangleright> x' \<Longrightarrow> Set x'"
  using subset_set1 by (auto elim: msetE2[OF assms] pair_inject) 

lemma mset_obj_set : assumes "M x" shows "mSet x \<Longrightarrow> Set (ObjOf x)"
  by (rule msetE4[OF assms], use mset_obj_set'[OF assms] in auto)

definition "mMem x y \<equiv> mSet y \<and> (x \<in> (ObjOf y))" 

lemma mMem_iff : assumes "mSet x" shows "mMem a x \<longleftrightarrow> a \<in> ObjOf x"
  unfolding mMem_def using assms by auto

lemma mMemI : assumes "mSet x" shows "a \<in> ObjOf x \<Longrightarrow> mMem a x"
  using mMem_iff[OF assms] by auto

lemma mMemI' : assumes "x = set \<triangleright> x'" shows "a \<in> x' \<Longrightarrow> mMem a x"
  unfolding mMem_def using snd_eq assms by auto

lemma mMemI'' : shows "a \<in> x' \<Longrightarrow> mMem a (set \<triangleright> x')"
  using mMemI' by auto

lemma mMem_mset : "mMem a x \<Longrightarrow> mSet x"
  unfolding mMem_def by simp

lemma mMemD : "mMem a x \<Longrightarrow> a \<in> ObjOf x"
  unfolding mMem_def by auto

lemma mMemD' : assumes "x = set \<triangleright> x'" shows "mMem a x \<Longrightarrow> a \<in> x'"
  unfolding mMem_def using snd_eq assms by auto

lemma mMemE : assumes "M x" "mMem a x" "\<And>x'. \<lbrakk> x = set \<triangleright> x'; a \<in> x' \<rbrakk> \<Longrightarrow> P" shows "P"
  unfolding mMem_def
proof -
  from \<open>mMem a x\<close> have "mSet x" "a \<in> ObjOf x" unfolding mMem_def by simp_all
  then obtain x' where "x = set \<triangleright> x'" using msetE4[OF \<open>M x\<close>] by auto
  moreover hence "a \<in> x'" using \<open>a \<in> ObjOf x\<close> snd_eq by auto
  ultimately show "P" using assms(3) by auto
qed

lemma mMem_m : assumes "M x" shows "mMem a x \<Longrightarrow> M a"
proof -
  assume "mMem a x" hence "mSet x" using mMem_mset by simp
  then obtain \<beta> x' where "Ord \<beta>" "x = set \<triangleright> x'" "x' \<subseteq> Tier \<beta>" by (blast elim: msetE3[OF assms])
  hence "a \<in> Tier \<beta>" using mMemD'[OF _ \<open>mMem a x\<close>] by auto
  hence "\<exists>\<beta>. Ord \<beta> \<and> a \<in> Tier \<beta>" using \<open>Ord \<beta>\<close> by auto
  thus "M a" by auto
qed

lemma mem_m : assumes "M x" "x = set \<triangleright> x'" shows "a \<in> x' \<Longrightarrow> M a"
  by (rule mMem_m[OF assms(1) mMemI'[OF assms(2)]])

lemma mMem_tier : assumes "Ord \<beta>" shows "\<lbrakk> x \<in> Tier (succ \<beta>); mMem a x \<rbrakk> \<Longrightarrow> a \<in> Tier \<beta>"
proof -
  assume "x \<in> Tier (succ \<beta>)" hence "M x" using assms by auto
  assume "mMem a x" then obtain x' where "x = set \<triangleright> x'" "a \<in> x'" using mMemE[OF \<open>M x\<close>] by auto
  thus "a \<in> Tier \<beta>" unfolding mMem_def mSet_def 
    using set_succD[OF assms] \<open>x \<in> Tier (succ \<beta>)\<close> by auto
qed

definition forceM where "forceM x \<equiv> if M x then x else set \<triangleright> \<emptyset>"
definition "mEmp \<equiv> set \<triangleright> \<emptyset>"

lemma memp_mset : "mSet (mEmp)" unfolding mSet_def mEmp_def fst_eq by simp
lemma memp_m : "M (mEmp)" unfolding mEmp_def 
  using mI'[OF zero_ord] empty_subsetI[OF diff_set[OF tier_set[OF zero_ord]]] by auto

lemma forceM_m [simp] : "M (forceM x)"
  using forceM_def memp_m unfolding mEmp_def by auto

lemma forceM_eq : "M x \<Longrightarrow> forceM x = x"
  unfolding forceM_def by auto

text \<open>(EMP) : Axiom of Empty Set\<close>
theorem "m\<forall>a. \<not> (mMem a mEmp)"
proof (rule, rule ccontr, simp)
  fix a assume "mMem a mEmp"
  hence "a \<in> \<emptyset>" unfolding mEmp_def using mMemD snd_eq by blast
  thus "False" using not_mem_empty by simp
qed

text \<open>(SET): Set Ownership Axiom\<close>
theorem "m\<forall>x. mSet x \<longleftrightarrow> (x = mEmp \<or> (m\<exists>y. mMem y x))"
proof (rule, rule)
  fix x assume "M x" "mSet x" 
  then obtain \<beta> x' where "Ord \<beta>" "x \<in> Tier (succ \<beta>)" "x = set \<triangleright> x'" "x' \<subseteq> Tier \<beta>" by (rule msetE3)
  hence "x' = \<emptyset> \<or> (\<exists>y. y \<in> x')" using setE[OF subset_set1] by blast
  thus "x = mEmp \<or> (m\<exists>y. mMem y x)"
  proof (rule)
    assume "x' = \<emptyset>" hence "x = mEmp" unfolding mEmp_def \<open>x = set \<triangleright> x'\<close> by auto
    thus "x = mEmp \<or> (m\<exists>y. mMem y x)" by rule
  next
    assume "\<exists>y. y \<in> x'" then obtain y where "y \<in> x'" by auto
    hence "M y" "mMem y x" using mMemI'[OF \<open>x = set \<triangleright> x'\<close>] mI[OF \<open>Ord \<beta>\<close>] subsetD[OF \<open>x' \<subseteq> Tier \<beta>\<close>] by auto
    hence "m\<exists>y. mMem y x" by auto
    thus "x = mEmp \<or> (m\<exists>y. mMem y x)" by rule
  qed
next
  fix x assume "M x" "x = mEmp \<or> (m\<exists>y. mMem y x)"
  thus "mSet x" unfolding mEmp_def mMem_def by auto
qed

text \<open>(EXT): Axiom of Extensionality\<close>
theorem "m\<forall>x y. mSet x \<longrightarrow> mSet y \<longrightarrow> (m\<forall>a. mMem a x \<longleftrightarrow> mMem a y) \<longrightarrow> x = y"
proof (rule, rule, rule, rule, rule)
  fix x y assume "M x" "M y" "mSet x" "mSet y" and iff:"m\<forall>a. mMem a x \<longleftrightarrow> mMem a y"
  then obtain x' y' where [simp] : "x = set \<triangleright> x'" "y = set \<triangleright> y'" by (blast elim: msetE4)
  hence "Set x'" "Set y'" using mset_obj_set' \<open>M x\<close> \<open>M y\<close> by auto
  hence "x' = y'" proof (rule equality_iffI)
    fix a show "a \<in> x' \<longleftrightarrow> a \<in> y'" proof
      assume "a \<in> x'" hence "M a" "mMem a x" 
        using mem_m[OF \<open>M x\<close>] mMemI' by simp_all
      hence "mMem a y" using iff by auto
      thus "a \<in> y'" using mMemD' by auto
    next
      assume "a \<in> y'" hence "M a" "mMem a y" 
        using mem_m[OF \<open>M y\<close>] mMemI' by simp_all
      hence "mMem a x" using iff by auto
      thus "a \<in> x'" using mMemD' by auto
    qed
  qed
  thus "x = y" using kpair_iff by simp
qed


definition "mUnion x \<equiv> set \<triangleright> (\<Union> (RepFun ObjOf (Part set (ObjOf x))))"

text \<open>(UNI): Axiom of Union\<close>
theorem munion_iff : "m\<forall>x. mSet x \<longrightarrow> mSet (mUnion x) 
          \<and> (m\<forall>a. mMem a (mUnion x) \<longleftrightarrow> (m\<exists>z. mMem z x \<and> mMem a z))"
proof (rule, rule, rule)
  fix x assume "M x" "mSet x"
  then obtain \<beta> x' where "Ord \<beta>" "x \<in> Tier (succ \<beta>)" "x' \<subseteq> Tier \<beta>" "x = set \<triangleright> x'" by (auto elim: msetE3)
  show "mSet (mUnion x)" unfolding mUnion_def by simp
  show "m\<forall>a. mMem a (mUnion x) \<longleftrightarrow> (m\<exists>z. mMem z x \<and> mMem a z)"
  proof (rule)
    fix a assume "M a" show "mMem a (mUnion x) = (m\<exists>z. mMem z x \<and> mMem a z)"
    proof
      assume "mMem a (mUnion x)" 
      hence "a \<in> \<Union> RepFun ObjOf (Part set x')" unfolding mUnion_def using mMemD' \<open>x = set \<triangleright> x'\<close> by auto 
      then obtain z where "a \<in> ObjOf z" "z \<in> Part set x'" 
        using repfun_union[OF part_set[OF mset_obj_set'[OF \<open>M x\<close> \<open>x = set \<triangleright> x'\<close>]]] by auto
      hence "mSet z" "z \<in> x'" using mset_obj_set'[OF \<open>M x\<close> \<open>x = set \<triangleright> x'\<close>] partD1 partD2 unfolding mSet_def by auto
      hence "M z" "mMem a z" "mMem z x" 
         using mem_m[OF \<open>M x\<close> \<open>x = set \<triangleright> x'\<close>] mMemI[OF _ \<open>a \<in> ObjOf z\<close>] mMemI'[OF \<open>x = set \<triangleright> x'\<close>] by auto 
      thus "m\<exists>z. mMem z x \<and> mMem a z" by auto
    next
      assume "m\<exists>z. mMem z x \<and> mMem a z"
      then obtain z where "M z" "mMem z x" "mMem a z" by auto
      hence "z \<in> x'" "TagOf z = set" "a \<in> ObjOf z" using mMemD mMemD'[OF \<open>x = set \<triangleright> x'\<close>] mMem_mset mSet_def by auto
      hence "z \<in> Part set (ObjOf x)" using partI m_tag[OF \<open>M z\<close>] \<open>x = set \<triangleright> x'\<close> by auto
      hence "a \<in> \<Union> RepFun ObjOf (Part set (ObjOf x))" unfolding 
        repfun_union[OF part_set[OF mset_obj_set[OF \<open>M x\<close> \<open>mSet x\<close>]]] using \<open>a \<in> ObjOf z\<close> by auto
      thus "mMem a (mUnion x)" unfolding mUnion_def using mMemI by auto
    qed
  qed
qed

definition mSubset where msub_def : "mSubset x y \<equiv> mSet x \<and> mSet y \<and> (\<forall>a. mMem a x \<longrightarrow> mMem a y)"
thm strip
lemmas stripm = impI allI rallI mallI

text \<open>(SUB): Definition of Subset\<close>
theorem msub_iff : "m\<forall>x y. mSubset x y \<longleftrightarrow> mSet x \<and> mSet y \<and> (m\<forall>a. mMem a x \<longrightarrow> mMem a y)"
  unfolding msub_def mall_def rall_def using mMem_m by auto

lemma msubI : assumes "mSet x" "mSet y" 
  shows "(\<And>a. mMem a x \<Longrightarrow> mMem a y) \<Longrightarrow> mSubset x y"
  using assms msub_def by auto

lemma msubI' : assumes "x = set \<triangleright> x'" "y = set \<triangleright> y'" 
  shows "x' \<subseteq> y' \<Longrightarrow> mSubset x y"
  using assms msub_def mMemI'[OF assms(2)] mMemD'[OF assms(1)] subsetD by auto

lemma msub_mset1 : "mSubset x y \<Longrightarrow> mSet x" unfolding msub_def by auto
lemma msub_mset2 : "mSubset x y \<Longrightarrow> mSet y" unfolding msub_def by auto

lemma msubE : assumes "M x" "M y" 
  "mSubset x y" "\<And>x' y'. \<lbrakk> x = set \<triangleright> x'; y = set \<triangleright> y'; x' \<subseteq> y' \<rbrakk> \<Longrightarrow> P" shows "P" 
proof -
  from assms(1,2,3) obtain x' y' where x':"x = set \<triangleright> x'" and y':"y = set \<triangleright> y'" 
    unfolding msub_def by (blast elim: msetE4)
  moreover have "x' \<subseteq> y'" using assms(3) mMemD'[OF y'] mMemI'[OF x']
   unfolding msub_def by (auto intro: subsetI[OF mset_obj_set'[OF \<open>M x\<close> x'] mset_obj_set'[OF \<open>M y\<close> y']])  
  ultimately show "P" using assms(4) by simp
qed

definition "mPow x \<equiv> set \<triangleright> (TagSetMems set (Pow (ObjOf x)))"

lemma mpow_mset : "mSet (mPow x)" unfolding mSet_def mPow_def by simp

text \<open>(POW): Axiom of Power Set\<close>
theorem "m\<forall>x. mSet x \<longrightarrow> (m\<forall>z. mMem z (mPow x) = mSubset z x)"
proof (rule, rule, rule)
  fix x z assume "M x" "M z" "mSet x"
  then obtain x' where x':"x = set \<triangleright> x'" using msetE4 by auto
  hence "Set x'" and mpow: "mPow x = set \<triangleright> TagSetMems set (Pow x')" 
    using mset_obj_set'[OF \<open>M x\<close>] unfolding mPow_def by simp_all
  
  show "mMem z (mPow x) = mSubset z x" proof
    assume "mMem z (mPow x)" 
    hence "z \<in> TagSetMems set (Pow x')" by (rule mMemD'[OF mpow])
    then obtain z' where "z' \<subseteq> x'" "z = set \<triangleright> z'" using powD[OF \<open>Set x'\<close>] 
      by (blast elim: tmapE[OF pow_set[OF \<open>Set x'\<close>]])
    thus "mSubset z x" using msubI'[OF _ x'] by auto
  next
    assume "mSubset z x" 
    then obtain z' x'' where z':"z = set \<triangleright> z'" "x = set \<triangleright> x''" and "z' \<subseteq> x''" 
      using msubE[OF \<open>M z\<close> \<open>M x\<close>] x' by blast
    also hence "z' \<subseteq> x'" using x' by (auto elim: pair_inject)
    hence "z' \<in> Pow x'" using powI by simp
    hence "z \<in> TagSetMems set (Pow x')" using tmapI z' by auto
    thus "mMem z (mPow x)" unfolding mPow_def using mMemI'' x' by auto
  qed
qed

definition "mSucc x \<equiv> mUnion (set \<triangleright> (upair x (set \<triangleright> (sng x))))"

lemma sng_succ : assumes "Ord \<beta>" "x = set \<triangleright> x'" 
  shows "x \<in> Tier \<beta> \<Longrightarrow> set \<triangleright> sng x \<in> Tier (succ \<beta>)"
  by  (rule set_succI'[OF assms(1)], rule subsetI[OF sng_set diff_set[OF tier_set[OF \<open>Ord \<beta>\<close>]]], 
       unfold sng_iff, rule diffI, use no_set_ignored assms(2) in auto)

lemma upair_succ : assumes "Ord \<beta>" "x = set \<triangleright> x'" "y = set \<triangleright> y'" 
  shows "x \<in> Tier \<beta> \<Longrightarrow> y \<in> Tier \<beta> \<Longrightarrow> set \<triangleright> upair x y \<in> Tier (succ \<beta>)"
  by (rule set_succI'[OF assms(1)], rule subsetI[OF upair_set diff_set[OF tier_set[OF \<open>Ord \<beta>\<close>]]], 
      unfold upair_iff, rule diffI, use no_set_ignored assms(2,3) in auto)

text \<open>(SUC): Characterisation of Successor Operation\<close>
theorem msucc_iff : "m\<forall>x. mSet x \<longrightarrow> (m\<forall>a. mMem a (mSucc x) = (mMem a x \<or> a = x))"
proof (rule, rule, rule)
  fix x a assume "M x" "M a" "mSet x"
  then obtain \<beta> x' where "Ord \<beta>" and x:"x \<in> Tier \<beta>" and x': \<open>x = set \<triangleright> x'\<close> by (blast elim: msetE3)
  let ?sng = "set \<triangleright> sng x" 
  let ?up = "set \<triangleright> upair x ?sng"
  have "?sng \<in> Tier (succ \<beta>)" and "x \<in> Tier (succ \<beta>)" by (rule sng_succ[OF \<open>Ord \<beta>\<close> x' x], rule tier_succI1[OF \<open>Ord \<beta>\<close> x])
  hence upM:"?up \<in> Tier (succ (succ \<beta>))" using upair_succ[OF succ_ord[OF \<open>Ord \<beta>\<close>] x'] by auto
  hence "M ?up" "mSet ?up" using mI[OF succ_ord[OF succ_ord[OF \<open>Ord \<beta>\<close>]]] by auto
  hence uni:"(m\<forall>a. mMem a (mUnion ?up) = (m\<exists>z. mMem z ?up \<and> mMem a z))" using munion_iff by blast
  show "mMem a (mSucc x) \<longleftrightarrow> mMem a x \<or> a = x" 
  proof 
    assume "mMem a (mSucc x)"
    hence "(m\<exists>z. mMem z ?up \<and> mMem a z)" unfolding mSucc_def using uni \<open>M a\<close> by auto 
    then obtain z where "M z" "mMem z ?up" "mMem a z" by blast
    hence "z \<in> upair x ?sng" using mMemD' by auto
    thus "mMem a x \<or> a = x" using \<open>mMem a z\<close> mMemD'[OF _ \<open>mMem a z\<close>] sng_iff by (auto elim: upairE)
  next
    assume "mMem a x \<or> a = x"
    hence "mMem a x \<or> mMem a ?sng" using mMemI' sngI by auto
    then obtain z where "mMem z ?up" "mMem a z" using upairI1 upairI2 mMemI' by blast
    moreover hence "M z" using mI[OF succ_ord[OF \<open>Ord \<beta>\<close>] mMem_tier[OF succ_ord[OF \<open>Ord \<beta>\<close>] upM]] by auto
    ultimately have "m\<exists>z. mMem z ?up \<and> mMem a z" by auto
    thus "mMem a (mSucc x)" unfolding mSucc_def using uni \<open>M a\<close> by auto
  qed
qed

abbreviation "\<Theta> n \<equiv> OrdRec (\<lambda>\<mu> f. f[predSet \<omega>]) (\<lambda>_ x. mSucc x) mEmp n"

definition "mInf \<equiv> set \<triangleright> (\<Theta> \<omega>)"

text \<open>(INF): Axiom of Infinity\<close>
theorem minf: "mMem mEmp mInf \<and> (m\<forall>x. mMem x mInf \<longrightarrow> mMem (mSucc x) mInf)"
proof
  have theta:"\<Theta> \<omega> = RepFun \<Theta> (predSet \<omega>)" using ordrec_lim \<omega>_lim image_domain by auto
  show "mMem mEmp mInf" unfolding mInf_def theta
  proof (rule mMemI', simp)
    have "\<Theta> 0 = mEmp" using ordrec_0 by simp
    moreover have "\<Theta> 0 \<in> RepFun \<Theta> (predSet \<omega>)" using repfunI[OF predsetI[OF \<omega>_0]] by auto
    ultimately show "mEmp \<in> RepFun \<Theta> (predSet \<omega>)" by simp
  qed
  thm mMemD'
  show "m\<forall>x. mMem x mInf \<longrightarrow> mMem (mSucc x) mInf" unfolding mInf_def theta
  proof (rule, rule, rule mMemI', simp)
    fix x assume "M x" "mMem x (set \<triangleright> RepFun \<Theta> (predSet \<omega>))"
    hence "x \<in> RepFun \<Theta> (predSet \<omega>)" using mMemD' by auto
    then obtain \<beta>  where "x = \<Theta> \<beta>" "\<beta> < \<omega>" 
       using repfunE[OF predset_set[OF \<omega>_ord]] predsetE[OF \<omega>_ord] by blast
     hence "mSucc x = \<Theta> (succ \<beta>)" using ordrec_succ by auto
     thus "mSucc x \<in> RepFun \<Theta> (predSet \<omega>)" using repfunI[OF predsetI[OF \<omega>_succ[OF \<open>\<beta> < \<omega>\<close>]]] by auto
  qed
qed



definition "mRepl P x \<equiv> set \<triangleright> (Replace (\<lambda>a b. M a \<and> M b \<and> P a b) (ObjOf x))"

text \<open>(REPL): Axiom of Replacement\<close>
lemma mrepl: "\<forall>P. m\<forall>x. mSet x \<longrightarrow> mSet (mRepl P x) \<and> ((m\<forall>a. mMem a x \<longrightarrow> (m\<exists>\<^sub>\<le>\<^sub>1b. P a b)) 
    \<longrightarrow> (m\<forall>b. mMem b (mRepl P x) = (m\<exists>a. mMem a x \<and> P a b)))"
proof (rule, rule, rule, rule)
  fix P x assume "M x" "mSet x"
  then obtain x' where x':"x = set \<triangleright> x'" using msetE4 by auto
  hence "ObjOf x = x'" "Set x'" using mset_obj_set[OF \<open>M x\<close> \<open>mSet x\<close>] by auto

  show "mSet (mRepl P x)" unfolding mRepl_def by simp
  show "(m\<forall>a. mMem a x \<longrightarrow> (m\<exists>\<^sub>\<le>\<^sub>1b. P a b)) \<longrightarrow> (m\<forall>b. mMem b (mRepl P x) = (m\<exists>a. mMem a x \<and> P a b))"
  proof (rule)  
    let ?P' = "(\<lambda>a b. M a \<and> M b \<and> P a b)"
    assume "m\<forall>a. mMem a x \<longrightarrow> (m\<exists>\<^sub>\<le>\<^sub>1 b. P a b)"
    hence uniq: "\<And>a b c. M a \<Longrightarrow> mMem a x \<Longrightarrow> M b \<Longrightarrow> M c \<Longrightarrow> P a b \<Longrightarrow> P a c \<Longrightarrow> b =c" unfolding muniq_def by auto
    show "m\<forall>b. mMem b (mRepl P x) = (m\<exists>a. mMem a x \<and> P a b)"
    proof (rule, rule)
      fix b assume "M b" "mMem b (mRepl P x)"
      hence "b \<in> Replace ?P' x'" unfolding mRepl_def using mMemD' \<open>ObjOf x = x'\<close> by (auto)
      thus "m\<exists>a. mMem a x \<and> P a b" 
      proof (rule replaceE[OF \<open>Set x'\<close>])
        fix a assume "a \<in> x'" "?P' a b"
        hence "M a" "mMem a x" "P a b" using mMemI'[OF x'] by auto
        thus "m\<exists>a. mMem a x \<and> P a b" by auto
      qed
    next
      fix b assume "M b" "m\<exists>a. mMem a x \<and> P a b"
      then obtain a where "M a" "mMem a x" "P a b" by auto
      show "mMem b (mRepl P x)" proof (rule mMemI', simp add: mRepl_def, rule replaceI)
        show "M a \<and> M b \<and> P a b" using \<open>M a\<close> \<open>M b\<close> \<open>P a b\<close> forceM_def by auto
        show "a \<in> ObjOf x" by (rule mMemD[OF \<open>mMem a x\<close>])
        fix c assume "M a \<and> M c \<and> P a c" thus "c=b"
          using uniq[OF \<open>M a\<close> \<open>mMem a x\<close>] \<open>M b\<close> \<open>P a b\<close> by auto
      qed
    qed
  qed
qed




(*Model versions of Ord constants*)
definition "mOrd_conv \<beta> \<equiv> ord \<triangleright> \<beta>"
definition "mOrd \<B> \<equiv> TagOf \<B> = ord"

lemma mOrdI : "b = ord \<triangleright> b' \<Longrightarrow> mOrd b"
  unfolding mOrd_def by simp

definition "mzero \<equiv> ord \<triangleright> 0" 
definition "momega \<equiv> ord \<triangleright> \<omega>"

theorem "mOrd mzero" unfolding mzero_def using mOrdI by auto
theorem "mOrd momega" unfolding momega_def using mOrdI by auto

definition "mlt \<A> \<B> \<equiv> mOrd \<A> \<and> mOrd \<B> \<and> (ObjOf \<A>) < (ObjOf \<B>)"

theorem "m\<forall>\<alpha> \<beta>. mlt \<alpha> \<beta> \<longrightarrow> mOrd \<alpha> \<and> mOrd \<beta>"
  using mlt_def by auto

definition "msucc \<B> \<equiv> ord \<triangleright> (succ (ObjOf \<B>))"
theorem "m\<forall>\<beta>. mOrd (msucc \<beta>) = mOrd \<beta>" sorry


definition "mpredSet \<B> \<equiv> set \<triangleright> (TagSetMems ord (predSet (ObjOf \<B>)))"
definition "mOrdRec L F A \<B> \<equiv> OrdRec (\<lambda>a b. L (forceM a) (forceM b)) (\<lambda>a b. F (forceM a) (forceM b)) A (ObjOf \<B>)"



definition "mLimit \<B> \<equiv> Limit (ObjOf \<B>)"




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



end
end






    