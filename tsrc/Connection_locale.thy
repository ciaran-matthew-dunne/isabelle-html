theory Connection_locale
  imports Model_locale
  keywords "lift_model_defs" :: thy_goal 
begin 

ML_file \<open>transfer_all_method.ML\<close>

locale Connection = Model Ord lt zero succ Limit predSet OrdRec omega
  for 
    Ord :: "'i \<Rightarrow> bool" and
    lt :: "'i \<Rightarrow> 'i \<Rightarrow> bool" (infixl \<open><\<close> 50) and
    zero :: "'i" (\<open>0\<close>) and
    succ :: "'i \<Rightarrow> 'i" and
    Limit :: "'i \<Rightarrow> bool" and
    predSet :: "'i \<Rightarrow> 'i" and
    OrdRec :: "('i \<Rightarrow> 'i \<Rightarrow> 'i) \<Rightarrow> ('i \<Rightarrow> 'i \<Rightarrow> 'i) \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> 'i" and
    omega :: "'i" (\<open>\<omega>\<close>) +
  fixes 
    Abs :: "'i \<Rightarrow> 'j" and
    Rep :: "'j \<Rightarrow> 'i"
  assumes 
    td : "type_definition Rep Abs (Set.Collect M)"

context Connection begin
context includes lifting_syntax begin
thm Connection_axioms
find_theorems Connection

find_theorems "GZF_locale.GZF"
ML \<open>Locale.get_intros @{context}\<close>
ML \<open>val (SOME intros) = fst (Locale.intros_of @{theory} "GZF_locale.GZF")\<close> 
ML \<open>val assms = Thm.prems_of intros\<close>
ML \<open>val [Element.Assumes it] = Locale.hyp_spec_of @{theory} "GZF_locale.GZF"\<close>

ML \<open>
  fun get_locale_assms thy str = let
      val [Element.Assumes assms] = Locale.hyp_spec_of thy str
  in map ((fn bind => str ^ "." ^ (Binding.name_of bind)) o fst o fst) assms end
  val it = map (get_locale_assms @{theory}) 
          ["GZF_locale.GZF", "Ord_locale.Ord", "Model_locale.Model", "Connection_locale.Connection"]
  val it2 = List.concat it 
  val it3 = Pretty.big_list "" (map (Pretty.str) it2)  \<close>



ML \<open>Locale.pretty_locale @{theory} true "GZF_locale.GZF"\<close>
interpretation connect: type_definition "Rep" "Abs" "(Set.Collect M)"
  by (rule td)

definition md :: "'i \<Rightarrow> 'j \<Rightarrow> bool"
  where "md x y \<equiv> x = Rep y"

ML_file \<open>swap_transfer.ML\<close>

lemma M_abs_inverse [simp] : "M x \<Longrightarrow> Rep (Abs x) = x" using connect.Abs_inverse by simp
lemma M_rep [simp] : "M (Rep x)" using connect.Rep by simp
declare M_abs_inverse connect.Rep_inverse [simp]

lemmas forceM_inverse = M_abs_inverse[OF forceM_m] 

lemma binpred_transfer : assumes "(md ===> md ===> iff) P Q" shows
  "(\<lambda>a b. Q (Abs (forceM a)) (Abs (forceM b))) = (\<lambda>a b. P (forceM a) (forceM b))"
proof (rule, rule) 
  have ab: "\<And>a b. M a \<and> M b \<longrightarrow> (P a b \<longleftrightarrow> Q (Abs a) (Abs b))" 
  proof
    fix a b
    from assms have pq : "\<And>a' b'. a = Rep a' \<Longrightarrow> b = Rep b' \<Longrightarrow> (P a b \<longleftrightarrow> Q a' b')" unfolding md_def by (auto dest: rel_funD)
    assume "M a \<and> M b"
    hence "a = Rep (Abs a)" and "b = Rep (Abs b)" by auto
    thus "(P a b \<longleftrightarrow> Q (Abs a) (Abs b))" using pq[of \<open>Abs a\<close> \<open>Abs b\<close>] by auto
  qed
  fix a b 
  show " Q (Abs (forceM a)) (Abs (forceM b)) = P (forceM a) (forceM b)" 
    using forceM_m ab[of \<open>forceM a\<close> \<open>forceM b\<close>] by auto
qed

lemma unfun_transfer : assumes "(md ===> md) F G" 
  shows "Rep (G (Abs (forceM a))) = F (forceM a)"
proof - 
  from assms have a:"\<And>a a'. a = Rep a' \<Longrightarrow> F a = Rep (G a')" unfolding md_def by (auto dest: rel_funD)
  from forceM_inverse have "(forceM a) = Rep (Abs (forceM a))" by simp
  thus ?thesis using a[of \<open>forceM a\<close> \<open>Abs (forceM a)\<close>] by auto
qed

lemma binfun_transfer : assumes "(md ===> md ===> md) F G" 
  shows "Rep (G (Abs (forceM a)) (Abs (forceM b))) = F (forceM a) (forceM b)"
proof - 
  from assms have ab:"\<And>a a' b b'. a = Rep a' \<Longrightarrow> b = Rep b' \<Longrightarrow> F a b = Rep (G a' b')" 
    unfolding md_def by (auto dest: rel_funD)
  from forceM_inverse have "(forceM a) = Rep (Abs (forceM a))" "(forceM b) = Rep (Abs (forceM b))" by simp_all
  thus ?thesis using ab[of \<open>forceM a\<close> \<open>Abs (forceM a)\<close> \<open>forceM b\<close> \<open>Abs (forceM b)\<close>] by auto
qed

lift_model_defs lift_base: mOrd 
proof -
  show "(md ===> md ===> (=)) mMem cMem" unfolding cMem_def md_def by auto
  show "md mEmp cEmp" unfolding cEmp_def md_def using closed_gzf(1) by auto
  show "(md ===> (=)) mSet cSet" unfolding cSet_def md_def by auto
  show "(md ===> md) mUnion cUnion" unfolding cUnion_def md_def using closed_gzf(2) by auto    
  show "(md ===> md ===> (=)) mSubset cSubset" unfolding cSubset_def md_def by auto
  show "(md ===> md) mPow cPow" unfolding cPow_def md_def using closed_gzf(3) by auto
  show "(md ===> md) mSucc cSucc" unfolding cSucc_def md_def using closed_gzf(4) by auto
  show "md mInf cInf" unfolding cInf_def md_def using closed_gzf(5) by auto
  show "((md ===> md ===> (=)) ===> md ===> md) mRepl cRepl"   
  proof (rule, rule)
    fix P Q x y assume pq:"(md ===> md ===> iff) P Q"
    show "md x y \<Longrightarrow> md (mRepl P x) (cRepl Q y)" sorry
      (*by (unfold md_def mRepl_def cRepl_def, 
           subst binpred_transfer[OF pq], fold mRepl_def, 
           use closed_gzf(6) in auto) *)
  qed
  show "(md ===> (=)) mOrd cOrd" unfolding md_def cOrd_def by auto
  show "(md ===> md ===> (=)) mlt clt" unfolding md_def clt_def by auto
  show "md mzero czero" unfolding md_def czero_def using closed_ord by simp
  show "(md ===> md) msucc csucc" unfolding md_def csucc_def using closed_ord by auto
  show "(md ===> (=)) mLimit cLimit" unfolding cLimit_def md_def by auto
  show "(md ===> md) mpredSet cpredSet" unfolding cpredSet_def md_def using closed_ord(9) by auto
  show "((md ===> md ===> md) ===> (md ===> md ===> md) ===> 
          md ===> md ===> md) mOrdRec cOrdRec"
  proof (rule, rule, rule, rule)
    fix L L' F F' A A' \<beta> \<beta>'
    assume L: "(md ===> md ===> md) L L'" 
       and F: "(md ===> md ===> md) F F'"
       and A: "md A A'"
       and \<beta>: "md \<beta> \<beta>'" 
    show "md (mOrdRec L F A \<beta>) (cOrdRec L' F' A' \<beta>')"
      by (unfold md_def cOrdRec_def mOrdRec_def,
            subst binfun_transfer[OF L], 
            subst binfun_transfer[OF F],
            insert A \<beta>, unfold md_def, fold mOrdRec_def,
            use closed_ord(10) in auto)
  qed
  show "md momega comega" unfolding comega_def md_def using closed_ord(11) by simp
qed

declare lift_base [transfer_rule]


(*WARNING: BOILERPLATE
  Ciaran: Please figure out how to just generate these theorems for free.*)
lemma all_transfer [transfer_rule] : 
  "((md ===> iff) ===> iff) (mall) (All)"
proof
  fix P Q assume "(md ===> iff) P Q"
  hence x:"\<And>x x'. x = Rep x' \<Longrightarrow> P x \<longleftrightarrow> Q x'" unfolding md_def by (auto dest: rel_funD)
  show "mall P \<longleftrightarrow> All Q"
  proof (unfold mall_def rall_def, rule)
    assume P:"\<forall>x. M x \<longrightarrow> P x" 
    show "All Q" proof 
      fix x' have "P (Rep x')" using P by auto
      thus "Q x'" using x by auto
    qed
  next
    assume Q: "All Q"
    show "\<forall>x. M x \<longrightarrow> P x"
    proof (rule, rule) fix x assume "M x"
      hence "Q (Abs x)" using Q by auto
      thus "P x" using `M x` x[of x \<open>Abs x\<close>] by auto
    qed
  qed
qed
    

lemma ex_transfer [transfer_rule] : 
  "((md ===> iff) ===> iff) (mex) (Ex)"
proof 
  fix P Q assume "(md ===> iff) P Q"
  hence x:"\<And>x x'. x = Rep x' \<Longrightarrow> P x \<longleftrightarrow> Q x'" unfolding md_def by (auto dest: rel_funD)
  show "mex P \<longleftrightarrow> Ex Q"
  proof (unfold mex_def rex_def, rule)
    assume P: "\<exists>x. M x \<and> P x" 
    show "Ex Q" proof -
      obtain x where "M x \<and> P x" using P by auto
      hence "Q (Abs x)" using x[of \<open>x\<close> \<open>Abs x\<close>] by auto
      thus "Ex Q" by blast
    qed
  next
    assume Q: "Ex Q"
    show "\<exists>x. M x \<and> P x"
    proof - 
      obtain x' where "Q x'" using Q by auto
      hence "M (Rep x') \<and> P (Rep x')" using x by auto
      thus "\<exists>x. M x \<and> P x " by blast
    qed
  qed
qed


lemma uniq_transfer [transfer_rule] : 
   "((md ===> iff) ===> iff) (muniq) (Uniq)" 
proof
  fix P Q assume "(md ===> iff) P Q"
  hence x:"\<And>x x'. x = Rep x' \<Longrightarrow> P x \<longleftrightarrow> Q x'" unfolding md_def by (auto dest: rel_funD)
  show "muniq P \<longleftrightarrow> Uniq Q"
  proof (unfold muniq_def mall_def rall_def, rule)
    assume P : "\<forall>x. M x \<longrightarrow> (\<forall>y. M y \<longrightarrow> P x \<and> P y \<longrightarrow> x = y)"
    show "Uniq Q"
    proof 
      fix x' y' assume "Q x'" "Q y'"
      let ?x = "Rep x'" and ?y = "Rep y'"
      from P have xy:"P ?x \<and> P ?y \<longrightarrow> ?x = ?y" by auto
      thus "x' = y'"
      proof - 
        have "P ?x \<and> P ?y" using \<open>Q x'\<close> \<open>Q y'\<close> x by auto
        thus "x' = y'" using xy connect.Rep_inject by simp
      qed
    qed
  next
    assume Q: "Uniq Q"
    show "\<forall>x. M x \<longrightarrow> (\<forall>y. M y \<longrightarrow> P x \<and> P y \<longrightarrow> x = y)"
    proof (rule, rule, rule, rule, rule)
      fix x y assume "M x" "M y" "P x \<and> P y" 
      hence "Q (Abs x) \<and> Q (Abs y)" using x[of \<open>x\<close> \<open>Abs x\<close>] x[of \<open>y\<close> \<open>Abs y\<close>] by auto
      hence "(Abs x) = (Abs y)" using Q unfolding Uniq_def by simp
      thus "x = y" using connect.Abs_inject \<open>M x\<close> \<open>M y\<close> by auto
    qed
  qed
qed

lemma eq_transfer [transfer_rule] : "(md ===> md ===> iff) (=) (=)" 
  unfolding md_def rel_fun_def using connect.Rep_inject by auto


lemma binpred_all_transfer [transfer_rule] :
  "(((md ===> md ===> iff) ===> iff) ===> iff) All All" 
proof 
  fix U :: "('i \<Rightarrow> 'i \<Rightarrow> bool) \<Rightarrow> bool" and V  
  assume "((md ===> md ===> (=)) ===> (=)) U V"
  hence pq:"\<And>P Q. (\<And>a a' b b'. a = Rep a' \<Longrightarrow> b = Rep b' \<Longrightarrow> P a b \<longleftrightarrow> Q a' b') \<Longrightarrow> U P \<longleftrightarrow> V Q"
    unfolding md_def rel_fun_def by auto
  show "All U = All V"
  proof
    assume U:"All U"
    show "All V"
    proof fix Q :: "'j \<Rightarrow> 'j \<Rightarrow> bool"
      let ?P = "\<lambda>a b. Q (Abs a) (Abs b)"
      have "\<And>a a' b b'. a = Rep a' \<Longrightarrow> b = Rep b' \<Longrightarrow> ?P a b \<longleftrightarrow> Q a' b'" by auto
      hence "U ?P \<longleftrightarrow> V Q" by (rule pq)
      thus "V Q" using U by simp
    qed
  next
    assume V: "All V"
    show "All U"
    proof fix P :: "'i \<Rightarrow> 'i \<Rightarrow> bool"
      let ?Q = "\<lambda>a' b'. P (Rep a') (Rep b')"
      have "\<And>a a' b b'. a = Rep a' \<Longrightarrow> b = Rep b' \<Longrightarrow> P a b \<longleftrightarrow> ?Q a' b'" by auto
      hence "U P \<longleftrightarrow> V ?Q" by (rule pq)
      thus "U P" using V by simp
    qed
  qed
qed

lemma unfun_all_transfer [transfer_rule]: 
  "(((md ===> md) ===> iff) ===> iff) fun_mall All"
proof
  fix P Q assume "((md ===> md) ===> iff) P Q"
  hence FG: "\<And> F G. (\<And>x x'. x = Rep x' \<Longrightarrow> F x = Rep (G x')) \<Longrightarrow> P F \<longleftrightarrow> Q G" unfolding md_def rel_fun_def by simp
  show "fun_mall P \<longleftrightarrow> All Q"
  proof
    assume P:"fun_mall P"
    show "All Q" 
    proof fix G :: "'j \<Rightarrow> 'j"
      let ?F = "\<lambda>x. Rep (G (Abs x))"
      have "\<And>x x'. x = Rep x' \<Longrightarrow> ?F x = Rep (G x')" by (auto)
      hence "P ?F \<longleftrightarrow> Q G" using FG by auto
      thus "Q G" using P unfolding fun_mall_def by auto
    qed
  next
    assume Q:"All Q"
    show "fun_mall P" 
    proof (unfold fun_mall_def, rule, rule) 
      fix F :: "'i \<Rightarrow> 'i" assume M:"\<forall>x. M x \<longrightarrow> M (F x)"
      let ?G = "\<lambda>x. Abs (F (Rep x))"
      have "\<And>x x'. x = Rep x' \<Longrightarrow> F x = Rep (?G x')" using M by auto
      hence "P F \<longleftrightarrow> Q ?G" using FG by auto
      thus "P F" using Q by auto
    qed
  qed
qed

lemma binfun_all_transfer [transfer_rule]: 
  "(((md ===> md ===> md) ===> iff) ===> iff) binfun_mall All"
proof
  fix P Q assume "((md ===> md ===> md) ===> iff) P Q"
  hence FG: "\<And> F G. (\<And>x x' y y'. x = Rep x' \<Longrightarrow> y = Rep y' \<Longrightarrow> F x y = Rep (G x' y')) \<Longrightarrow> P F \<longleftrightarrow> Q G"
    unfolding md_def rel_fun_def by simp
  show "binfun_mall P \<longleftrightarrow> All Q"
  proof
    assume P:"binfun_mall P"
    show "All Q" 
    proof fix G :: "'j \<Rightarrow> 'j \<Rightarrow> 'j"
      let ?F = "\<lambda>x y. Rep (G (Abs x) (Abs y))"
      have "\<And>x x' y y'. x = Rep x' \<Longrightarrow> y = Rep y' \<Longrightarrow> ?F x y = Rep (G x' y')" by (auto)
      hence "P ?F \<longleftrightarrow> Q G" using FG by auto
      thus "Q G" using P unfolding binfun_mall_def by auto
    qed
  next
    assume Q:"All Q"
    show "binfun_mall P" 
    proof (unfold binfun_mall_def, rule, rule) 
      fix F :: "'i \<Rightarrow> 'i \<Rightarrow> 'i" assume M:"\<forall>x y. M x \<and> M y \<longrightarrow> M (F x y)"
      let ?G = "\<lambda>x y. Abs (F (Rep x) (Rep y))"
      have "\<And>x x' y y'. x = Rep x' \<Longrightarrow> y = Rep y' \<Longrightarrow> F x y = Rep (?G x' y')" using M by auto
      hence "P F \<longleftrightarrow> Q ?G" using FG by auto
      thus "P F" using Q by auto
    qed
  qed
qed
(*END BOILERPLATE*)

(*From here we can interpret the Base locale, and get GZF/Ordinal definitions on 'j for free.
  If we then define an Ops operator, we can invoke the model locale.
  If we then give a type_definition on this model, we can invoke the Connection locale
  and repeat the process. *)
interpretation interp : Ord cMem cEmp cSet cUnion cSubset cPow cSucc cInf cRepl 
                            cOrd clt czero csucc cLimit cpredSet cOrdRec comega 
  sorry
(* proof (unfold_locales, transfer_all,
      rule trans_gzf(1), rule trans_gzf(2), rule trans_gzf(3), 
      rule trans_gzf(4), rule trans_gzf(5), rule trans_gzf(6), 
      rule trans_gzf(7), rule trans_gzf(8), rule trans_gzf(9)) *)
end
end
end