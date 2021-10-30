theory GZF_locale
  imports Main begin

no_notation Set.member ("'(\<in>')") and 
            Set.member ("(_/ \<in> _)" [51, 51] 50) and
            Set.not_member  ("'(\<notin>')") and
            Set.not_member  (infixl \<open>\<notin>\<close> 50) and
            Set.not_member  ("(_/ \<notin> _)" [51, 51] 50) and
            subset_eq  ("'(\<subseteq>')") and
            subset_eq  ("(_/ \<subseteq> _)" [51, 51] 50) and
            Union ("\<Union>") and Inter ("\<Inter>") and
            union (infixl "\<union>" 65) and inter (infixl "\<inter>" 70) and
            image (infixr "`" 90)

no_notation Product_Type.Times (infixr "\<times>" 80)

no_notation less_eq  ("'(\<le>')") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50) and
  less  ("'(<')") and
  less  ("(_/ < _)"  [51, 51] 50)

no_notation 
  Groups.minus (infixl "-" 65) and 
  Groups.zero ("0") and 
  Groups.one_class.one ("1")

no_notation (ASCII)
  Set.member  ("'(:')") and
  Set.member  ("(_/ : _)" [51, 51] 50) and
  Set.not_member  ("'(~:')") and
  Set.not_member  ("(_/ ~: _)" [51, 51] 50) and
  less_eq  ("'(<=')") and
  less_eq  ("(_/ <= _)" [51, 51] 50) and
  union (infixl "Un" 65) and
  inter (infixl "Int" 70)

notation (ASCII)
  not_equal  (infixl \<open>~=\<close> 50) and
  Not  (\<open>~ _\<close> [40] 40) and
  conj  (infixr \<open>&\<close> 35) and
  disj  (infixr \<open>|\<close> 30) and
  All  (binder \<open>ALL \<close> 10) and
  Ex  (binder \<open>EX \<close> 10) and
  Ex1  (binder \<open>EX! \<close> 10) and
  implies  (infixr \<open>-->\<close> 25) and
  iff  (infixr \<open><->\<close> 25)

(*Removing list syntax so that we can have f[x] := image(f,x) *)
no_translations
  "[x, xs]" == "x#[xs]"
  "[x]" == "x#[]"
no_syntax
  "_list" :: "args => 'a list" ("[(_)]")

locale GZF =  (*Fixes and axiomatises constants on type 'd*)
  fixes Mem :: "'d \<Rightarrow> 'd \<Rightarrow> bool"  (infixl \<open>\<in>\<close> 50) 
    and Emp :: "'d"  (\<open>\<emptyset>\<close>)
    and Set :: "'d \<Rightarrow> bool"            
    and Union :: "'d \<Rightarrow> 'd" (\<open>\<Union> _\<close> [90] 90)
    and Subset :: "['d,'d] \<Rightarrow> bool" (infixl \<open>\<subseteq>\<close> 50)
    and Pow ::  "'d \<Rightarrow> 'd" (\<open>\<P> _\<close> [90] 90)
    and Succ :: "'d \<Rightarrow> 'd"
    and Inf :: "'d" 
    and Repl :: "[['d,'d] \<Rightarrow> bool] \<Rightarrow> 'd \<Rightarrow>'d" (\<open>\<R>\<close> 90) 
 assumes emp : "\<forall>x. ~ (x \<in> \<emptyset>)"
    and set : "\<forall>x. Set x \<longleftrightarrow> (x = \<emptyset> \<or> (\<exists>y. y \<in> x))"
    and ext : "\<forall>x y. Set x \<longrightarrow> Set y \<longrightarrow> 
      ((\<forall>a. a \<in> x \<longleftrightarrow> a \<in> y) \<longrightarrow> x = y)"
    and subset_def : "\<forall>x y. x \<subseteq> y \<longleftrightarrow> Set x \<and> Set y \<and> (\<forall>a. a \<in> x \<longrightarrow> a \<in> y)"
    and uni : "\<forall>x. Set x \<longrightarrow> (Set (\<Union> x) \<and> (\<forall>a. a \<in> \<Union> x \<longleftrightarrow> (\<exists>z. z \<in> x \<and> a \<in> z)))"
    and pow : "\<forall>x. Set x \<longrightarrow> (\<forall>z. z \<in> \<P> x \<longleftrightarrow> z \<subseteq> x)" 
    and suc : "\<forall>x. Set x \<longrightarrow> (\<forall>a. a \<in> Succ x \<longleftrightarrow> (a \<in> x \<or> a = x))"
    and inf : "\<emptyset> \<in> Inf \<and> (\<forall>x. x \<in> Inf \<longrightarrow> Succ x \<in> Inf)"
    and repl: "\<forall>P x. Set x \<longrightarrow> Set (Repl P x) \<and> 
             ((\<forall>a. a \<in> x \<longrightarrow> (\<exists>\<^sub>\<le>\<^sub>1 b. P a b))
         \<longrightarrow> (\<forall>b. b \<in> (Repl P x) \<longleftrightarrow> (\<exists>a. a \<in> x \<and> P a b)))" 

context GZF begin

definition the_default :: "'d \<Rightarrow> ('d \<Rightarrow> bool) \<Rightarrow> 'd" (\<open>\<iota>'' _ _\<close> [90,90] ) where
 "\<iota>' d F \<equiv> if Ex1 F then (THE x. F x) else d"

lemma the_def_if : "if (Ex1 F) then (F a \<longleftrightarrow> \<iota>' d F = a) 
                               else \<iota>' d F = d"
proof (cases \<open>Ex1 F\<close>)
  assume "Ex1 F" hence eq:"\<iota>' d F = (THE x. F x)" 
    unfolding the_default_def by auto
  have "F a \<longleftrightarrow> \<iota>' d F = a" 
  proof
    assume "F a"
    thus "\<iota>' d F = a" by (subst eq, insert \<open>Ex1 F\<close>, auto)
  next
    assume "\<iota>' d F = a"
    thus "F a" using eq \<open>Ex1 F\<close> by (auto intro: theI)
  qed
  thus "if (Ex1 F) then (F a \<longleftrightarrow> \<iota>' d F = a) else \<iota>' d F = d" using \<open>Ex1 F\<close> by simp
next
  assume "\<not> Ex1 F"
  thus "if (Ex1 F) then (F a \<longleftrightarrow> \<iota>' d F = a) else \<iota>' d F = d" 
    unfolding the_default_def by auto
qed

lemma the_def_eq : assumes "P a" "\<And>x. P x \<Longrightarrow> x = a"
  shows "\<iota>' d P = a"
proof -
  from assms have "Ex1 P" by auto
  hence "P a \<longleftrightarrow> (\<iota>' d P) = a" using the_def_if by auto
  thus "(\<iota>' d P) = a" using \<open>P a\<close> by auto
qed

lemma the_defI : assumes "P a" "\<And>x. P x \<Longrightarrow> x = a" 
  shows "P (\<iota>' d P)"
proof - 
  from the_def_eq assms have "\<iota>' d P = a" by blast 
  thus "P (\<iota>' d P)" using \<open>P a\<close> by simp
qed

lemma the_defI' : assumes "Ex1 P" shows "P (\<iota>' d P)"
  using assms by (blast intro: the_defI)

lemma the_defI2 : assumes "P a" "\<And>x. P x \<Longrightarrow> x = a" "\<And>x. P x \<Longrightarrow> Q x"
  shows "Q (\<iota>' d P)" by (blast intro: assms the_defI)

lemma the_defI2' : assumes "Ex1 P" "\<And>x. P x \<Longrightarrow> Q x" shows "Q (\<iota>' d P)" 
  by (blast intro: assms(2) the_defI2[where P=P and Q=Q] ex1E[OF assms(1)])

lemma the_def_eq' : "\<lbrakk> Ex1 P ; P a \<rbrakk> \<Longrightarrow> (\<iota>' d P) = a"
  by (blast intro: the_def_eq)

subsection \<open>Restricted quantification using a predicate\<close>

definition rall :: "('d \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> bool) \<Rightarrow> bool" where
  rall_def : "rall P Q \<equiv> \<forall>x. P x \<longrightarrow> Q x"
definition rex :: "('d \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> bool) \<Rightarrow> bool" where
  rex_def : "rex P Q \<equiv> \<exists>x. P x \<and> Q x"

(*Taken from ZF/OrdQuant, unfolded syntax*)
lemma rallI [intro]: "[| !!x. M(x) ==> P(x) |] ==> rall M P"
by (simp add: rall_def)

lemma rspec: "[| rall M P; M(x) |] ==> P(x)"
by (simp add: rall_def)

lemma rev_rallE [elim]:
    "[| rall M P;  ~ M(x) ==> Q;  P(x) ==> Q |] ==> Q"
by (simp add: rall_def, blast)

lemma rallE: "[| rall M P; P(x) ==> Q;  ~ M(x) ==> Q |] ==> Q"
by blast

lemma rall_triv [simp]: "(rall M (\<lambda>x. P)) \<longleftrightarrow> ((\<exists>x. M x) \<longrightarrow> P)"
by (simp add: rall_def)

lemma rall_cong [cong]:
    "(!!x. M(x) ==> P(x) <-> P'(x)) ==> (rall M P) <-> (rall M P')"
by (simp add: rall_def)

lemma rexI [intro]: "[| P(x); M(x) |] ==> rex M P"
by (simp add: rex_def, blast)

lemma rev_rexI: "[| M(x);  P(x) |] ==> rex M P"
by blast

lemma rexCI: "[| rall M (\<lambda>x. ~P x) ==> P(a); M(a) |] ==> rex M P"
by blast

lemma rexE [elim]: "[| rex M P;  !!x. [| M(x); P(x) |] ==> Q |] ==> Q"
by (simp add: rex_def, blast)

lemma rex_triv [simp]: "(rex M (\<lambda>x. P)) \<longleftrightarrow> ((\<exists>x. M(x)) \<and> P)"
by (simp add: rex_def)

lemma rex_cong [cong]:
    "(!!x. M(x) ==> P(x) <-> P'(x)) ==> (rex M P) <-> (rex M P')"
by (simp add: rex_def cong: conj_cong)

lemma atomize_rall: "(!!x. M(x) ==> P(x)) == Trueprop (rall M P)"
by (simp add: rall_def atomize_all atomize_imp)


subsection \<open>Bounding quantification over a set\<close>

definition ball :: "'d \<Rightarrow> ('d \<Rightarrow> bool) \<Rightarrow> bool" where
  ball_def : "ball x P \<equiv> rall (\<lambda>a. a \<in> x) P" 
definition bex :: "'d \<Rightarrow> ('d \<Rightarrow> bool) \<Rightarrow> bool" where
  bex_def : "bex x P \<equiv> rex (\<lambda>a. a \<in> x) P"

abbreviation not_mem :: "['d, 'd] \<Rightarrow> bool"  (infixl \<open>\<notin>\<close> 50)  \<comment> \<open>negated membership relation\<close>
  where "x \<notin> y \<equiv> \<not> (x \<in> y)"

(*Lemmas taken from ZF/ZF_Base*)
lemma ballI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> P x) \<Longrightarrow> ball A P"
  by (simp add: ball_def)

lemma bspec [dest?]: "[| ball A P;  x\<in>A |] ==> P x"
  unfolding ball_def by auto

lemma rev_ballE [elim]:
    "[| ball A P;  x\<notin>A ==> Q;  P x ==> Q |] ==> Q"
  by (simp add: ball_def, blast)

lemma ballE: "[| ball A P;  P x ==> Q;  x\<notin>A \<Longrightarrow>  Q |] ==> Q"
  by auto

lemma ball_triv [simp]: "ball A (\<lambda>x. P) \<longleftrightarrow> ((\<exists>x. x\<in>A) \<longrightarrow> P)"
 by (simp add: ball_def)

lemma ball_cong [cong]:
 "[| A=A';  !!x. x\<in>A' ==> P x \<longleftrightarrow> P' x |] ==> (ball A P \<longleftrightarrow> ball A' P')"
  by (simp add: ball_def)

lemma bexI [intro]: "[| P x;  x\<in> A |] ==> bex A P "
  by (simp add: bex_def, blast)

lemma rev_bexI: "[| x\<in>A;  P x |] ==>  bex A P " by blast

lemma bexCI: "[| ball A  (\<lambda>x. ~P x) \<Longrightarrow> P a;  a\<in> A |] ==>  bex A P "
  by blast

lemma bexE [elim!]: 
  "[|  bex A P ;  !!x. [| x\<in>A; P x |] ==> Q |] ==> Q"
by (simp add: bex_def, blast)

lemma bex_triv [simp]: "bex A (\<lambda>x. P) \<longleftrightarrow> ((\<exists>x. x\<in>A) & P)"
by (simp add: bex_def)

lemma bex_cong [cong]:
    "[| A=A';  !!x. x\<in>A' ==> P x \<longleftrightarrow> P'(x) |]
     ==>  bex A P \<longleftrightarrow> bex A' P'"
  by (simp add: bex_def cong: conj_cong)

subsection \<open>Rules for the Set ownership relation\<close>

lemma set_iff : "Set x \<longleftrightarrow> x = \<emptyset> \<or> (\<exists>y. y \<in> x)"
  using set by auto

lemma setI  : "a \<in> x \<Longrightarrow> Set x" using set_iff by auto
lemma setE  : "Set x \<Longrightarrow> x = \<emptyset> \<or> (\<exists>y. y \<in> x)" using set_iff by auto


subsection \<open>Rules for the subset relation\<close>

lemma subset_iff : "x \<subseteq> y \<longleftrightarrow> Set x \<and> Set y \<and> (ball x (\<lambda>a. a \<in> y))"
  using subset_def by auto

lemma subset_set : "x \<subseteq> y \<Longrightarrow> Set x \<and> Set y" using subset_iff by auto
lemma subset_set1 : "x \<subseteq> y \<Longrightarrow> Set x" using subset_set by auto
lemma subset_set2 : "x \<subseteq> y \<Longrightarrow> Set y" using subset_set by auto

(*Lemmas taken from ZF/ZF_Base:*)

(*Added assumptions \<open>Set A\<close>, \<open>Set B\<close>*)
lemma subsetI [intro]: assumes "Set A" "Set B" shows
    "(!!x. x\<in>A ==> x\<in>B) ==> A \<subseteq> B"
  using assms subset_iff by auto
(*WAS: by (simp add: subset_def) *)

lemma subsetD [elim]: "[| A \<subseteq> B;  c\<in>A |] ==> c\<in>B"
  using subset_iff by auto
(*WAS: apply (unfold subset_def)
       apply (erule bspec, assumption)
       done
*)
lemma subsetCE [elim]:
    "[| A \<subseteq> B;  c\<notin>A ==> P;  c\<in>B ==> P |] ==> P"
  using subsetD by auto
(*WAS: by (simp add: subset_def, blast)*)

lemma rev_subsetD: "[| c\<in>A; A \<subseteq> B |] ==> c\<in>B"
by blast

lemma contra_subsetD: "[| A \<subseteq> B; c \<notin> B |] ==> c \<notin> A"
by blast

lemma rev_contra_subsetD: "[| c \<notin> B;  A \<subseteq> B |] ==> c \<notin> A"
by blast

(*Added assumption: \<open>Set A\<close>*)
lemma subset_refl : assumes "Set A" shows "A \<subseteq> A"
 using assms by blast
(*WAS: by blast*)

lemma subset_trans: "[| A \<subseteq> B;  B \<subseteq> C |] ==> A \<subseteq> C"
  by (simp add: subset_iff, auto)

(*WAS: by blast*)

declare subsetD [trans] rev_subsetD [trans] subset_trans [trans]

subsection \<open>Equality of sets\<close>

lemma subset_equal : assumes "Set x" "Set y" 
  shows "x = y \<longleftrightarrow> x \<subseteq> y \<and> y \<subseteq> x "
  using assms ext by auto

lemma equality_iff : assumes "Set x" "Set y"
  shows "x = y \<longleftrightarrow> (\<forall>a. a \<in> x \<longleftrightarrow> a \<in> y)"
  using assms ext by auto

(*Lemmas taken from ZF/ZF_Base:*)
lemma equalityI : "[| A \<subseteq> B;  B \<subseteq> A |] ==> A = B"
  using subset_set subset_equal by auto
(*WAS: by (rule extension [THEN iffD2], rule conjI) *)

(*Added assumptions: \<open>Set A\<close> \<open>Set B\<close>*)
lemma equality_iffI: assumes "Set A" "Set B" 
  shows "(!!x. x \<in> A \<longleftrightarrow> x \<in> B) \<Longrightarrow> A = B"
  using assms equalityI subsetI by blast

(*WAS: by (rule equalityI, blast+)*)

(*Replaced \<open>extension\<close> with \<open>subset_equal\<close>*)
lemmas equalityD1 = subset_equal [THEN iffD1, THEN conjunct1]
lemmas equalityD2 = subset_equal [THEN iffD1, THEN conjunct2]

(*Added assumptions: \<open>Set A\<close> \<open>Set B\<close>*)
lemma equalityE: assumes "Set A" "Set B" shows "[| A = B;  [| A \<subseteq> B; B \<subseteq> A |] ==> P |]  ==>  P"
  by (use equalityD1[OF assms] equalityD2[OF assms] in auto)
(*WAS: by (blast dest: equalityD1 equalityD2) *)

(*Added assumptions: \<open>Set A\<close> \<open>Set B\<close>*)
lemma equalityCE: assumes "Set A" "Set B" shows
    "[| A = B;  [| c\<in>A; c\<in>B |] ==> P;  [| c\<notin>A; c\<notin>B |] ==> P |]  ==>  P"
by (erule equalityE[OF assms], blast)
(*WAS: by (erule equalityE, blast)*)

subsection\<open>Rules for the empty set\<close>

lemma emp_set [simp] : "Set \<emptyset>" using set_iff by auto

(*Taken from ZF/ZF_Base*)
lemma not_mem_empty : "a \<notin> \<emptyset>"
  by (simp add: emp)
(*WAS: apply (cut_tac foundation)
       apply (best dest: equalityD2)
       done *)

lemmas emptyE [elim] = not_mem_empty [THEN notE]

(*Added assumption: \<open>Set A\<close>*)
lemma empty_subsetI [simp]: assumes "Set A" shows "\<emptyset> \<subseteq> A"
  using assms by auto
(*WAS: by blast*)

(*Added assumption: \<open>Set A\<close>*)
lemma equals0I: assumes "Set A" shows "[|!!y. y\<in>A ==> False |] ==> A=\<emptyset>"
  by (rule equality_iffI[OF assms emp_set], use not_mem_empty in auto)
(*WAS: by blast*)

lemma equals0D [dest]: "x = \<emptyset> \<Longrightarrow> a \<notin> x"
  by blast

declare sym [THEN equals0D, dest]

lemma not_emptyI: "a \<in> x ==> x \<noteq> \<emptyset>"
  by blast

(*Added assumption: \<open>Set A\<close>*)
lemma not_emptyE: assumes "Set A" 
  shows "[| A \<noteq> \<emptyset>;  !!x. x\<in>A ==> R |] ==> R"
  using setE[OF assms] by blast
(*WAS: by blast*)

subsection \<open>Corollaries of the Axiom of Union\<close>

lemma union_set : "Set x \<Longrightarrow> Set (\<Union> x)"
  using uni by auto

(*Added assumption: \<open>Set x\<close>*)
lemma union_iff : assumes "Set x" 
  shows "a \<in> \<Union> x \<longleftrightarrow> (bex x (\<lambda>y. a \<in> y))"
  using assms uni by auto
(*WAS: axiomatised then, declare union_iff [simp]*)

(*Added assumption: \<open>Set x\<close>*)
lemma unionI [intro]: assumes "Set x" 
  shows "\<lbrakk> y \<in> x;  a \<in> y \<rbrakk> \<Longrightarrow> a \<in> \<Union> x"
  by (simp add: union_iff[OF assms], blast)
(*WAS: by (simp, blast)*)

(*Added assumption: \<open>Set x\<close>*)
lemma unionE [elim]: assumes "Set x" 
  shows "\<lbrakk> a \<in> \<Union> x;  \<And>y. \<lbrakk> a \<in> y;  y \<in> x \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (simp add: union_iff[OF assms], blast)
(*WAS: by (simp, blast)*)

lemma union_emp : assumes "Set x" shows "a \<in> \<Union> x \<Longrightarrow> x \<noteq> \<emptyset>"
  using assms unionE not_emptyI by auto

subsection \<open>Rules for power sets\<close>

(*Added assumption: \<open>Set x\<close>*)
lemma pow_iff : assumes "Set x" shows "y \<in> \<P> x \<longleftrightarrow> y \<subseteq> x"
  using pow assms by auto
(*WAS: an axiom*)

(*Added assumption: \<open>Set x\<close>*)
lemma powI: "A \<subseteq> B \<Longrightarrow> A \<in> \<P> B"
  using subset_set2 pow_iff by auto
(*WAS: by (erule Pow_iff [THEN iffD2])*)

lemma powD: assumes "Set B" shows "A \<in> \<P> B \<Longrightarrow> A \<subseteq> B"
  using pow_iff[OF assms] by simp
(*WAS: by (erule Pow_iff [THEN iffD1]) *)

declare pow_iff 

lemmas pow_bottom = empty_subsetI [THEN powI]    \<comment> \<open>\<^term>\<open>\<emptyset> \<in> \<P> B\<close>\<close>
lemmas pow_top = subset_refl [THEN powI]         \<comment> \<open>\<^term>\<open>A \<in> \<P> A\<close>\<close>

lemma pow_set : "Set x \<Longrightarrow> Set (\<P> x)"
  using setI[OF pow_top] by simp

subsection \<open>Rules for von Neumann successor operation\<close>

thm suc
lemma vsucc_iff : assumes "Set x" 
  shows "y \<in> Succ x \<longleftrightarrow> (y \<in> x | y = x)"
  using assms suc by simp

lemma vsuccI1 : assumes "Set x"
  shows "y \<in> x \<Longrightarrow> y \<in> Succ x"
  using vsucc_iff[OF assms] by simp

lemma vsuccI2 : assumes "Set x"
  shows "x \<in> Succ x"
  using vsucc_iff[OF assms] by simp

lemma vsucc_set : assumes "Set x" 
  shows "Set (Succ x)"
  by (rule setI[OF vsuccI2[OF assms]])

lemma vsuccE : assumes "Set x" 
  shows "y \<in> Succ x \<Longrightarrow> (y \<in> x | y = x)"
  using vsucc_iff[OF assms] by simp

subsection \<open>Rules for the witness of Axiom of Infinity\<close>

thm inf
lemma inf0 : "\<emptyset> \<in> Inf" by (simp add: inf)
lemma inf_closed: "x \<in> Inf \<Longrightarrow> Succ x \<in> Inf" by (simp add: inf)
lemma inf_set : "Set Inf" by (rule setI[OF inf0])

subsection \<open>Rules for Replacement and derived operators\<close>

thm repl
lemma repl_set : "Set x \<Longrightarrow> Set (Repl P x)" using repl by auto

lemma repl_iff : assumes "Set x" "ball x (\<lambda>a. \<exists>\<^sub>\<le>\<^sub>1 b. P a b)"
  shows "b \<in> Repl P x \<longleftrightarrow> (bex x (\<lambda>a. P a b))"
  using repl assms unfolding ball_def rall_def bex_def rex_def by auto

definition Replace :: "[['d,'d] \<Rightarrow> bool, 'd] \<Rightarrow> 'd" where
  "Replace P x \<equiv> Repl (\<lambda>x y. (\<exists>!z. P x z) \<and> P x y) x"

lemma replace_set : "Set x \<Longrightarrow> Set (Replace P x)" 
  by (unfold Replace_def, rule repl_set)

lemma replace_iff : assumes "Set x" 
  shows "b \<in> Replace P x \<longleftrightarrow> (bex x (\<lambda>a. P a b \<and> (\<forall>c. P a c \<longrightarrow> c = b)))" 
proof -
  let ?Q = "(\<lambda>x y. (\<exists>!z. P x z) \<and> P x y)"
  have "ball x (\<lambda>a. \<exists>\<^sub>\<le>\<^sub>1 b. ?Q a b)" unfolding Uniq_def by auto
  hence "b \<in> Repl ?Q x \<longleftrightarrow> (bex x (\<lambda>a. ?Q a b))" by (rule repl_iff[OF assms])
  thus ?thesis unfolding Replace_def Ex1_def by auto
qed

lemma replaceI : "\<lbrakk> P a b ; a \<in> x ; \<And>c. P a c \<Longrightarrow> c = b \<rbrakk> \<Longrightarrow> b \<in> Replace P x"
  using replace_iff setI by blast

lemma replaceE: assumes "Set x"
  shows "\<lbrakk> b \<in> Replace P x ; 
          \<And>a. \<lbrakk>a \<in> x ; P a b ; \<forall>c. P a c \<longrightarrow> c = b \<rbrakk> \<Longrightarrow> R \<rbrakk>
          \<Longrightarrow> R"
  by (rule replace_iff [OF assms, THEN iffD1, THEN bexE], simp+)

lemma replaceE2 : assumes "Set x"
  shows "\<lbrakk> b \<in> Replace P x ; \<And>a. \<lbrakk>a \<in> x ; P a b \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (erule replaceE[OF assms], blast)

lemma replace_cong : assumes "Set x" "Set y" shows [cong]:
  "\<lbrakk>x = y ; \<And>a b. a \<in> y \<Longrightarrow> P a b \<longleftrightarrow> Q a b\<rbrakk> \<Longrightarrow> Replace P x = Replace Q y"
  by (rule equality_iffI[OF replace_set[OF assms(1)] 
                            replace_set[OF assms(2)]], 
      simp add: assms replace_iff)

definition RepFun :: "['d \<Rightarrow> 'd, 'd] \<Rightarrow> 'd" where
  "RepFun F x \<equiv> Replace (\<lambda>a b. b = F a) x"

lemma repfun_set : "Set x \<Longrightarrow> Set (RepFun F x)"
  unfolding RepFun_def by (rule replace_set)

lemma repfunI : "a \<in> x \<Longrightarrow>  F a \<in> RepFun F x"
  unfolding RepFun_def using replace_iff setI by auto

lemma repfun_eqI : "\<lbrakk>b = F a ; a \<in> x\<rbrakk> \<Longrightarrow> b \<in> RepFun F x"
  using repfunI by auto

lemma repfunE : assumes "Set x" 
  shows "\<lbrakk> b \<in> RepFun F x ; 
        \<And>a. \<lbrakk> a \<in> x ; b = F a \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add: RepFun_def replace_iff[OF assms], blast)

lemma repfun_cong : assumes "Set x" "Set y" 
  shows "\<lbrakk> x = y ; \<And>a. a \<in> y \<Longrightarrow> F a = G a \<rbrakk> \<Longrightarrow> RepFun F x = RepFun G y"
  unfolding RepFun_def using assms by simp

lemma repfun_iff  : assumes "Set x" 
  shows "b \<in> RepFun F x \<longleftrightarrow> (bex x (\<lambda>c. b = F c))"
  using repfun_eqI repfunE[OF assms] by blast

lemma repfun_union : assumes "Set x"
  shows "b \<in> \<Union> RepFun F x \<longleftrightarrow> (bex x (\<lambda>a. b \<in> F a))"
  by (simp add: union_iff[OF repfun_set[OF \<open>Set x\<close>]] bex_def rex_def
                repfun_iff[OF \<open>Set x\<close>], auto)

lemma repfun_union_subset : "a \<in> x \<Longrightarrow> y \<subseteq> F a \<Longrightarrow> y \<subseteq> \<Union> RepFun F x"
  using subset_iff repfun_union[OF setI] union_set[OF repfun_set[OF setI]] by auto

subsection \<open>Subset comprehension\<close>

definition Collect :: "['d \<Rightarrow> bool, 'd] \<Rightarrow> 'd" where
  "Collect P x \<equiv> Replace (\<lambda>a b. a = b \<and> P a) x"

lemma collect_set : "Set x \<Longrightarrow> Set (Collect P x)"
  unfolding Collect_def by (rule replace_set) 

lemma collect_iff : assumes "Set x" 
  shows "a \<in> Collect P x \<longleftrightarrow> a \<in> x \<and> P a"
  unfolding Collect_def by (simp add: replace_iff[OF assms], auto) 

lemma collectI : "\<lbrakk> a \<in> x ; P a \<rbrakk> \<Longrightarrow> a \<in> Collect P x"
  using setI collect_iff by auto

lemma collectE : assumes "Set x" 
  shows "\<lbrakk> a \<in> Collect P x ; \<lbrakk> a \<in> x ; P a \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  using collect_iff[OF assms] by auto

lemma collectD1 : assumes "Set x" shows "a \<in> Collect P x \<Longrightarrow> a \<in> x"
  using collectE[OF assms] by auto
lemma collectD2 : assumes "Set x" shows "a \<in> Collect P x \<Longrightarrow> P a"
  using collectE[OF assms] by auto

lemma Collect_cong [cong]: assumes "Set x" "Set y" shows [cong]: 
    "\<lbrakk> x = y;  \<And>a. a \<in> y \<Longrightarrow> P a \<longleftrightarrow> Q a \<rbrakk>
     \<Longrightarrow> Collect P x = Collect Q y"
  unfolding Collect_def using assms by simp


subsection \<open>Intersection of a set\<close>

definition Int :: "'d \<Rightarrow> 'd" (\<open>\<Inter> _\<close> [90] 90) where
  "\<Inter> x \<equiv> Collect (\<lambda>a. ball x (\<lambda>y. a \<in> y)) (Union x)"

lemma Int_set : "Set x \<Longrightarrow> Set (\<Inter> x)" 
  unfolding Int_def by (rule collect_set[OF union_set])

lemma Int_iff: assumes "Set x" 
  shows "a \<in> \<Inter> x \<longleftrightarrow> (ball x (\<lambda>y. a \<in> y)) \<and> x \<noteq> \<emptyset> "
proof
  assume "a \<in> \<Inter> x" hence "a \<in> \<Union> x" "ball x (\<lambda>y. a \<in> y)" unfolding Int_def
    using collectE[OF union_set[OF assms]] by auto
  thus "ball x (\<lambda>y. a \<in> y) \<and> x \<noteq> \<emptyset>" using union_emp[OF assms] by auto
next
  assume "ball x (\<lambda>y. a \<in> y) \<and> x \<noteq> \<emptyset>" hence ball:"ball x (\<lambda>y. a \<in> y)" and "x \<noteq> \<emptyset>" by simp_all
  from \<open>x \<noteq> \<emptyset>\<close> have "a \<in> \<Union> x"
  proof (rule not_emptyE[OF assms])
    fix y assume "y \<in> x" thus "a \<in> \<Union> x" 
      using ball unionI[OF assms] unfolding ball_def rall_def by auto
  qed
  thus "a \<in> \<Inter> x" unfolding Int_def using ball collectI by auto
qed

lemma IntI : assumes "Set x" shows "\<lbrakk> \<And>y. y \<in> x \<Longrightarrow> a \<in> y ; x \<noteq> \<emptyset> \<rbrakk> \<Longrightarrow> a \<in> \<Inter> x"
  using Int_iff[OF assms] by auto

lemma IntD : "\<lbrakk> a \<in> \<Inter> x ; y \<in> x \<rbrakk> \<Longrightarrow> a \<in> y"
  using setI Int_iff by auto

lemma IntE : assumes "Set x" shows "\<lbrakk> a \<in> \<Inter> x ; y \<notin> x \<Longrightarrow> R; a \<in> y \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  using Int_iff[OF assms] by auto


subsection \<open>Set difference\<close>

definition diff :: "['d, 'd] \<Rightarrow> 'd" (infixl \<open>-\<close> 65) where
  "x - y \<equiv> Collect (\<lambda>a. a \<notin> y) x"

lemma diff_set : assumes "Set x" shows "Set (x - y)"
  unfolding diff_def by (rule collect_set[OF assms])

lemma diff_iff : assumes "Set x" shows "a \<in> x - y \<longleftrightarrow> a \<in> x \<and> a \<notin> y"
  unfolding diff_def using collect_iff[OF assms] by simp

lemma diffI : "\<lbrakk> a \<in> x ; a \<notin> y \<rbrakk> \<Longrightarrow> a \<in> x - y"
  using setI diff_iff by simp

lemma diffD1 : assumes "Set x" shows "a \<in> x - y \<Longrightarrow> a \<in> x" using diff_iff[OF assms] by simp
lemma diffD2 : assumes "Set x" shows "a \<in> x - y \<Longrightarrow> a \<notin> y" using diff_iff[OF assms] by simp

lemma diffE : assumes "Set x" shows "\<lbrakk> a \<in> x - y ; \<lbrakk>a \<in> x ; a \<notin> y\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using diff_iff[OF assms] by simp

lemma diff_sub : "x \<subseteq> y \<Longrightarrow> x - z \<subseteq> y - z"
  using subset_iff diff_iff diff_set by auto

lemma diff_subset1 : shows "x \<subseteq> y \<Longrightarrow> a \<subseteq> (x - z) \<Longrightarrow> a \<subseteq> (y - z)"
  using subset_iff diff_iff diff_set by auto

lemma diff_subset2 : assumes "Set y" shows "x \<subseteq> (y - z) \<Longrightarrow> x \<subseteq> y"
  using subset_iff diff_iff[OF assms] assms by auto



lemma diff_emp : "\<emptyset> - x = \<emptyset>"
  using diff_iff[OF emp_set] equals0I[OF diff_set[OF emp_set]] by auto

subsection \<open>Unordered pairs; defined by replacement over \<P> (\<P> \<emptyset>)\<close>

abbreviation "\<phi> x y a b \<equiv> (a = \<emptyset> \<and> b = x) \<or> (a = \<P> \<emptyset> \<and> b = y)"

definition upair :: "'d \<Rightarrow> 'd \<Rightarrow> 'd" where
  "upair x y \<equiv> Replace (\<phi> x y) (\<P> (\<P> Emp))"

lemma upair_set : "Set (upair a b)"
  unfolding upair_def
  by (rule replace_set[OF pow_set[OF pow_set[OF emp_set]]])

lemma pow_emp_iff : "x \<in> \<P> \<emptyset> \<longleftrightarrow> x = \<emptyset>" unfolding pow_iff[OF emp_set]
proof
  assume "x \<subseteq> \<emptyset>" hence "Set x" "\<forall>a. a \<notin> x" using subset_iff by auto
  thus "x = \<emptyset>" using equals0I by blast
next
  assume "x = \<emptyset>" thus "x \<subseteq> \<emptyset>" using empty_subsetI[OF emp_set] by simp
qed

lemma pow_pow_emp_iff : "x \<in> \<P> (\<P> \<emptyset>) \<longleftrightarrow> (x = \<emptyset> | x = \<P> \<emptyset>)" unfolding pow_iff[OF pow_set[OF emp_set]]
proof
  assume "x \<subseteq> \<P> \<emptyset>" hence "Set x" using subset_set by auto (*and "\<forall>a. a \<in> x \<longrightarrow> a \<in> \<P> \<emptyset>" by auto*)
  hence "x = \<emptyset> | (\<exists>y. y \<in> x)" by (rule setE)
  thus "x = \<emptyset> | x = \<P> \<emptyset>"
  proof (rule, simp)
    assume "\<exists>y. y \<in> x" hence emp_x : "\<emptyset> \<in> x" using \<open>x \<subseteq> \<P> \<emptyset>\<close> pow_emp_iff by auto
    have "x = \<P> \<emptyset>" proof (rule equality_iffI[OF \<open>Set x\<close> pow_set[OF emp_set]])
      fix a show "a \<in> x \<longleftrightarrow> a \<in> \<P> \<emptyset>" using \<open>x \<subseteq> \<P> \<emptyset>\<close> \<open>\<emptyset> \<in> x\<close> pow_emp_iff by auto
    qed
    thus "x = \<emptyset> | x = \<P> \<emptyset>" by simp
  qed
next
  assume "x = \<emptyset> | x = \<P> \<emptyset>" thus "x \<subseteq> \<P> \<emptyset>" 
  proof
    assume "x = \<emptyset>" thus "x \<subseteq> \<P> \<emptyset>"
      using empty_subsetI[OF pow_set[OF emp_set]] by simp
  next
    assume "x = \<P> \<emptyset>" thus "x \<subseteq> \<P> \<emptyset>" 
      using subset_refl[OF pow_set[OF emp_set]] by simp
  qed
qed

lemma \<phi>_uniq : "\<phi> x y a b \<Longrightarrow> (\<forall>z. \<phi> x y a z \<longrightarrow> z = b)"
  using pow_emp_iff by blast

thm replace_iff[OF pow_set[OF pow_set[OF emp_set]]]
lemma upair_iff : "b \<in> upair x y \<longleftrightarrow> (b = x | b = y)"
  unfolding upair_def 
proof (rule, erule replaceE2[OF pow_set[OF pow_set[OF emp_set]]])
  fix a assume "a \<in> (\<P> \<P> \<emptyset>)" and "\<phi> x y a b"
  thus "(b = x | b = y)" using pow_pow_emp_iff by auto
next
  assume "(b = x | b = y)"
  thus "b \<in> Replace (\<phi> x y) (\<P> \<P> \<emptyset>)" 
  proof
    assume "b = x" show "b \<in> Replace (\<phi> x y) (\<P> \<P> \<emptyset>)"
    proof (rule replaceI)
      let ?a = "\<emptyset>" show "\<phi> x y ?a b" using \<open>b = x\<close> by simp
      show "\<emptyset> \<in> \<P> (\<P> \<emptyset>)" using pow_pow_emp_iff by simp
      show "\<And>c. \<phi> x y ?a c \<Longrightarrow> c = b" using \<phi>_uniq[OF `\<phi> x y ?a b`] by auto
    qed
  next
    assume "b = y" show "b \<in> Replace (\<phi> x y) (\<P> \<P> \<emptyset>)"
    proof (rule replaceI)
      let ?a = "\<P> \<emptyset>" show "\<phi> x y ?a b" using \<open>b = y\<close> by simp
      show "\<P> \<emptyset> \<in> \<P> (\<P> \<emptyset>)" using pow_pow_emp_iff by simp
      show "\<And>c. \<phi> x y ?a c \<Longrightarrow> c = b" using \<phi>_uniq[OF `\<phi> x y ?a b`] by auto
    qed
  qed
qed

lemma upairI1 : "a \<in> upair a b" using upair_iff by simp
lemma upairI2 : "b \<in> upair a b" using upair_iff by simp

lemma upairE : "\<lbrakk> a \<in> upair b c ; a=b \<Longrightarrow> P ; a=c \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" 
  by (simp add: upair_iff, blast)

subsection \<open>Singleton sets\<close>

definition sng :: "'d \<Rightarrow> 'd" where
  "sng x \<equiv> upair x x"

lemma sng_set : "Set (sng a)" unfolding sng_def by (rule upair_set)

lemma sng_iff : "a \<in> sng x \<longleftrightarrow> a = x"
  unfolding sng_def using upair_iff by auto

lemma sngI : "a \<in> sng a" using sng_iff by auto

lemma sngE : "\<lbrakk> a \<in> sng x ; a = x \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using sng_iff by auto



subsection \<open>Properties of very small sets\<close>


lemma upair_subset: "a \<in> x \<Longrightarrow> b \<in> x \<Longrightarrow> upair a b \<subseteq> x" using upair_iff by (auto intro: subsetI[OF upair_set setI])
lemma sng_subset: "a \<in> x \<Longrightarrow> sng a \<subseteq> x" unfolding sng_def using upair_subset by auto

lemma sng_eq_iff : "sng a = sng b \<longleftrightarrow> a=b"
  by (rule equality_iff[OF sng_set, OF sng_set, THEN cnf.iff_trans],
      use sng_iff in auto)

lemma upair_eq_iff : "(upair a b) = (upair c d) \<longleftrightarrow> ((a=c \<and> b=d) | (a=d \<and> b=c))"
proof (rule equality_iff[OF upair_set upair_set, THEN cnf.iff_trans], rule)
  assume eq:"\<forall>x. x \<in> upair a b \<longleftrightarrow> x \<in> upair c d"
  have "a = b | a \<noteq> b" by simp
  thus "a = c \<and> b = d \<or> a = d \<and> b = c"
  proof
    assume "a = b" hence "upair a b = sng a" unfolding sng_def by simp
    hence "c = a \<and> d = a" using eq upair_iff sng_iff by auto
    thus "a = c \<and> b = d \<or> a = d \<and> b = c" using \<open>a = b\<close> by auto
  next
    assume "a \<noteq> b"
    have "a \<in> upair c d" "b \<in> upair c d" using eq upairI1 upairI2 by auto
    thus "a = c \<and> b = d \<or> a = d \<and> b = c" using \<open>a\<noteq>b\<close> upair_iff by auto
  qed
next
  assume "a = c \<and> b = d \<or> a = d \<and> b = c" 
  thus "\<forall>x. (x \<in> upair a b) \<longleftrightarrow> (x \<in> upair c d)" using upair_iff by auto
qed


subsection \<open>Kuratowski ordered pairs\<close>

definition kpair :: "['d,'d] \<Rightarrow> 'd" where
  "kpair x y \<equiv> upair (upair x y) (upair x x)"

lemma kpair_iff : "kpair a b = kpair c d \<longleftrightarrow> a = c \<and> b = d" 
  using kpair_def upair_eq_iff by auto

lemma pair_inject : "kpair a b = kpair c d \<Longrightarrow> (a=c \<Longrightarrow> b=d \<Longrightarrow> R) \<Longrightarrow> R "
  using kpair_iff by auto

lemma pair_inject1 : "kpair a b = kpair c d \<Longrightarrow> a=c"
  by (auto elim: pair_inject)
lemma pair_inject2 : "kpair a b = kpair c d \<Longrightarrow> b=d"
  by (auto elim: pair_inject)

subsection \<open>Cartesian product\<close>

definition cprod :: "['d, 'd] \<Rightarrow> 'd" (infixr \<open>\<times>\<close> 80) where
  "x \<times> y \<equiv> \<Union> Replace (\<lambda>a z. z = Replace (\<lambda>b p. p = kpair a b) y) x"

lemma cprod_set : assumes "Set x"
  shows "Set (x \<times> y)" unfolding cprod_def 
  by (rule union_set[OF replace_set[OF assms]])

lemma cprod_iff : assumes "Set x" "Set y"
  shows "p \<in> x \<times> y \<longleftrightarrow> (\<exists>a b. p = kpair a b \<and> a \<in> x \<and> b \<in> y)" 
proof -  
  let ?R = "Replace (\<lambda>a z. z = Replace (\<lambda>b p. p = kpair a b) y) x"
  show ?thesis unfolding cprod_def
  proof (rule union_iff[OF replace_set[OF \<open>Set x\<close>], THEN cnf.iff_trans], rule)
    assume "bex ?R (\<lambda>a. p \<in> a)" then obtain r where "r \<in> ?R" "p \<in> r" by auto
    show "\<exists>a b. p = kpair a b \<and> a \<in> x \<and> b \<in> y"
    proof (rule replaceE2[OF \<open>Set x\<close> \<open>r \<in> ?R\<close>], rule)
      fix a assume "a \<in> x" "r = Replace (\<lambda>b p. p = kpair a b) y"
      hence "p \<in> Replace (\<lambda>b p. p = kpair a b) y" using \<open>p \<in> r\<close> by simp
      show "\<exists>b. p = kpair a b \<and> a \<in> x \<and> b \<in> y"
      proof (rule replaceE2[OF \<open>Set y\<close> \<open>p \<in> Replace (\<lambda>b p. p = kpair a b) y\<close>], rule)
        fix b assume "b \<in> y" "p = kpair a b" 
        thus "p = kpair a b \<and> a \<in> x \<and> b \<in> y" using \<open>a \<in> x\<close> by auto
      qed
    qed
  next
    assume "\<exists>a b. p = kpair a b \<and> a \<in> x \<and> b \<in> y"
    then obtain a b where "p = kpair a b" "a \<in> x" "b \<in> y" by auto
    hence r: "p \<in> Replace (\<lambda>b p. p = kpair a b) y" 
             "Replace (\<lambda>b p. p = kpair a b) y \<in> ?R" 
      by (auto intro: replaceI)
    thus "bex ?R (\<lambda>r. p \<in> r)" using r by auto
  qed
qed

lemma cprod_iff_pair : assumes "Set x" "Set y" 
  shows "kpair a b \<in> x \<times> y \<longleftrightarrow> a \<in> x \<and> b \<in> y" 
  using cprod_iff[OF assms] pair_inject by blast

lemma cprodI : "a \<in> x \<Longrightarrow> b \<in> y \<Longrightarrow> p = kpair a b \<Longrightarrow> p \<in> x \<times> y"
  using setI cprod_iff by auto

lemma cprodI_pair : "a \<in> x \<Longrightarrow> b \<in> y \<Longrightarrow> kpair a b \<in> x \<times> y"
  using setI cprod_iff_pair by auto

lemma cprodD1 : assumes "Set x" "Set y" shows "kpair a b \<in> x \<times> y \<Longrightarrow> a \<in> x" 
  using cprod_iff_pair[OF assms] by auto

lemma cprodD2 : assumes "Set x" "Set y" shows "kpair a b \<in> x \<times> y \<Longrightarrow> b \<in> y"
  using cprod_iff_pair[OF assms] by auto

lemma cprodE : assumes "Set x" "Set y" 
  shows "\<lbrakk> p \<in> x \<times> y ; \<And>a b. \<lbrakk> a \<in> x ; b \<in> y ; p = kpair a b \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using cprod_iff[OF assms] by auto   

lemma cprodE_pair : assumes "Set x" "Set y" 
  shows "\<lbrakk> kpair a b \<in> x \<times> y ; \<And>a b. \<lbrakk> a \<in> x ; b \<in> y \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using cprod_iff[OF assms] by auto   

lemma cprod_eq : "\<lbrakk> x=x' ; y=y' \<rbrakk> \<Longrightarrow> x\<times>y = x'\<times>y'" by auto

subsection \<open>Projection relations\<close>

definition fst :: "'d \<Rightarrow> 'd" (\<open>\<tau>\<close>) where
  "\<tau> p \<equiv> \<iota>' \<emptyset> (\<lambda>a. \<exists>b. p = kpair a b)"

definition snd :: "'d \<Rightarrow> 'd" (\<open>\<pi>\<close>) where
  "\<pi> p \<equiv> \<iota>' \<emptyset> (\<lambda>b. \<exists>a. p = kpair a b)"

lemma kpair_uniq1 : "p = kpair a b \<Longrightarrow> (\<exists>!a. (\<exists>b. p = kpair a b)) " 
  using kpair_iff by auto

lemma kpair_uniq2 : "p = kpair a b \<Longrightarrow> (\<exists>!b. (\<exists>a. p = kpair a b))" 
  using kpair_iff by auto 

lemma fst_eq [simp]: "\<tau> (kpair a b) = a" unfolding fst_def 
  by (rule the_def_eq', use kpair_uniq1 in auto)

lemma snd_eq [simp]: "\<pi> (kpair a b) = b" unfolding snd_def 
  by (rule the_def_eq', use kpair_uniq2 in auto)

lemma fst_set : assumes "Set x" "Set y" 
  shows "p \<in> x \<times> y \<Longrightarrow> \<tau> p \<in> x"
  by (rule cprodE[OF assms], use fst_eq in auto)

lemma snd_set : assumes "Set x" "Set y" 
  shows "p \<in> x \<times> y \<Longrightarrow> \<pi> p \<in> y"
  by (rule cprodE[OF assms], use snd_eq in auto)

lemma fst_snd_eq : assumes "Set x" "Set y" 
  shows "p \<in> x \<times> y \<Longrightarrow> kpair (\<tau> p) (\<pi> p) = p"
  by (rule cprodE[OF assms], use fst_eq snd_eq in auto)

subsection \<open>Binary union and intersection\<close>

definition un :: "['d,'d] \<Rightarrow> 'd" (infixl \<open>\<union>\<close> 90) where
  "x \<union> y \<equiv> \<Union> upair x y"

lemma un_set : "Set (x \<union> y)" unfolding un_def by (rule union_set[OF upair_set])

lemma un_iff : "a \<in> x \<union> y \<longleftrightarrow> (a \<in> x | a \<in> y)"
  unfolding un_def 
  by (simp add: union_iff[OF upair_set], 
      auto intro: upairI1 upairI2 elim: upairE)

lemma unI1 : "a \<in> x \<Longrightarrow> a \<in> x \<union> y" by (simp add: un_iff)
lemma unI2 : "b \<in> y \<Longrightarrow> b \<in> x \<union> y" by (simp add: un_iff)

lemma un_subset1 : assumes "Set x" shows "x \<subseteq> x \<union> y" using subsetI[OF assms un_set] unI1 by simp
lemma un_subset2 : assumes "Set y" shows "y \<subseteq> x \<union> y" using subsetI[OF assms un_set] unI2 by simp

lemma unE : "\<lbrakk> a \<in> x \<union> y ; a \<in> x \<Longrightarrow> P ; a \<in> y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add: un_iff, blast)

lemma unE' : "\<lbrakk> a \<in> x \<union> y ; a \<in> x \<Longrightarrow> P ; \<lbrakk> a \<in> y ; a \<notin> x \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add: un_iff, blast)

lemma unCI : "(a \<notin> y \<Longrightarrow> a \<in> x) \<Longrightarrow> a \<in> x \<union> y"
  by (simp add: un_iff, blast)


definition int :: "['d,'d] \<Rightarrow> 'd" (infixl \<open>\<inter>\<close> 90) where
  "x \<inter> y \<equiv> \<Inter> upair x y"

lemma int_iff : "a \<in> x \<inter> y \<longleftrightarrow> (a \<in> x \<and> a \<in> y)"
  unfolding int_def 
  by (simp add: Int_iff[OF upair_set], 
      blast intro: upairI1 upairI2 elim: upairE)

lemma intI : "\<lbrakk> a \<in> x ; a \<in> y \<rbrakk> \<Longrightarrow> a \<in> x \<inter> y"
  by (simp add: int_iff)

lemma intD1 : "a \<in> x \<inter> y \<Longrightarrow> a \<in> x" by (simp add: int_iff)  
lemma intD2 : "a \<in> x \<inter> y \<Longrightarrow> a \<in> y" by (simp add: int_iff)

lemma intE : "\<lbrakk> a \<in> x \<inter> y ; \<lbrakk> a \<in> x ; a \<in> y \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add: int_iff)

subsection \<open>Converting a \<lambda>-function to a set-function\<close>

text \<open>Perhaps consider doing this development in a locale,
      so that we can abstract from the representation of the ordered pair.\<close>

definition converse :: "'d \<Rightarrow> 'd"
  where "converse r \<equiv> Replace (\<lambda>p q. \<exists>a b. p = kpair a b \<and> q = kpair b a) r"

definition domain :: "'d \<Rightarrow> 'd" 
  where "domain r \<equiv> Replace (\<lambda>p x. (\<exists>y. p = kpair x y)) r"
    
definition range :: "'d \<Rightarrow> 'd" 
  where "range r \<equiv> domain (converse r)"

definition field :: "'d \<Rightarrow> 'd"
  where "field r \<equiv> domain r \<union> range r"

definition relation :: "'d \<Rightarrow> bool" 
  where "relation r \<equiv> ball r (\<lambda>p. \<exists>a b. p = kpair a b)"

definition func :: "'d \<Rightarrow> bool"  
  where "func f \<equiv> \<forall>a b c. kpair a b \<in> f \<and> kpair a c \<in> f \<longrightarrow> b = c"
  
definition Lambda :: "['d, 'd \<Rightarrow> 'd] \<Rightarrow> 'd" where
  lam_def : "Lambda A F \<equiv> RepFun (\<lambda>x. kpair x (F x)) A"

definition "apply" :: "['d, 'd] \<Rightarrow> 'd"  (infixl \<open>`\<close> 90) 
  where "f`a \<equiv> \<iota>' \<emptyset> (\<lambda>b. kpair a b \<in> f)"

definition image :: "['d,'d] \<Rightarrow> 'd"  (\<open>_[_]\<close> 90) 
  where image_def: "f[x] \<equiv> RepFun (\<lambda>a. f`a) x"

lemma image_domain : "(Lambda D F)[D] = RepFun F D"
  sorry
end
end