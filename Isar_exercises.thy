theory Isar_exercises
imports Main
begin


(*==================Propositional Logic=========================*)
lemma "A \<longrightarrow> A"
proof (rule impI)
  assume a: "A"
  show "A" by (rule a)
qed

lemma "A \<longrightarrow> A"
(*Command proof automatically tries to select an introduction rule based on the goal and predefined
list of rules*)
proof
  assume a: "A"
  show "A" by (rule a)
qed

lemma "A \<longrightarrow> A \<and> A"
proof
  assume a:"A"
  show "A \<and> A" (* by (rule conjI) . *)
    by (simp add: a)
qed

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB: "A \<and> B"
  show "B \<and> A"
  proof (rule conjE[OF AB])
    assume "A" "B"
    show ?thesis (*?thesis always stands for current goal, show/have statement*)
      by (simp add: AB)
  qed
qed

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB: "A \<and> B"
  from AB show "B \<and> A"
  proof
    assume "A" "B"
    show ?thesis
      by (simp add: AB)
  qed
qed

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB: "A \<and> B"
  from this show "B \<and> A"
  proof
    assume "A" "B"
    show ?thesis
      using AB by auto
  qed
qed

(*Forward Reasoning*)
(*Proving intermediate propositions 'have' on the way to the final 'show', when we cannot bridge
the gap between the assumptions and the conclusion in one step.*)
lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB: "A \<and> B"
  from AB have a: "A"
    by simp
  from AB have b: "B"
    by simp
  from b a show "B \<and> A"
    by blast
qed

(*
lemma "\<not>(A \<and> B) \<longrightarrow> \<not>A \<or> \<not>B"
proof
  assume n: "\<not>(A \<and> B)"
  show "\<not>A \<or> \<not>B"
  proof (rule ccontr)
    assume nn: "\<not>(\<not>A \<and> B)"
    have "\<not>A"
    proof
      assume "A"
      have "\<not>B"
      proof
        assume "B"
        have "A \<and> B"
          by (simp add: \<open>A\<close> \<open>B\<close>)
        with n show False
          by simp
      qed
      hence "\<not>A \<or> \<not>B" by blast
      with nn show False
        sorry
    qed
*)

lemma assumes AB: "A \<or> B" shows "B \<or> A"
proof -
  from AB show ?thesis
  proof
    assume "A" show ?thesis
      by (simp add: \<open>A\<close>)
  next
    assume "B" show ?thesis
      by (simp add: \<open>B\<close>)
  qed
qed

(*==================Predicate Calculus=========================*)
lemma assumes P: "\<forall>x. P x" shows "\<forall>x. P(f x)"
(*fix introduces new local variables into a proof*)
(*pair fix-show corresponds to \<And>, universal quantifier at meta-level, 
like assume-show corresponds to \<Longrightarrow>*)
proof (*allI: (\<And>x. ?P x) \<Longrightarrow> \<forall>x. ?P x*)
  fix a 
  from P show "P(f a)" (*allE: \<lbrakk>\<forall>x. ?P x; ?P ?x \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R*)
    by simp
qed

lemma assumes Pf: "\<exists>x. P(f x)" shows "\<exists>y. P y"
proof -
(*obtain for existential quantifier. Similar to fix and assume.*)
  from Pf obtain a where "P(f a)" by blast
  then show "\<exists>y. P y" by blast
qed

lemma assumes ex: "\<exists>x. \<forall>y. P x y" shows "\<forall>y. \<exists>x. P x y"
proof
  fix y
  from ex obtain x where "\<forall>y. P x y" by blast
  then have "P x y" by blast
  then show "\<exists>x. P x y" by blast
qed

(*Cantor's theorem*)
theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
proof
  let ?S = "{x. x \<notin> f x}" (*let introduces an abbreviation for a term*)
  show "?S \<notin> range f"
  proof
    assume "?S \<in> range f"
    then obtain y where fy: "?S = f y" by blast
    show False
    proof cases (*starts a proof by cases. Note it remains implicit what the two cases are.
Merely expected that the two subproofs prove P \<Longrightarrow> ?thesis and \<not>P \<Longrightarrow> ?thesis for some P, in this order*)
      assume "y \<in> ?S"
      with fy show False by blast
    next
      assume "y \<notin> ?S"
      with fy show False by blast
    qed
  qed
qed

(*Detailed version of Cantor's theorem*)
theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
proof
  let ?S = "{x. x \<notin> f x}"
  show "?S \<notin> range f"
  proof
    assume "?S \<in> range f"
    then obtain y where fy: "?S = f y" by blast
    show False
    proof cases
      assume "y \<in> ?S"
      hence "y \<notin> f y" by simp
      hence "y \<notin> ?S" by (simp add: fy)
      thus False
        using \<open>y \<in> {x. x \<notin> f x}\<close> by blast 
    next
      assume "y \<notin> ?S"
      hence "y \<in> f y" by simp
      hence "y \<in> ?S" by (simp add: fy)
      thus False
        using \<open>y \<notin> {x. x \<notin> f x}\<close> by auto
    qed
  qed
qed

lemma "\<forall>x y. A x y \<and> B x y \<longrightarrow> C x y"
proof -
  have "\<And>x y. \<lbrakk>A x y; B x y\<rbrakk> \<Longrightarrow> C x y"
  proof -
    fix x y assume "A x y" "B x y"
    show "C x y" sorry
  qed
  thus ?thesis by blast
qed





end