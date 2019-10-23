theory Isar_Demo
imports Main
begin

section{* An introductory example *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by(simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

text{* A bit shorter: *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  from 1 show "False" by blast
qed

subsection{* this, then, hence and thus *}

text{* Avoid labels, use this: *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  from this show "False" by blast
qed

text{* then = from this *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  then have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then show "False" by blast
qed

text{* hence = then have, thus = then show *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  thus "False" by blast
qed


subsection{* Structured statements: fixes, assumes, shows *}

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -  (* no automatic proof step! *)
  have "\<exists> a. {x. x \<notin> f x} = f a" using s
    by(auto simp: surj_def)
  thus "False" by blast
qed


section{* Proof patterns *}

lemma "P \<longleftrightarrow> Q"
proof
  assume "P"
  show "Q" sorry
next
  assume "Q"
  show "P" sorry
qed

lemma "A = (B::'a set)"
proof
  show "A \<subseteq> B" sorry
next
  show "B \<subseteq> A" sorry
qed

lemma "A \<subseteq> B"
proof
  fix a
  assume "a \<in> A"
  show "a \<in> B" sorry
qed

text{* Contradiction *}

lemma P
proof (rule ccontr)
  assume "\<not>P"
  show "False" sorry
qed

text{* Case distinction *}

lemma "R"
proof cases
  assume "P"
  show "R" sorry
next
  assume "\<not> P"
  show "R" sorry
qed

lemma "R"
proof -
  have "P \<or> Q" sorry
  then show "R"
  proof
    assume "P"
    show "R" sorry
  next
    assume "Q"
    show "R" sorry
  qed
qed


text{* obtain example *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus "False" by blast
qed


text{* Interactive exercise: *}

lemma assumes "EX x. ALL y. P x y" shows "ALL y. EX x. P x y"
oops (* solution at the bottom *)


section{* Streamlining proofs *}

subsection{* Pattern matching and ?-variables *}

text{* Show EX *}

lemma "EX xs. length xs = 0" (is "EX xs. ?P xs")
proof
  show "?P([])" by simp
qed

text{* Multiple EX easier with forward proof: *}

lemma "EX x y :: int. x < z & z < y" (is "EX x y. ?P x y")
proof -
  have "?P (z - 1) (z + 1)" by arith
  thus ?thesis by blast
qed


subsection{* Quoting facts: *}

lemma assumes "x < (0::int)" shows "x*x > 0"
proof -
  from `x<0` show ?thesis by(metis mult_neg_neg)
qed


subsection {* Example: Top Down Proof Development *}

text{* The key idea: case distinction on length: *}

lemma "(EX ys zs. xs = ys @ zs \<and> length ys = length zs) |
  (EX ys zs. xs = ys @ zs & length ys = length zs + 1)"
proof cases
  assume "EX n. length xs = n+n"
  show ?thesis sorry
next
  assume "\<not> (EX n. length xs = n+n)"
  show ?thesis sorry
qed

text{* A proof skeleton: *}

lemma "(EX ys zs. xs = ys @ zs \<and> length ys = length zs) |
  (EX ys zs. xs = ys @ zs & length ys = length zs + 1)"
proof cases
  assume "EX n. length xs = n+n"
  then obtain n where "length xs = n+n" by blast
  let ?ys = "take n xs"
  let ?zs = "take n (drop n xs)"
  have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs" sorry
  thus ?thesis by blast
next
  assume "\<not> (EX n. length xs = n+n)"
  then obtain n where "length xs = Suc(n+n)" sorry
  let ?ys = "take (Suc n) xs"
  let ?zs = "take n (drop (Suc n) xs)"
  have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs + 1" sorry
  then show ?thesis by blast
qed

text{* The complete proof: *}

lemma "(EX ys zs. xs = ys @ zs \<and> length ys = length zs) |
  (EX ys zs. xs = ys @ zs & length ys = length zs + 1)"
proof cases
  assume "EX n. length xs = n+n"
  then obtain n where "length xs = n+n" by blast
  let ?ys = "take n xs"
  let ?zs = "take n (drop n xs)"
  have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs"
    by (simp add: `length xs = n + n`)
  thus ?thesis by blast
next
  assume "\<not> (EX n. length xs = n+n)"
  hence "EX n. length xs = Suc(n+n)" by arith
  then obtain n where l: "length xs = Suc(n+n)" by blast
  let ?ys = "take (Suc n) xs"
  let ?zs = "take n (drop (Suc n) xs)"
  have "xs = ?ys @ ?zs \<and> length ?ys = length ?zs + 1" by (simp add: l)
  thus ?thesis by blast
qed


subsection {* moreover *}

lemma assumes "A \<and> B" shows "B \<and> A"
proof -
  from `A \<and> B` have "A" by auto
  moreover
  from `A \<and> B` have "B" by auto
  ultimately show "B \<and> A" by auto
qed


subsection{* Raw proof blocks *}

lemma fixes k :: int assumes "k dvd (n+k)" shows "k dvd n"
proof -
  { fix a assume a: "n+k = k*a"
    have "EX b. n = k*b"
    proof
      show "n = k*(a - 1)" using a by(simp add: algebra_simps)
    qed }
  with assms show ?thesis by (auto simp add: dvd_def)
qed


text{* Solution to interactive exercise: *}

lemma assumes "EX x. ALL y. P x y" shows "ALL y. EX x. P x y"
proof
  fix b
  from assms obtain a where 0: "ALL y. P a y" by blast
  show "EX x. P x b"
  proof
    show "P a b" using 0 by blast
  qed
qed

end