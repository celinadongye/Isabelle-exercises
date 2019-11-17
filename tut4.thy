theory tut4
  imports Main

(* Isar, structured proofs *)

begin
(* Exercise 1 *)

(*- takes the assumptions and puts them in the proof*)
lemma "(P \<longrightarrow> (Q \<longrightarrow> R)) \<longrightarrow> ((P \<longrightarrow> Q) \<longrightarrow> (P \<longrightarrow> R))"
proof
  assume "P \<longrightarrow> (Q \<longrightarrow> R)"
  show "(P \<longrightarrow> Q) \<longrightarrow> (P \<longrightarrow> R)"
  proof
    assume "P \<longrightarrow> Q"
    show "P \<longrightarrow> R"
    proof
      assume P
      show R
      proof (rule mp)
        show "Q \<longrightarrow> R" by (rule mp) fact+
        show Q by (rule mp) fact+
      qed
    qed
  qed
qed

lemma "(P \<longrightarrow> (Q \<longrightarrow> R)) \<longrightarrow> ((P \<longrightarrow> Q) \<longrightarrow> (P \<longrightarrow> R))"
proof (rule impI)+
  assume "P" "P \<longrightarrow> Q \<longrightarrow> R" then have qr: "Q \<longrightarrow> R"
(*try sledgehammer *)
    by fast
  assume "P" "P \<longrightarrow> Q" then have "Q"
    by blast
  then show "R" using qr
    by blast
qed

lemma "(\<forall>x. P x \<longrightarrow> Q) \<longrightarrow> (\<exists>x. P x \<longrightarrow> Q)"
proof
  assume "\<forall>x. P x \<longrightarrow> Q"
  then have "P a \<longrightarrow> Q" by (erule_tac x="a" in allE)
  then show "(\<exists>x. P x \<longrightarrow> Q)" by (rule exI)
qed

lemma assumes 0: "(\<not>(\<exists>x. P x))" shows "(\<forall>x. \<not>P x)"
proof (rule allI, rule notI)
  fix x
  assume 0: "\<not>(\<exists>x. P x)" and forContra: "P x"
  have 1: "\<exists>x. P x" using forContra by (rule exI)
qed

(*method safe*)
(* -, do nothing, don't do natural deduction steps*)
lemma assumes n_all: "(\<not>(\<forall>x. P x))" shows "(\<exists>x. \<not>P x)"
proof (rule ccontr) (* can use classical too *)
  assume n_ex: "(\<nexists>x. \<not>P x)"
  have "\<forall>x. P x"
  proof -
    {fix x
      have "P x"
      proof (rule ccontr)
        assume "\<not> P x" then have "\<exists>x. \<not> P x" ..
        then show False using n_ex by simp
      qed
    }
    then show ?thesis ..
  qed
  then show False using n_all by simp
qed



lemma "(R \<longrightarrow> P) \<longrightarrow> (((\<not>R \<or> P) \<longrightarrow> (Q \<longrightarrow> S)) \<longrightarrow> (Q \<longrightarrow> S))"
proof
  assume 0: "R \<longrightarrow> P"
  show "((\<not>R \<or> P) \<longrightarrow> (Q \<longrightarrow> S)) \<longrightarrow> (Q \<longrightarrow> S)"
  proof
    assume 1: "\<not>R \<or> P"
    show "Q \<longrightarrow> S"


(* Exercise 2 *)
lemma "(\<forall>x. \<not>rich x \<longrightarrow> rich(father x)) \<longrightarrow> (\<exists>x. rich(father(father x)) \<and> rich x)"
proof cases
  assume "(\<forall>x. \<not>rich x \<longrightarrow> rich(father x))"
  show "(\<exists>x. rich(father(father x)) \<and> rich x)"
  next

qed

end