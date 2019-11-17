theory Tut4Practice
imports Main
begin

lemma "(P \<longrightarrow> (Q \<longrightarrow> R)) \<longrightarrow> ((P \<longrightarrow> Q) \<longrightarrow> (P \<longrightarrow> R))"
proof (rule impI)+
  assume "P" "P \<longrightarrow> Q \<longrightarrow> R" then have qr: "Q \<longrightarrow> R"
    by blast
  assume "P" "P \<longrightarrow> Q" then have "Q"
    by blast
  then show "R" using qr
    by simp
qed

lemma "(\<forall>x. P x \<longrightarrow> Q) \<longrightarrow> (\<exists>x. P x \<longrightarrow> Q)"
proof 
  fix a
  assume "(\<forall>x. P x \<longrightarrow> Q)" then have pq: "P a \<longrightarrow> Q"
    by blast
  then show "(\<exists>x. P x \<longrightarrow> Q)"
    by blast
qed

lemma one: assumes ex:"(\<nexists>x. P x)" shows  all:"(\<forall>x. \<not>P x)"
proof
  fix x
  show "\<not> P x"
  proof
    assume "P x" then have "\<exists>x. P x"
      by auto
    then show False
      using ex by blast
  qed
qed

lemma assumes n_all: "\<not>(\<forall>x. P x)" shows "\<exists>x. \<not>P x"
proof (rule ccontr)
  assume "\<nexists>x. \<not>P x"
  then have "\<forall>x. \<not>\<not>P x" by (rule one)
  then have "\<forall>x. P x" by simp
  from n_all this show False
    by simp
qed




lemma "(R \<longrightarrow> P) \<longrightarrow> (((\<not>R \<or> P) \<longrightarrow> (Q \<longrightarrow> S)) \<longrightarrow> (Q \<longrightarrow> S))"
  oops

end