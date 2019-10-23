theory isar
imports Main

begin
(* Propositional Logic *)
lemma "A \<longrightarrow> A"
proof
  assume a : "A"
  show "A" by (rule a) (*remove naming, replace by .*)
qed

lemma "A \<longrightarrow> (A \<and> A)"
proof 
  assume A
  show "A \<and> A" by (rule conjI) (* implicit proofs by assumption *)
qed

lemma "A \<longrightarrow> (A \<and> A)"
proof
  assume A
  show "A \<and> A" ..
qed





end