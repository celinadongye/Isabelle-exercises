theory book imports Main

begin

lemma conj_swap1: "P \<and> Q \<Longrightarrow> Q \<and> P"
  apply (rule conjI)
   apply (erule conjE)
   apply assumption
  apply (erule conjE)
  apply assumption
  done

lemma conj_swap2: "P \<and> Q \<Longrightarrow> Q \<and> P"
  apply (rule conjI)
   apply (drule conjunct2)
   apply assumption
  apply (drule conjunct1)
  apply assumption
  done

lemma imp_uncurry1: "P \<longrightarrow> (Q \<longrightarrow> R) \<Longrightarrow> P \<and> Q \<longrightarrow> R"
  apply (rule impI)
  apply (erule impE)
   apply (erule conjE)
   apply assumption
  apply (erule impE)
   apply (erule conjE)
   apply assumption+
  done

lemma imp_uncurry2: "P \<longrightarrow> (Q \<longrightarrow> R) \<Longrightarrow> P \<and> Q \<longrightarrow> R"
  apply (rule impI)
  apply (erule conjE)
  apply (drule mp)
   apply assumption
  apply (drule mp)
   apply assumption+
  done

lemma imp_uncurry3: "P \<longrightarrow> (Q \<longrightarrow> R) \<Longrightarrow> P \<and> Q \<longrightarrow> R"
  apply (rule impI)
  apply (erule conjE)
  apply (drule mp)
   apply assumption
  by (drule mp)

lemma "\<lbrakk> \<not>(P \<longrightarrow> Q); \<not>(R \<longrightarrow> Q) \<rbrakk> \<Longrightarrow> R"
  apply (erule_tac Q="R\<longrightarrow>Q" in contrapos_np)
  apply (intro impI) (* rule impI works too *)
  by (erule notE)

lemma "(P \<and> Q) \<and> R \<Longrightarrow> P \<or> (Q \<and> R)"
  apply (rule disjCI)
  apply (elim conjE disjE) (* rule conjE, rule disjE *)
  by (erule contrapos_np, rule conjI)
 (* apply assumption *)

end