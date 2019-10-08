theory tut2
imports Main

begin
(*Exercise 2*)
lemma "(\<forall>x. P x \<longrightarrow> Q) \<longrightarrow> (\<exists>x. P x \<longrightarrow> Q)"
  apply (rule impI)
  apply (erule allE)
  apply (rule exI)
  apply assumption
  done

lemma "(\<not>(\<exists> x. P x)) \<longrightarrow> (\<forall> x. \<not>P x)"
  apply (rule impI)
  apply (rule allI)
  apply (rule notI)
  apply (erule notE)
  apply (rule exI)
  apply assumption
  done

lemma "\<not>(\<forall>x. P x) \<longrightarrow> (\<exists>x. \<not>P x)"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule allI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule exI)
  apply assumption
  done

end