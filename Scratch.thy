theory Scratch
imports Main

begin

theorem A: "A \<longrightarrow> A \<or> B"
apply (rule impI)
apply (rule disjI1)
apply assumption
done

theorem B: "A \<or> B \<longrightarrow> B \<or> A"
apply (rule impI)
apply (erule disjE)
apply (rule disjI2)
apply assumption
apply (rule disjI1)
apply assumption
done


\<lbrakk> \<rbrakk>
\<not> 
\<longrightarrow>
\<longleftrightarrow>
\<rightarrow>
\<Rightarrow>

\<forall>
\<exists>
\<and> \<or> \<Longrightarrow>
\<rightleftharpoons>





end