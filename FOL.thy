(*<*)

theory FOL
imports Main

begin

(*>*)

section {* Quantifier Rules in Action *}


text{* Here is one version of 
       the first example proof from the lecture on predicate logic *}

lemma "(\<forall>x. P x) \<longrightarrow> (\<exists>y. P y)"  
  apply (rule impI)
  apply (frule_tac x=a in spec)
  apply (rule_tac x=a in exI)
  by assumption

text {* This proof is rather unusual in that in the second step, it is
  sufficient to instantiate the universally quantified hypothesis with a new
  variable `a' which is unconstrained by any formulas in the sequent.

  More commonly we instantiate formulas with terms built with free
  variables already present in the sequent.  See the next couple of
  proofs. *}


text{* Here is the 2nd example proof from Lecture 5, with some
renaming of bound variables to make the formulas and proofs a little
clearer. This shows use of left and right forall introduction rules. *}

lemma "(\<forall>u. P u \<longrightarrow> Q u) \<and> (\<forall>v. P v) \<longrightarrow> (\<forall>w. Q w)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)  
  apply (erule_tac x="w" in allE)
  apply (erule_tac x="w" in allE)
  apply (erule impE)
  by assumption+


text {* An example showing use of left and right exists introduction rules *}

lemma " (\<exists>z. P z) \<and> Q \<longrightarrow> (\<exists>y. P y \<and> Q)"
apply (rule impI)
apply (erule conjE)
apply (erule exE)
apply (rule_tac x="z" in exI)
apply (rule conjI)
apply assumption+
done

text {* Here's a variation on the classical exists right introduction
rule exCI in the Isabelle library.  The advantage of this one is that
it doesn't introduce meta-variables into the sequent. *}

lemma exCIF: "((\<forall>x. \<not>(P x)) \<Longrightarrow> False) \<Longrightarrow> \<exists>x. P x"
by auto


text {* An example of the use of exCIF *}

lemma "\<not>( \<not> P a \<and> \<not> P b) \<longrightarrow> (\<exists>z. P z)"
apply (rule impI)
apply (rule exCIF)
apply (erule notE)
apply (rule conjI)
apply (erule_tac x="a" in allE)
apply assumption
apply (erule_tac x="b" in allE)
apply assumption
done

section {* Cheaters are losers *}

lemma Cheaters:
  "\<lbrakk>(\<exists>x. cheats x) \<longrightarrow> (\<forall>x. loses x);
    (\<forall>x. cheats x \<longrightarrow> loses x) \<longrightarrow> loses me\<rbrakk> \<Longrightarrow> loses me"
apply (erule mp)      (* View mp rule as special left intro rule for implies*)
apply (rule allI)
apply (rule impI)     (* From here on, is little choice in next rules *)
apply (erule impE)
apply (rule_tac x="x" in exI)
apply assumption
apply (erule_tac x="x" in allE)
apply assumption
done

section {* Use of meta-variables in Isabelle goals *}

text{* Meta-variables (also called schematic-variables in the Isabelle
documentation) in goals can be considered to be existentially
quantified at the sequent level.  As a proof proceeds, the proof is
free to substitute in more specialised terms for the meta-variables.

Often, the unification that happens when rules are applied will find
the needed meta-variable instantiations.  This saves having to enter
instantiating terms explicitly.  However using meta-variables in goals
and instantiating them with unification can be rather confusing when
first starting out.  All the Isabelle exercises and coursework can be
accomplished without exploiting them.

Below are some examples of proofs involving meta-variables.  
*}



text {* Example 1 again *}

lemma "(\<forall>x. P x) \<longrightarrow> (\<exists>y. P y)"
  apply (rule impI)
  apply (rule exI)
  apply (drule spec)
  apply assumption
done

text {* Example II again.  Here the meta-variables introduced are
actually functions taking as argument a variable universally
meta-quantified at the sequent level.  This indicates that any
instantiating term for the meta-variables can make use of the
universally quantified variable.  *}

lemma "(\<forall>x. P x \<longrightarrow> Q x) \<and> (\<forall>x. P x) \<longrightarrow> (\<forall>x. Q x)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)  
  apply (erule allE)
  apply (erule allE)
  apply (erule mp)
  by assumption

text {* The example again of how existential quantification
distributes over conjunction.  Once you have stepped through the
proof, try doing it again with the order of the exE and exI rules
swapped.  Why does the proof fail? *}

lemma " (\<exists>z. P z) \<and> Q \<longrightarrow> (\<exists>y. P y \<and> Q)"
apply (rule impI)
apply (erule conjE)
apply (erule exE)
apply (rule exI)
apply (rule conjI)
apply assumption+
done

  
end
         