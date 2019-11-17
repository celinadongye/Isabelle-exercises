(*
    Original Author of Riddle: Tjark Weber
    Updates and additions by Jacques Fleuriot
*)

theory tut4sol imports Main begin 

(* Note that most of these can be proved in more than one way *)

lemma "(P \<longrightarrow>(Q\<longrightarrow>R))\<longrightarrow>((P\<longrightarrow>Q)\<longrightarrow>(P\<longrightarrow>R))"
proof (rule impI)+
  assume "P" "P \<longrightarrow> Q \<longrightarrow> R" then have qr: "Q \<longrightarrow> R"
    (* try sledgehammer here instead to see what it suggests *)
    by fast 
  assume "P" "P \<longrightarrow> Q" then have "Q" 
    by blast
  then show "R" using qr
    by blast 
qed

lemma "(\<forall>x. P x \<longrightarrow> Q)\<longrightarrow>(\<exists>x. P x\<longrightarrow>Q)"
proof 
  assume "\<forall>x. P x \<longrightarrow> Q" then have "P a \<longrightarrow> Q" ..
  then show "\<exists>x. P x\<longrightarrow>Q" ..
qed
lemma foo: assumes ex: "\<not>(\<exists>x. P x)" shows all: "\<forall>x. \<not>P x"
proof
  fix x 
  show  "\<not> P x"
  proof 
    assume "P x" then have "\<exists>x. P x" by (rule exI)
    then show False using ex by simp
  qed
qed

lemma foo2: assumes ex: "\<not>(\<exists>x. P x)" shows "\<forall>x. \<not>P x"
(* "safe" is a method that will not make any provable goal become unprovable. 
    It does not do any exI or spec/allE steps. You can use other methods instead *)
proof(safe)
  fix x
  assume "P x" then have "\<exists>x. P x" by (rule exI)
  then show False using ex
    by simp
qed

(* A proof showing the use of a raw proof block. More elegant proofs are possible. *)

lemma assumes n_all: "\<not>(\<forall>x. P x)" shows "\<exists>x. \<not>P x"
proof (rule ccontr)
  assume n_ex: "\<nexists>x. \<not> P x"  
  have "\<forall>x. P x" 
    proof - (* dash means don't apply any default ND steps *)
      {fix z   (* arbitrary z *)
        have "P z"
        proof (rule ccontr)
          assume "\<not> P z" then have "\<exists>x. \<not> P x" ..
          then show False using n_ex  by simp
        qed
      }
      then show ?thesis .. (* method ".." is one that can do straightforward ND steps but you could e.g. use simp instead*)
    qed
    then show False using n_all by simp
qed

(* Shorter proof of same theorem as above *)

lemma assumes n_all: "\<not>(\<forall>x. P x)" shows "\<exists>x. \<not>P x"
proof (rule ccontr)
  assume n_ex: "\<nexists>x. \<not> P x"     
  {fix x 
    have "P x" 
    proof (rule ccontr)
      assume "\<not> P x" then have "\<exists>x. \<not> P x" ..
      then show False using n_ex  by simp
    qed
  }
  then have "\<forall>x. P x" ..
  then show False using n_all by simp
qed


(* Another Proof using previous result *)
lemma assumes n_all: "\<not>(\<forall>x. P x)" shows "\<exists>x. \<not>P x"
proof (rule ccontr)
  assume "\<nexists>x. \<not> P x" 
  then have "\<forall>x. \<not>\<not>P x" by (rule foo)
  then have "\<forall>x. P x" by simp
  from n_all this show False by (rule notE)
qed

(* A possible proof, without named assumptions and goals. Other proofs are possible *)   

lemma "(R\<longrightarrow>P)\<longrightarrow>(((\<not>R \<or> P)\<longrightarrow>(Q\<longrightarrow>S))\<longrightarrow>(Q\<longrightarrow>S))"
proof (rule impI)+
  assume "R \<longrightarrow> P" "Q" "\<not> R \<or> P \<longrightarrow> Q \<longrightarrow> S"
  show "S"
  proof (cases)
    assume  "R" 
    then have "P" using `R \<longrightarrow> P` by blast 
    then have "\<not>R \<or> P" ..
    then have "Q \<longrightarrow> S" using `\<not> R \<or> P \<longrightarrow> Q \<longrightarrow> S` by blast 
    then show "S" using  `Q` by simp
  next
    assume notr: "\<not>R" 
    then have "\<not>R \<or> P" ..
    then have "Q \<longrightarrow> S" using `\<not> R \<or> P \<longrightarrow> Q \<longrightarrow> S` by blast 
    then show "S" using  `Q` by simp    
  qed
qed

(* Another proof of the above, without explicit use of cases *)
lemma "(R \<longrightarrow> P) \<longrightarrow> (((\<not>R \<or> P) \<longrightarrow> (Q \<longrightarrow> S)) \<longrightarrow> (Q \<longrightarrow> S))"
proof (rule impI, rule impI)
  assume a: "R \<longrightarrow> P" "\<not> R \<or> P \<longrightarrow> Q \<longrightarrow> S"
  { assume R 
    hence P using a(1) by (rule_tac mp) 
    hence "\<not> R \<or> P" by (rule disjI2)
  }
  moreover 
  { assume "\<not>R" 
    hence "\<not> R \<or> P" by (rule disjI1)
  }
  ultimately have "\<not> R \<or> P" by (rule_tac disjE, rule_tac excluded_middle)
  from this a(2) show "Q \<longrightarrow> S" by (rule_tac mp)
qed


text {* A Riddle: Rich Grandfather *}

text {*
  First prove the following formula, which is valid in classical predicate
  logic, informally with pen and paper.  Use case distinctions and/or proof by
  contradiction.

  "If every poor man has a rich father,
   then there is a rich man who has a rich grandfather"
*}


text {*
Proof
(1) We first show: "\<exists>x. rich x".
Proof by contradiction.
    Assume "\<not> (\<exists>x. rich x)"
      Then "\<forall>x. \<not> rich x" 
      We consider an arbitrary "y" with "\<not> rich y"
      Then "rich (father y)"

(2) Now we show the theorem. 
Proof by cases.  
    Case 1:  "rich (father (father x))" 
             We are done.
    Case 2: "\<not> rich (father (father x))" 
            Then "rich (father (father (father x))) 
            Also "rich (father x)"
            because otherwise "rich (father (father x))"
qed
*}

text {*
  Now prove the formula in Isabelle using a sequence of rule applications (i.e.\
  only using the methods rule, erule and assumption).
*}

theorem
  "\<forall>x. \<not> rich x \<longrightarrow> rich (father x) \<Longrightarrow>
  \<exists>x. rich (father (father x)) \<and> rich x"
apply (rule classical)
apply (rule exI)
apply (rule conjI)
  
  apply (rule classical)
  apply (rule allE) apply assumption
  apply (erule impE) apply assumption
  apply (erule notE) 
  apply (rule exI)
  apply (rule conjI) apply assumption
  apply (rule classical)
  apply (erule allE)
  apply (erule notE)
  apply (erule impE) apply assumption
  apply assumption

apply (rule classical)
apply (rule allE) apply assumption
apply (erule impE) apply assumption
apply (erule notE)
apply (rule exI)
apply (rule conjI) apply assumption
apply (rule classical)
apply (erule allE)
apply (erule notE)
apply (erule impE) apply assumption
apply assumption
done


text{* An alternative proof of the above that does not rely on meta variables and uses additional
       tactics/methods such as drule and cut_tac .Note the use of rule exCI too. 

       Note also that the order in which the subgoals are tackled are dictated by Isabelle but 
       there are ways of doing the proof in a way closer to the informal one e.g. using "prefer" 
       to change the order of the goals (although this makes the proof potentially more "brittle" 
       to changes in future versions of Isabelle *}

theorem
  "\<forall>x. \<not> rich x \<longrightarrow> rich (father x) \<Longrightarrow>
  \<exists>x. rich (father (father x)) \<and> rich x"
apply (subgoal_tac "\<exists>x. rich x")
apply (erule exE)
(* Tackling (2) first *)
apply (cut_tac P="rich (father(father x))" in excluded_middle)
apply (erule disjE)
(* Case 2 *)
apply (subgoal_tac "rich(father x)")
apply (drule_tac x="father(father x)" in spec)
apply (drule mp, assumption)
apply (rule_tac x="father x" in exI)
apply (rule conjI)
apply assumption
apply assumption
apply (rule ccontr)
apply (drule_tac x="father x" in spec)
apply (drule mp, assumption)
apply (erule notE, assumption)
(* Case 1*)
apply (rule_tac x=x in exI)
apply (rule conjI)
apply assumption
apply assumption
(* Tackling (1) now *)
apply (rule_tac a="father x" in exCI)
apply (drule_tac x=x in spec)
apply (drule_tac x=x in spec)
apply (drule mp, assumption)
apply assumption
done


text {*
  Here is a proof in Isar that resembles the informal reasoning above:
*}

theorem rich_grandfather: 
  "\<forall>x. \<not> rich x \<longrightarrow> rich (father x) 
   \<Longrightarrow> \<exists>x. rich x \<and> rich (father (father x))"
proof -
  assume a: "\<forall>x. \<not> rich x \<longrightarrow> rich (father x)"
  have "\<exists>x. rich x"
  proof (rule classical)
    fix y 
    assume "\<not> (\<exists>x. rich x)"
    then have "\<forall>x. \<not> rich x" by simp 
    then have "\<not> rich y" by simp
    with a have "rich (father y)" by simp
    then show ?thesis by rule
  qed
  then obtain x where x: "rich x" by auto
  show ?thesis
  proof cases
    assume "rich (father (father x))"
    with x show ?thesis by auto
  next
    assume b: "\<not> rich (father (father x))"
    with a have "rich (father (father (father x)))" by blast
    moreover have "rich (father x)" 
    proof (rule classical)
      assume "\<not> rich (father x)" 
      with a have "rich (father (father x))" by simp
      with b show ?thesis by contradiction 
    qed
    ultimately show ?thesis by auto
  qed
qed

text {*
  An slightly modified proof of the above, with a named assumption right from the beginning:
*}


theorem rich_grandfather2: 
  assumes a: "\<forall>x. \<not> rich x \<longrightarrow> rich (father x)" 
  shows "\<exists>x. rich x \<and> rich (father (father x))"
proof -
  have "\<exists>x. rich x"
  proof (rule classical)
    fix y 
    assume "\<not> (\<exists>x. rich x)"
    then have "\<forall>x. \<not> rich x" by simp 
    then have "\<not> rich y" by simp
    with a have "rich (father y)" by simp
    then show ?thesis by rule 
  qed
  then obtain x where x: "rich x" by auto
  show ?thesis
  proof cases
    assume "rich (father (father x))"
    with x show ?thesis by auto
  next
    assume b: "\<not> rich (father (father x))"
    with a have "rich (father (father (father x)))" by simp
    moreover have "rich (father x)" 
    proof (rule classical)
      assume "\<not> rich (father x)" 
      with a have "rich (father (father x))" by simp
      with b show ?thesis by contradiction 
    qed
    ultimately show ?thesis by auto
  qed
qed


 end 