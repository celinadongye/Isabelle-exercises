theory Lecture14
imports Main
begin


primrec myappend :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"myappend Nil ys = ys" |
"myappend (Cons x xs) ys = Cons x (myappend xs ys)"

lemma  "myappend xs (myappend ys zs) = myappend (myappend xs ys) zs"
apply (induct xs)
apply simp
apply simp
done

lemma  myappend_assoc: "myappend xs (myappend ys zs) = myappend (myappend xs ys) zs"
proof (induction xs)
  case Nil then show ?case by simp
next
  case (Cons x xs) then show ?case by simp
qed

lemma myappend_Nil: "myappend xs Nil = xs"
proof (induction xs)
  case Nil thus ?case  by simp
next 
  case (Cons x xs) thus ?case by simp
qed


primrec myreverse :: "'a list \<Rightarrow> 'a list" where
"myreverse Nil = Nil" |
"myreverse (Cons x xs) = myappend (myreverse xs) (Cons x Nil)"

lemma myreverse_myreverse: "myreverse(myreverse xs) = xs"
apply (induct xs)
apply simp
apply simp
(* stuck: need to speculate a lemma *)
oops


lemma speculated_myreverse: 
  "myreverse(myappend xs ys) = myappend (myreverse ys) (myreverse xs)"
proof (induction xs)
  case Nil then show ?case by (simp add: myappend_Nil) 
next
  case (Cons x xs) then show ?case by (simp add:myappend_assoc)
qed

(* A detailed proof to match the one given in the lecture *)

lemma myreverse_myreverse: "myreverse(myreverse xs) = xs"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs) 
  then have "myreverse (myreverse (x # xs)) = myreverse(myappend (myreverse xs) (Cons x Nil))" 
       by simp
  moreover have "\<dots> = myappend (Cons x Nil) (myreverse(myreverse xs))"
      by (simp add: speculated_myreverse) 
  moreover have "\<dots> = Cons x (myappend Nil (myreverse(myreverse xs)))"
      by simp
  moreover have "\<dots> = Cons x (myreverse(myreverse xs))" 
      by simp
  moreover have "\<dots> = Cons x xs" using Cons.hyps by blast 
  ultimately show ?case by simp
qed

(* Simpler proof -- as one would normally do it*)
lemma myreverse_myreverse2: "myreverse(myreverse xs) = xs"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs) thus ?case by (simp add: speculated_myreverse) 
qed

end