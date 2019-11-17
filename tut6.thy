theory tut6
imports Main
begin


datatype 'a TREE = LEAF 'a | NODE 'a "'a TREE" "'a TREE"

primrec MIRROR :: "'a TREE \<Rightarrow> 'a TREE" where
"MIRROR (LEAF x) = LEAF x" |
"MIRROR (NODE x left right) = NODE x (MIRROR right) (MIRROR left)"

thm TREE.induct

lemma "MIRROR(MIRROR t) = t"
proof (induction t)
  case LEAF
  then show ?case by simp
next
  case (NODE x left right)
  then show ?case by simp
qed

end