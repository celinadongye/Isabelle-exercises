theory tut3
imports Main

begin
(*Exercise 2*)
locale geometry =
  fixes on :: 'point \<Rightarrow> 'line \<Rightarrow> bool
  assumes line_exs: "x \<noteq> y \<Rightarrow> \<exists>l. on x l \<and> on y l"
  assumes line_eq: "\<exists>x y. x \<noteq> y \<and> on x l \<and> on y l"
  assumes line_points: "\<exists>x y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z \<and> \<forall>l. \<not>(on x l \<and> on y l \<and> on z l)"

begin
(*Not all points lie on the same line*)
lemma a: "\<forall>l. \<exists>p. \<not>on p l"
  apply (rule allI)
  oops

(*There exist at least two lines through each point*)
lemma b: "\<exists>l1 l2. \<forall>p. on p l1 \<and> on p l2 "
  oops
(*Two lines cannot intersect in more than one point*)

end

end