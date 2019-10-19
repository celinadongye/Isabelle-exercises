theory Lecture8
imports Main

begin
text{* An "abstract" notion of a finite graph *}

locale finitegraph =
  fixes edges :: "('a \<times> 'a)set" and vertices :: "'a set"
  assumes finite_vertex_set : "finite vertices"
    and is_graph : "(u, v) \<in> edges \<Longrightarrow> u \<in> vertices \<and> v \<in> vertices"

begin

(* We can tell Isabelle's simplifier about 2 of the rules using [simp] *)
inductive walk :: "'a list \<Rightarrow> bool" where
Nil[simp] : "walk []"
|Singleton : "v \<in> vertices \<Longrightarrow>  walk [v]"
|Cons : "(v,w) \<in> edges \<Longrightarrow> walk(w#vs) \<Longrightarrow> walk(v#w#vs)"

lemma walk_edge: assumes "(v,w) \<in> edges" shows "walk [v,w]"
proof -
  have "w \<in> vertices"
    using assms is_graph by presburger
  then show ?thesis
    by (simp add: assms walk.Cons)
qed
 

end
