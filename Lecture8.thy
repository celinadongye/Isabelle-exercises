theory Lecture8
imports Main
begin
text{* An "abstract" notion of a finite graph *} 

locale finitegraph =
  fixes edges :: "('a\<times>'a)set" and vertices::"'a set" 
  assumes finite_vertex_set : "finite vertices"
  and is_graph : "(u, v) \<in> edges \<Longrightarrow>  u \<in> vertices \<and> v \<in> vertices" 
begin

(* Note that we can tell Isabelle's simplifier about 2 of the rules using [simp]. 
   More on this later in the course. *)
inductive walk:: "'a list \<Rightarrow> bool" where
Nil[simp] : "walk []"
|Singleton [simp] : "v \<in> vertices \<Longrightarrow> walk [v]"
|Cons : "(v,w)\<in>edges \<Longrightarrow> walk(w#vs) \<Longrightarrow> walk(v#w#vs)"


lemma walk_edge: assumes "(v,w) \<in> edges" shows "walk [v,w]"
proof -
  have "w \<in> vertices"
    using assms is_graph by presburger
  then show ?thesis
    by (simp add: assms walk.Cons)
qed


definition connected :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<rightarrow>\<^sup>*" 60) where
  "connected v w \<equiv> \<exists>xs. walk xs \<and> xs \<noteq> Nil \<and> hd xs = v \<and> last xs = w"

end

(* We can examine the definition of the locale and any lemma proven (whether explicitly or implicitly) 
   inside it. For example: *)

thm finitegraph_def
thm "finitegraph.walk_edge"
thm "finitegraph.walk.Singleton"
(* An induction principle was proven automatically for our finite graphs*)
thm "finitegraph.walk.induct"

text{* Extending the finite graphs locale to one about weighted finite graphs*} 

locale weighted_finitegraph = finitegraph + 
  fixes weight :: "('a \<times> 'a) \<Rightarrow> nat"
  assumes edges_weighted: "\<forall>e\<in>edges. \<exists>w. weight e = w"

thm finitegraph_def
thm weighted_finitegraph_def [unfolded weighted_finitegraph_axioms_def]

text{* We can define a concrete graph and show that it is an instance of our finite graph. In this 
   case, we just go for the graph with a single vertex "1" and an edge "(1,1)" to itself.
*}
interpretation singleton_finitegraph: finitegraph "{(1,1)}" "{1}"
proof 
 show "finite {1}" by simp 
 next fix u v assume "(u, v) \<in> {(1::'a, 1::'a)}" then show "u \<in> {1} \<and> v \<in> {1}" by blast
qed

(* We can "peek" into our instance: *)
term singleton_finitegraph.connected 
term singleton_finitegraph.walk

(* The definitions and theorems are now  available for the locale instance. For example: *)
thm singleton_finitegraph.connected_def
thm singleton_finitegraph.walk_edge
thm singleton_finitegraph.walk.Singleton
thm singleton_finitegraph.walk.induct


text{* We can make the concrete singleton_finitegraph an instance of the weighted_finitegraph locale 
   by providing a weight function e.g. the one that associates a weight "1" to any edge. 
*}

interpretation singleton_finitegraph: weighted_finitegraph "{(1,1)}" "{1}" "\<lambda>(u,v). 1"
by (unfold_locales) simp

(* The walk_edge theorem is still available *)
thm singleton_finitegraph.walk_edge
(* The weighted edges assumption instantiated with our single edge graph (yielding a trivial property)*)
thm singleton_finitegraph.edges_weighted

