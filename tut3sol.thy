theory tut3sol 
imports
Main

begin

locale Geom =
  fixes on :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes line_on_two_pts: "a \<noteq> b \<Longrightarrow> \<exists>l. on a l \<and> on b l" 
  and line_on_two_pts_unique: "\<lbrakk> a \<noteq> b; on a l; on b l; on a m; on b m \<rbrakk> \<Longrightarrow> l = m"
  and two_points_on_line: "\<exists>a b. a \<noteq> b \<and> on a l \<and> on b l"
  and three_points_not_on_line: "\<exists>a b c. a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c \<and> 
                                    \<not> (\<exists>l. on a l \<and> on b l \<and> on c l)"
begin
  

(* Not asked for in tutorial: An alternative way of writing Axiom 4 *)  
lemma three_points_not_on_line_alt:
  "\<exists>a b c. a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c \<and> (\<forall>l. on a l \<and> on b l \<longrightarrow> \<not> on c l)"
proof -
  obtain a b c where distinct: "a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c" "\<not> (\<exists>l. on a l \<and> on b l \<and> on c l)" 
    using three_points_not_on_line by blast
  then have "\<forall>l. on a l \<and> on b l \<longrightarrow> \<not> on c l"
    by blast
  thus ?thesis using distinct by blast
qed        
  
lemma exists_pt_not_on_line: "\<exists>x. \<not> on x l"
proof -
   obtain a b c where l3: "\<not> (on a l \<and> on b l \<and> on c l)" using three_points_not_on_line by blast 
   thus ?thesis by blast 
qed

lemma two_lines_through_each_point: "\<exists>l m. on x l \<and> on x m \<and> l \<noteq> m"
proof -
  have "\<exists>z. z \<noteq> x" 
  proof (rule ccontr)
    from two_points_on_line obtain a b where ab: "(a::'p) \<noteq> b" by blast
    assume "\<nexists>z. z \<noteq> x" then have univ: "\<forall>z. z = x" by blast
    then have "a = x" "b = x" by auto
    then show False using ab by simp
  qed
  then obtain z where "z \<noteq> x" by blast
  then obtain l where xl: "on x l" and zl: "on z l" using line_on_two_pts by blast 
  obtain w where n_wl: "\<not> on w l" using exists_pt_not_on_line by blast
  obtain m where wm: "on x m" and zm: "on w m" using line_on_two_pts xl by force
  then have "l \<noteq> m" using n_wl by blast  
  thus ?thesis using wm xl by blast 
qed

(* Alternative proof of the above that uses Metis *)
lemma two_lines_through_each_point2: "\<exists>l m. on x l \<and> on x m \<and> l \<noteq> m"
proof -
  obtain z where "z \<noteq> x" using two_points_on_line by metis 
  then obtain l where xl: "on x l" and zl: "on z l" using line_on_two_pts by blast 
  obtain w where n_wl: "\<not> on w l" using exists_pt_not_on_line by blast
  obtain m where wm: "on x m" and zm: "on w m" using line_on_two_pts xl by force
  then have "l \<noteq> m" using n_wl by blast  
  thus ?thesis using wm xl by blast 
qed


lemma two_lines_through_each_point2: "\<exists>l m. on x l \<and> on x m \<and> l \<noteq> m"
proof -
  obtain z where "z \<noteq> x" using two_points_on_line by metis 
  then obtain l where xl: "on x l" and zl: "on z l" using line_on_two_pts by blast 
  obtain w where n_wl: "\<not> on w l" using exists_pt_not_on_line by blast
  obtain m where wm: "on x m" and zm: "on w m" using line_on_two_pts xl by force
  then have "l \<noteq> m" using n_wl by blast  
  thus ?thesis using wm xl by blast 
qed

lemma two_lines_unique_intersect_pt: 
   assumes lm: "l \<noteq> m" and "on x l" and "on x m" and "on y l" and "on y m" shows "x = y"
proof (rule ccontr)
   assume "x \<noteq> y" then have "l = m" using line_on_two_pts_unique assms by simp
   thus "False" using lm by simp
qed

end

(* Not asked for in tutorial: An extension of the locale with a new definition 
   using the "in" keyword *)

definition (in Geom) 
  collinear :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" 
  where "collinear a b c \<equiv> \<exists>l. on a l \<and> on b l \<and> on c l"


end