theory EKR imports Main
begin

definition intersecting :: "'a set set \<Rightarrow> bool" where
  "intersecting F \<longleftrightarrow> (\<forall>A \<in> F. \<forall>B \<in> F. A \<inter> B \<noteq> {})"

locale ekr_context =
  fixes n k :: nat
  fixes S :: "'a set"
  fixes \<F> :: "'a set set"
  assumes finite_S: "finite S"
  assumes card_S: "card S = n"
  assumes k_pos: "k > 0"
  assumes n_bound: "2 * k \<le> n"
  assumes F_family_of_k_subsets: "\<F> \<subseteq> {A. A \<subseteq> S \<and> card A = k}"
  assumes intersecting_F: "intersecting \<F>"
begin
definition all_k_subsets :: "'a set set" where
  "all_k_subsets = {A. A \<subseteq> S \<and> card A = k}"
end

context ekr_context
begin

lemma erdos_ko_rado_tight:
  fixes x :: 'a
  assumes "x \<in> S"
  defines "Star \<equiv> {A \<in> all_k_subsets. x \<in> A}"
  shows "intersecting Star" 
    and "card Star = (n - 1) choose (k - 1)"
proof -
  show "intersecting Star" 
  using Star_def intersecting_def
  by fastforce
  show "card Star = (n - 1) choose (k -1)" sorry
qed

definition is_circular_permutation_of :: "'a list \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_circular_permutation_of \<sigma> S' \<longleftrightarrow> distinct \<sigma> \<and> set \<sigma> = S'"

definition meets :: "'a list \<Rightarrow> 'a set \<Rightarrow> bool" where
  "meets \<sigma> A \<longleftrightarrow> (\<exists>i. A = set (take k (rotate i \<sigma>)))"

lemma katona_circle_claim:
  fixes \<sigma> :: "'a list"
  assumes "is_circular_permutation_of \<sigma> S"    
  shows "card {A \<in> \<F>. meets \<sigma> A} \<le> k"
proof -
  show ?thesis sorry
qed

definition \<S> :: "('a set \<times> 'a list) set" where 
"\<S> = {(A, \<sigma>). A \<in> \<F> \<and> is_circular_permutation_of \<sigma> S \<and> meets \<sigma> A}"

lemma \<S>_upper_bound:
  shows "card \<S> \<le> (fact (n - 1)) * k"
proof -
  show ?thesis sorry
qed

lemma \<S>_equality:
  shows "card \<S> = card \<F> * (fact k) * (fact (n - 1))"
proof -
  show ?thesis sorry
qed

lemma binomial_eq: 
  assumes "k \<le> n"
  shows "n choose k = (fact n) div ((fact k) * (fact (n - k)))"
  using assms
  using binomial_altdef_nat by blast 

theorem erdos_ko_rado_upper_bound:
  shows "card \<F> \<le> (n - 1) choose (k - 1)"
proof -
  have "card \<F> = (card \<S>) div ((fact k) * (fact (n - 1)))" 
    using \<S>_equality by simp
  also have "... \<le> ((fact (n - 1)) * k) div ((fact k) * (fact (n - 1)))"
    using \<S>_upper_bound using div_le_mono by blast  
  finally show ?thesis using binomial_eq sorry
qed

theorem erdos_ko_rado:
  shows "Max (card ` {F. F \<subseteq> all_k_subsets \<and> intersecting F}) = (n - 1) choose (k - 1)"
proof -
  show ?thesis sorry
qed
end

end