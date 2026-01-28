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
  shows "card \<S> = card \<F> * (fact k) * (fact (n - k))"
proof -
  show ?thesis sorry
qed


theorem erdos_ko_rado_upper_bound:
  shows "card \<F> \<le> (n - 1) choose (k - 1)"
proof -
  have "card \<F> = (card \<S>) div ((fact k) * (fact (n - k)))" 
    using \<S>_equality by simp
  also have "... \<le> ((fact (n - 1)) * k) div ((fact k) * (fact (n - k)))"
    using \<S>_upper_bound using div_le_mono by blast 
  also have "... = fact (n - 1) div (fact (k - 1) * fact (n - k))"
    by (metis div_mult2_eq div_mult_self_is_m
        ekr_context.k_pos ekr_context_axioms
        fact_reduce of_nat_id)
  also have "... = fact (n - 1) div (fact (k - 1) * fact ((n-1) - (k-1)))"
    using ekr_context.k_pos ekr_context_axioms by fastforce
  also have "... = (n - 1) choose (k - 1)" using binomial_altdef_nat n_bound by simp
  finally show ?thesis .
qed


theorem erdos_ko_rado:
  shows "Max (card ` {F. F \<subseteq> all_k_subsets \<and> intersecting F}) = (n - 1) choose (k - 1)"
proof -
  (* Define the set of families and the target bound for clarity *)
  let ?Families = "{F. F \<subseteq> all_k_subsets \<and> intersecting F}"
  let ?Counts = "card ` ?Families"
  let ?bound = "(n - 1) choose (k - 1)"

  (* 1. Establish finiteness *)
  have "finite S" using finite_S .
  then have "finite all_k_subsets" unfolding all_k_subsets_def by auto
  then have fin_families: "finite ?Families" by simp
  then have fin_counts: "finite ?Counts" by simp

  (* 2. Establish the Upper Bound for all valid families *)
  have upper_bound_check: "\<forall>C \<in> ?Counts. C \<le> ?bound"
  proof
    fix C assume "C \<in> ?Counts"
    then obtain F where F_def: "F \<in> ?Families" and C_eq: "C = card F" by auto
    
    (* Interpret the locale for this specific family F *)
    interpret F_context: ekr_context n k S F
    proof
      show "finite S" by (rule finite_S)
      show "card S = n" by (rule card_S)
      show "0 < k" by (rule k_pos)
      show "2 * k \<le> n" by (rule n_bound)
      show "F \<subseteq> {A. A \<subseteq> S \<and> card A = k}" 
        using F_def unfolding all_k_subsets_def by auto
      show "intersecting F" using F_def by auto
    qed
    
    have "card F \<le> ?bound" using F_context.erdos_ko_rado_upper_bound .
    then show "C \<le> ?bound" using C_eq by simp
  qed

  (* 3. Establish Tightness (Existence of a family reaching the bound) *)
  have "S \<noteq> {}" using n_bound k_pos card_S by auto
  then obtain x where "x \<in> S" by blast
  let ?Star = "{A \<in> all_k_subsets. x \<in> A}"

  have star_in_families: "?Star \<in> ?Families" 
    using erdos_ko_rado_tight(1)[OF \<open>x \<in> S\<close>] by auto
    
  have star_card: "card ?Star = ?bound" 
    using erdos_ko_rado_tight(2)[OF \<open>x \<in> S\<close>] by simp

  have bound_in_counts: "?bound \<in> ?Counts"
    using star_in_families star_card
  using image_iff by fastforce

show ?thesis using Max_eqI bound_in_counts fin_counts upper_bound_check by auto 
qed
end

end