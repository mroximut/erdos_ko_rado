theory EKR imports Main "HOL-Combinatorics.Permutations"
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

definition circular_equiv :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "\<sim>c" 50) where
  "xs \<sim>c ys \<longleftrightarrow> (length xs = length ys \<and> (\<exists>n. ys = rotate n xs))"

lemma c_reflexive:
  fixes xs :: "'a list"
  shows "xs \<sim>c xs"
  by (metis circular_equiv_def mod_0 rotate_id)

lemma c_transitive:
  fixes xs :: "'a list"
  fixes ys :: "'a list"
  fixes zs :: "'a list"
  assumes "xs \<sim>c ys \<and> ys \<sim>c zs"
  shows "xs \<sim>c zs"
  by (metis assms circular_equiv_def length_rotate rotate_rotate)
lemma c_symmetric:
  fixes xs :: "'a list"
  fixes ys :: "'a list"
  assumes "xs \<sim>c ys"
  shows "ys \<sim>c xs"
proof -
  (* 1. Unwrap definitions *)
  from assms obtain n where len: "length xs = length ys" and ys_def: "ys = rotate n xs"
    unfolding circular_equiv_def by blast

  (* 2. Construct the inverse rotation *)
  (* If we rotate ys by 'length xs - (n mod length xs)', we get xs back. *)
  (* Fortunately, metis can figure out the arithmetic if we give it the rotation laws. *)
  have "\<exists>k. xs = rotate k ys"
  proof (cases "xs = []")
    case True with ys_def show ?thesis by simp
  next
    case False
    (* The inverse rotation index *)
    let ?k = "length xs - (n mod length xs)"
    
    have "rotate ?k ys = rotate ?k (rotate n xs)" 
      using ys_def by simp
    also have "... = rotate (?k + n) xs" 
      by (simp add: rotate_rotate)
    also have "... = xs"
      (* This step relies on: rotate (L - (n%L) + n) xs = rotate (L + ...) xs = xs *)
      using False by (smt (verit, best) add.commute leD
        le_add_diff_inverse length_greater_0_conv
        mod_add_left_eq mod_less_divisor mod_self
        nat_le_linear rotate_id)
    finally show ?thesis by metis
  qed
  (* 3. Re-package into the definition *)
  thus ?thesis 
    using len unfolding circular_equiv_def by auto
qed

lemma equiv_circular: "equiv UNIV {(x, y). x \<sim>c y}"
  by (auto simp: equiv_def refl_on_def sym_def trans_def intro: c_reflexive c_symmetric c_transitive)

lemma circ_equivp: "equivp circular_equiv"
  by (metis c_reflexive c_symmetric c_transitive equivpI reflpI sympI transp_def)

quotient_type 'a circ_list = "'a list" / circular_equiv
  using circ_equivp .

lift_definition is_distinct_circ :: "'a circ_list \<Rightarrow> bool" is 
  "distinct"
  by (metis circular_equiv_def distinct_rotate)

typedef 'a circ_perm = "{c :: 'a circ_list. is_distinct_circ c}"
  morphisms rep_circ_perm abs_circ_perm
  by (rule_tac x="abs_circ_list []" in exI) (simp add: is_distinct_circ.abs_eq)


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
    
  show "card Star = (n - 1) choose (k - 1)"
  proof -
    let ?S' = "S - {x}"
    let ?Sub = "{B. B \<subseteq> ?S' \<and> card B = k - 1}"
    
    have "finite ?S'" using finite_S by simp
    have card_S': "card ?S' = n - 1" 
      using card_S `x \<in> S` finite_S by simp

    (* USE rule subset_antisym TO AVOID CONTEXT ERRORS *)
    have star_eq: "Star = (insert x) ` ?Sub"
    proof (rule subset_antisym)
      
      (* Direction 1: Left to Right *)
      show "Star \<subseteq> (insert x) ` ?Sub"
      proof (rule subsetI)
        fix A assume "A \<in> Star"
        hence "A \<subseteq> S" "card A = k" "x \<in> A"
          using Star_def all_k_subsets_def by auto
        
        let ?B = "A - {x}"
        have "?B \<subseteq> ?S'" using `A \<subseteq> S` by auto
        moreover have "card ?B = k - 1" 
          using `card A = k` `x \<in> A` finite_S `A \<subseteq> S` 
          by (simp add: card_Diff_singleton)
        ultimately show "A \<in> (insert x) ` ?Sub"
          using `x \<in> A` by (auto intro!: image_eqI[where x="?B"])
      qed
      
    next
      
      (* Direction 2: Right to Left *)
      show "(insert x) ` ?Sub \<subseteq> Star"
      proof (rule subsetI)
        (* We fix an element in the image and unpack it *)
        fix Y assume "Y \<in> (insert x) ` ?Sub"
        then obtain B where "Y = insert x B" and "B \<in> ?Sub" 
          by auto
          
        hence "B \<subseteq> S - {x}" and card_B: "card B = k - 1" by auto
        
        have "x \<notin> B" using `B \<subseteq> S - {x}` by auto
        have "finite B" using `B \<subseteq> S - {x}` finite_S by (auto intro: finite_subset)
        
        (* Now prove Y is in Star *)
        have "Y \<in> all_k_subsets"
        proof -
          have "insert x B \<subseteq> S" 
            using `B \<subseteq> S - {x}` `x \<in> S` by auto
          moreover have "card (insert x B) = k"
            using card_B `x \<notin> B` `finite B`
          by (metis Suc_pred' card_insert_disjoint
              ekr_context.k_pos
              ekr_context_axioms)
          ultimately show ?thesis 
            using all_k_subsets_def `Y = insert x B` by simp
        qed
        
        thus "Y \<in> Star"
          using Star_def `Y = insert x B` by simp
      qed
    qed

    (* 2. Cardinality Calculation using the named fact 'star_eq' *)
    have "card Star = card ((insert x) ` ?Sub)" 
      using star_eq by simp
    also have "... = card ?Sub"
    proof (rule card_image)
      show "inj_on (insert x) ?Sub"
        by (auto simp: inj_on_def)
    qed
    also have "... = (n - 1) choose (k - 1)"
      using n_subsets[OF `finite ?S'`, of "k - 1"] card_S' by simp
    finally show ?thesis .
  qed
qed

definition circular_permutations :: "'a set \<Rightarrow> ('a list set) set" where
  "circular_permutations S' = 
    {xs :: 'a list. set xs = S' \<and> distinct xs} // {(x, y). x \<sim>c y}"

lemma "card (circular_permutations S) = fact (n - 1)"
  sorry

definition meets :: "'a list \<Rightarrow> 'a set \<Rightarrow> bool" where
  "meets \<sigma> A \<longleftrightarrow> (\<exists>i. A = set (take k (rotate i \<sigma>)))"

lemma meets_rotation_invariant:
  assumes "meets \<sigma> A"
  shows "meets (rotate m \<sigma>) A"
proof -
  (* 1. Unwrap the definition to get the index 'j' *)
  from assms obtain j where "A = set (take k (rotate j \<sigma>))"
    unfolding meets_def by auto
  
  (* 2. We need to find an 'i' such that rotating 'rotate m \<sigma>' by 'i' 
        gives us the same list as 'rotate j \<sigma>'. 
        
        Logic: rotate i (rotate m \<sigma>) = rotate (i + m) \<sigma>.
        We can't just set i = j - m because j might be smaller than m.
        So we add (m * length \<sigma>) to j to make it big enough. 
  *)
  
  let ?len = "length \<sigma>"
  let ?big_j = "j + m * ?len" 
  let ?i = "?big_j - m"

  (* 3. Show that ?big_j acts exactly like j *)
  have "rotate ?big_j \<sigma> = rotate j \<sigma>"
    by (induct m) (auto simp: rotate_add) 
    (* or 'by (simp add: rotate_conv_mod)' if loaded *)

  (* 4. Show that our chosen i works *)
  have "rotate ?i (rotate m \<sigma>) = rotate (?i + m) \<sigma>"
    by (simp add: rotate_rotate)
  also have "... = rotate ?big_j \<sigma>"
  by (metis div_le_dividend
      le_add_diff_inverse2
      nonzero_mult_div_cancel_right
      rotate_length01 trans_le_add2
      zero_less_one_class.zero_le_one) (* Because ?big_j >= m, so ?big_j - m + m = ?big_j *)
  also have "... = rotate j \<sigma>"
    using `rotate ?big_j \<sigma> = rotate j \<sigma>` by simp
  finally have "rotate ?i (rotate m \<sigma>) = rotate j \<sigma>" .

  (* 5. Conclude that the definition of meets is satisfied *)
  then have "set (take k (rotate ?i (rotate m \<sigma>))) = A"
    using `A = set (take k (rotate j \<sigma>))` by simp
    
  then show ?thesis
    unfolding meets_def by blast
qed
  
definition \<S> :: "('a set \<times> 'a list set) set" where 
"\<S> = {(A, \<Sigma>). A \<in> \<F> \<and> (\<Sigma> \<in> circular_permutations S) \<and> (\<forall> \<sigma> \<in> \<Sigma>. meets \<sigma> A)}"

lemma katona_circle_claim:
  fixes \<sigma> :: "'a list"
  assumes "\<exists> \<Sigma> \<in> circular_permutations S. \<sigma> \<in> \<Sigma>"    
  shows "card {A \<in> \<F>. meets \<sigma> A} \<le> k"
proof -
  show ?thesis sorry
qed

lemma \<S>_upper_bound:
  shows "card \<S> \<le> (fact (n - 1)) * k"
sorry

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