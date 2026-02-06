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

lemma distinct_list_of_S:
  obtains xs0 where "set xs0 = S" "distinct xs0" "length xs0 = n"
proof -
  (* 1. Use the standard library theorem to get a distinct list from a finite set *)
  obtain xs0 where xs0_props: "set xs0 = S" "distinct xs0"
    using finite_distinct_list[OF finite_S] by blast

  (* 2. Prove the length must be n using the cardinality of S *)
  have "length xs0 = card (set xs0)"
    using distinct_card[OF xs0_props(2)] by simp
  also have "... = card S"
    using xs0_props(1) by simp
  also have "... = n"
    using card_S by simp
  finally have "length xs0 = n" .

  (* 3. Apply the properties to the goal *)
  then show ?thesis
    using xs0_props that by blast
qed

lemma permutations_to_list_bijection:
  assumes "set xs0 = S" "distinct xs0"
  shows "bij_betw (\<lambda>p. map p xs0) {p. p permutes S} {xs. set xs = S \<and> distinct xs}"
proof -
  (* Define the domain and codomain sets for clarity *)
  let ?P = "{p. p permutes S}"
  let ?L = "{xs. set xs = S \<and> distinct xs}"
  let ?f = "\<lambda>p. map p xs0"

  (* We need the length of xs0 for indexing arguments *)
  have len_xs0: "length xs0 = n"
    using assms card_S distinct_card by force

  show "bij_betw ?f ?P ?L"
    unfolding bij_betw_def
  proof (intro conjI)

    (* 1. Proof of Injectivity *)
    show "inj_on ?f ?P"
    proof (rule inj_onI)
      fix p q
      assume p: "p \<in> ?P" and q: "q \<in> ?P"
      assume eq: "?f p = ?f q"

      (* Permutations are functions, so we prove equality pointwise *)
      have "\<forall>x. p x = q x"
      proof
        fix x
        show "p x = q x"
        proof (cases "x \<in> S")
          case True
          (* If x is in S, it's at some index in xs0 *)
          then obtain i where "i < length xs0" "xs0 ! i = x"
            using assms(1) by (metis in_set_conv_nth)

          (* The mapped lists are equal at that index *)
          moreover from eq have "map p xs0 ! i = map q xs0 ! i"
            by argo

          (* Therefore the function values are equal *)
          ultimately show ?thesis
            using nth_map[of i xs0 p] nth_map[of i xs0 q] by simp
        next
          case False
          (* If x is not in S, permutes fixes it by definition *)
          then show ?thesis
            using p q permutes_not_in
          by (metis mem_Collect_eq)
        qed
      qed
      then show "p = q" by (simp add: fun_eq_iff)
    qed

    (* 2. Proof of Surjectivity *)
    show "?f ` ?P = ?L"
    proof (rule subset_antisym)

      (* Direction A: Mapping a permutation creates a valid distinct list *)
      show "?f ` ?P \<subseteq> ?L"
      proof
        fix ys assume "ys \<in> ?f ` ?P"
        then obtain p where p: "p \<in> ?P" and ys: "ys = map p xs0" by auto

        have "set ys = p ` S"
          using ys assms(1) by simp
        also have "... = S"
          using p permutes_image by simp
        finally have set_ys: "set ys = S" .

        have "distinct ys"
          using ys assms(2) p permutes_inj_on distinct_map by blast

        show "ys \<in> ?L"
          using set_ys `distinct ys` by simp
      qed

      (* Direction B: Every valid list comes from a permutation *)
      show "?L \<subseteq> ?f ` ?P"
      proof
        fix ys assume "ys \<in> ?L"
        then have ys_props: "set ys = S" "distinct ys" by auto

        have len_ys: "length ys = n"
          using ys_props card_S distinct_card by force

        (* Construct the permutation using the pairs of (xs0, ys) *)
        let ?pairs = "zip xs0 ys"
        let ?p = "permutation_of_list ?pairs"

        (* Verify the conditions for list_permutes *)
        have "list_permutes ?pairs S"
          unfolding list_permutes_def
          using assms ys_props len_xs0 len_ys by simp

        then have p_perm: "?p permutes S"
          using permutation_of_list_permutes by blast

        (* Verify this permutation actually maps xs0 to ys *)
        have "map ?p xs0 = ys"
        proof (rule nth_equalityI)
          show "length (map ?p xs0) = length ys"
            using len_xs0 len_ys by simp

          fix i assume "i < length (map ?p xs0)"
          then have i: "i < length xs0" by simp
          then have in_zip: "(xs0!i, ys!i) \<in> set ?pairs"
            using len_xs0 len_ys set_zip by fastforce

          (* Use the property that permutation_of_list returns the paired value *)
          have "?p (xs0!i) = ys!i"
            using permutation_of_list_unique[OF `list_permutes ?pairs S` in_zip] by simp

          then show "map ?p xs0 ! i = ys ! i"
            using i by simp
        qed

        then show "ys \<in> ?f ` ?P"
          using p_perm by force
      qed
    qed
  qed
qed

(* Main Lemma: Proving the cardinality using the helpers *)
lemma card_permutations_list: "card {xs :: 'a list. set xs = S \<and> distinct xs} = fact n"
proof -
  (* 1. Get the reference list using Helper Lemma 1 *)
  obtain xs0 where xs0: "set xs0 = S" "distinct xs0"
    using distinct_list_of_S by force

  (* 2. Define the sets for clarity *)
  let ?P = "{p. p permutes S}"
  let ?L = "{xs. set xs = S \<and> distinct xs}"

  (* 3. Establish the bijection using Helper Lemma 2 *)
  have "bij_betw (\<lambda>p. map p xs0) ?P ?L"
    using permutations_to_list_bijection[OF xs0] .

  (* 4. Equate cardinalities via the bijection *)
  then have "card ?L = card ?P"
    using bij_betw_same_card by force

  (* 5. Use the known cardinality of permutations from the library *)
  also have "... = fact n"
    using card_permutations[OF card_S finite_S] by simp

  finally show ?thesis .
qed

lemma circular_permutations_partition:
  "card {xs. set xs = S \<and> distinct xs} = (\<Sum>C \<in> circular_permutations S. card C)"
proof -
  (* Define the set of valid lists *)
  let ?L = "{xs :: 'a list. set xs = S \<and> distinct xs}"
  (* Define the quotient set (circular permutations) *)
  let ?CP = "circular_permutations S"
  let ?Rel = "{(x, y). x \<sim>c y}"

  (* 1. Finite constraints *)
  have fin_L: "finite ?L"
    using finite_lists_length_eq[OF finite_S]
  by (metis card.infinite card_permutations_list
      fact_nonzero)

  have fin_CP: "finite ?CP"
    unfolding circular_permutations_def quotient_def
    using fin_L by simp

  (* 2. Partition Property *)
  have partition: "?L = \<Union>?CP"
    unfolding circular_permutations_def 
  proof (rule set_eqI)
    fix xs
    (* The goal is now clean: xs \<in> ?L \<longleftrightarrow> xs \<in> \<Union>(?L // ?Rel) *)
    show "xs \<in> ?L \<longleftrightarrow> xs \<in> \<Union>(?L // ?Rel)"
    proof
      assume "xs \<in> ?L"
      (* Reflexivity: xs is in its own class, and that class is in the quotient *)
      have "xs \<in> ?Rel `` {xs}"
        using c_reflexive circular_equiv_def by blast
      moreover have "?Rel `` {xs} \<in> ?L // ?Rel"
        using `xs \<in> ?L` unfolding quotient_def by blast
      ultimately show "xs \<in> \<Union>(?L // ?Rel)"
        by blast
    next
      assume "xs \<in> \<Union>(?L // ?Rel)"
      then obtain C where "xs \<in> C" and "C \<in> ?L // ?Rel" by blast
      then obtain ys where "ys \<in> ?L" and "C = ?Rel `` {ys}"
        unfolding quotient_def by auto

      then have "ys \<sim>c xs"
      using \<open>xs \<in> C\<close> by blast
   
      then obtain n where "xs = rotate n ys"
        unfolding circular_equiv_def by auto
      then show "xs \<in> ?L"
        using `ys \<in> ?L` by simp
    qed
  qed

  (* 3. Disjointness Property *)
  have disjoint: "\<forall>A\<in>?CP. \<forall>B\<in>?CP. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
    unfolding circular_permutations_def quotient_def
    using equiv_circular disjoint_iff_not_equal equiv_class_eq_iff quotient_eq_iff
  by (smt (verit) Image_singleton_iff UN_E
      singletonD)

  (* 4. Each class is finite *)
  have blocks_finite: "\<forall>C\<in>?CP. finite C"
    using fin_L partition by (auto intro: finite_subset)

  (* 5. Apply the Additive Law of Cardinality *)
  have "card (\<Union>?CP) = sum card ?CP"
    using card_Union_disjoint
  by (metis blocks_finite disjnt_def disjoint
      pairwise_def)

  then show ?thesis
    using partition by simp
qed

lemma circular_permutations_class_size:
  assumes "C \<in> circular_permutations S"
  shows "card C = n"
proof -
  (* 1. Unwrap the definition to find a representative list xs *)
  (* Since C is an element of the quotient set, it is an equivalence class for some xs *)
  from assms obtain xs where xs_props: "set xs = S" "distinct xs"
    and C_def: "C = {ys. xs \<sim>c ys}"
    unfolding circular_permutations_def quotient_def Image_def
    by auto

  (* 2. Establish basic length properties *)
  have len_xs: "length xs = n"
    using xs_props card_S distinct_card by force

  have "n > 0"
    using k_pos n_bound by auto

  (* 3. Characterize C as exactly the set of n rotations *)
  (* We map indices 0 to n-1 to rotated lists *)
  let ?rotations = "(\<lambda>i. rotate i xs) ` {0..<n}"

  have "C = ?rotations"
  proof (intro set_eqI iffI)
    (* Direction 1: Any equivalent list is a rotation *)
    fix ys assume "ys \<in> C"
    then obtain k where "ys = rotate k xs"
      using C_def circular_equiv_def len_xs by auto

    (* Normalize the rotation index modulo n *)
    let ?i = "k mod n"
    have "ys = rotate ?i xs"
      using `ys = rotate k xs` rotate_conv_mod len_xs by auto
    moreover have "?i < n"
      using `n > 0` by simp
    ultimately show "ys \<in> ?rotations"
      by simp
  next
    (* Direction 2: Any rotation is equivalent *)
    fix ys assume "ys \<in> ?rotations"
    then obtain i where "i < n" and "ys = rotate i xs" by auto
    then show "ys \<in> C"
      using C_def circular_equiv_def len_xs by fastforce
  qed

  (* 4. Prove injectivity: All n rotations are distinct *)
  have "inj_on (\<lambda>i. rotate i xs) {0..<n}"
  proof (rule inj_onI)
    fix i j
    assume i: "i \<in> {0..<n}" and j: "j \<in> {0..<n}"
    assume eq: "rotate i xs = rotate j xs"

    (* If the lists are equal, their 0-th elements are equal *)
    have "(rotate i xs) ! 0 = (rotate j xs) ! 0" using eq by simp

    (* Expand the definition of nth for rotate *)
    then have "xs ! ((0 + i) mod n) = xs ! ((0 + j) mod n)"
      using nth_rotate len_xs `n > 0` i j by fastforce

    (* Simplify using the fact that i, j < n *)
    then have "xs ! i = xs ! j"
      using i j by simp

    (* Use distinctness of xs to prove indices are equal *)
    then show "i = j"
      using xs_props(2) len_xs distinct_conv_nth i j by auto
  qed

  (* 5. Final Cardinality Calculation *)
  then have "card C = card {0..<n}"
    using `C = ?rotations` card_image by fast
  thus ?thesis by simp
qed

lemma card_circular_permutations: "card (circular_permutations S) = fact (n - 1)"
proof -
  (* 1. Start with the cardinality of linear permutations *)
  have "fact n = card {xs. set xs = S \<and> distinct xs}"
    using card_permutations_list by simp

  (* 2. Decompose into the sum of partition block sizes *)
  also have "... = (\<Sum>C \<in> circular_permutations S. card C)"
    using circular_permutations_partition by simp

  (* 3. Substitute the constant size 'n' for each block *)
  also have "... = (\<Sum>C \<in> circular_permutations S. n)"
    using circular_permutations_class_size by simp

  (* 4. Simplify the sum of a constant *)
  also have "... = n * card (circular_permutations S)"
    by simp

  (* 5. Solve for card (circular_permutations S) *)
  finally have eq: "fact n = n * card (circular_permutations S)" .

  have "n > 0"
    using k_pos n_bound by simp

  then show ?thesis
  by (metis (no_types, opaque_lifting) Suc_diff_1 eq fact_reduce
      mult_cancel_left of_nat_eq_iff of_nat_fact of_nat_mult
      of_nat_neq_0)
qed

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
(*
lemma katona_circle_claim:
  fixes \<sigma> :: "'a list"
  assumes "\<exists> \<Sigma> \<in> circular_permutations S. \<sigma> \<in> \<Sigma>"    
  shows "card {A \<in> \<F>. meets \<sigma> A} \<le> k"
proof -
  show ?thesis sorry
qed
*)

lemma katona_circle_claim:
  assumes "\<Sigma> \<in> circular_permutations S"
  shows "card {A \<in> \<F>. (\<forall> \<sigma> \<in> \<Sigma>. meets \<sigma> A)} \<le> k"
  sorry

lemma meets_class_consistent:
  assumes "\<Sigma> \<in> circular_permutations S"
  assumes "\<sigma>1 \<in> \<Sigma>" and "\<sigma>2 \<in> \<Sigma>"
  shows "meets \<sigma>1 A \<longleftrightarrow> meets \<sigma>2 A"
  proof -
  (* Since they are in the same class, they are rotationally equivalent *)
  from assms have "\<sigma>1 \<sim>c \<sigma>2"
    unfolding circular_permutations_def quotient_def Image_def
    using circular_equiv_def mem_Collect_eq quotient_eq_iff
    by (smt (verit, best) c_symmetric c_transitive
      imageE mem_simps(9) singletonD
      split_conv)

  then obtain m where "\<sigma>2 = rotate m \<sigma>1"
    unfolding circular_equiv_def by auto

  show ?thesis
    using meets_rotation_invariant[of "\<sigma>1" A m]
    using meets_rotation_invariant[of "\<sigma>2" A "length \<sigma>1 - (m mod length \<sigma>1)"]
    unfolding `\<sigma>2 = rotate m \<sigma>1`
    (* The reverse direction is implied by symmetry of equivalence or reverse rotation *)
    using `\<sigma>1 \<sim>c \<sigma>2` c_symmetric circular_equiv_def meets_rotation_invariant
    by (metis \<open>\<sigma>2 = rotate m \<sigma>1\<close>)
qed

lemma \<S>_decomposition:
  "card \<S> = (\<Sum>\<Sigma>\<in>circular_permutations S. card {A \<in> \<F>. (\<forall> \<sigma> \<in> \<Sigma>. meets \<sigma> A)})"
proof -
  let ?CP = "circular_permutations S"
  (* Define the fiber for a given permutation class *)
  let ?Fiber = "\<lambda>\<Sigma>. {A \<in> \<F>. (\<forall> \<sigma> \<in> \<Sigma>. meets \<sigma> A)}"
  (* Define the set of pairs we are counting *)
  let ?S_swapped = "SIGMA \<Sigma>:?CP. ?Fiber \<Sigma>"

  (* 1. Establish the bijection between S and the Sigma set *)
  have "bij_betw (\<lambda>(A, \<Sigma>). (\<Sigma>, A)) \<S> ?S_swapped"
    unfolding \<S>_def bij_betw_def inj_on_def by auto
  then have "card \<S> = card ?S_swapped"
    by (rule bij_betw_same_card)

  (* 2. Bridge the gap: Prove the Set Equality explicitly *)
  (* The SIGMA set is definitionally equal to the Union of these products *)
  also have "?S_swapped = (\<Union>\<Sigma>\<in>?CP. {\<Sigma>} \<times> ?Fiber \<Sigma>)"
    by (auto simp: Sigma_def)

  (* Therefore, their cardinalities are equal *)
  then have "card ?S_swapped = card (\<Union>\<Sigma>\<in>?CP. {\<Sigma>} \<times> ?Fiber \<Sigma>)"
    by simp

  also have "... = (\<Sum>\<Sigma>\<in>?CP. card ({\<Sigma>} \<times> ?Fiber \<Sigma>))"
  proof (rule card_UN_disjoint)
    show "finite ?CP"
      using finite_S
    using card.infinite card_circular_permutations
    by fastforce

    show "\<forall>\<Sigma>\<in>?CP. finite ({\<Sigma>} \<times> ?Fiber \<Sigma>)"
    proof
      fix \<Sigma> assume "\<Sigma> \<in> ?CP"
      have "finite \<F>"
        using finite_S F_family_of_k_subsets finite_Pow_iff finite_subset by fastforce
      then have "finite (?Fiber \<Sigma>)" by auto
      thus "finite ({\<Sigma>} \<times> ?Fiber \<Sigma>)" by simp
    qed

    (* We match the expanded goal explicitly to avoid refinement errors *)
    show "\<forall>i\<in>?CP. \<forall>j\<in>?CP. i \<noteq> j \<longrightarrow> ({i} \<times> ?Fiber i) \<inter> ({j} \<times> ?Fiber j) = {}"
      by auto (* Disjoint because the first components (i and j) are distinct *)
  qed

  (* 3. Simplify the cardinality of the cartesian product *)
  also have "... = (\<Sum>\<Sigma>\<in>?CP. card (?Fiber \<Sigma>))"
  by (simp add: card_cartesian_product_singleton) (* card ({x} x A) = card A *)

  finally show ?thesis .
qed

lemma \<S>_upper_bound:
  shows "card \<S> \<le> (fact (n - 1)) * k"
proof -
  (* 1. Decompose S *)
  have "card \<S> = (\<Sum>\<Sigma>\<in>circular_permutations S. card {A \<in> \<F>. (\<forall> \<sigma> \<in> \<Sigma>. meets \<sigma> A)})"
    using \<S>_decomposition by simp

  (* 2. Apply the bound k to each term in the sum *)
  also have "... \<le> (\<Sum>\<Sigma>\<in>circular_permutations S. k)"
    using katona_circle_claim sum_mono by meson

  (* 3. Simplify the sum of a constant *)
  also have "... = card (circular_permutations S) * k"
    by simp

  (* 4. Use the cardinality of circular permutations *)
  also have "... = fact (n - 1) * k"
    using card_circular_permutations by simp

  finally show ?thesis .
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
