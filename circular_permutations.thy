theory circular_permutations imports Main "HOL-Combinatorics.Permutations"
begin

definition permutation_of :: "'a list \<Rightarrow> 'a set \<Rightarrow> bool" (infix "permutation-of" 50) where
  "xs permutation-of S \<longleftrightarrow> (set xs = S \<and> distinct xs)"

definition circular_equiv :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "\<sim>c" 50) where
  "xs \<sim>c ys \<longleftrightarrow> (length xs = length ys \<and> (\<exists>n. ys = rotate n xs))"

lemma c_reflexive:
  shows "xs \<sim>c xs"
  by (metis circular_equiv_def mod_0 rotate_id)

lemma c_transitive:
  assumes "xs \<sim>c ys \<and> ys \<sim>c zs"
  shows "xs \<sim>c zs"
  by (metis assms circular_equiv_def length_rotate rotate_rotate)

lemma c_symmetric:
  assumes "xs \<sim>c ys"
  shows "ys \<sim>c xs"
proof -
  (* Obtain the rotation index witness from the assumed equivalence of xs and ys *)
  obtain n where len_eq: "length xs = length ys" and ys_def: "ys = rotate n xs"
    using assms unfolding circular_equiv_def by blast

  (* We construct the inverse rotation index to prove symmetry *)
  have "\<exists>k. xs = rotate k ys"
    proof (cases "xs = []")
      case xs_empty: True 
      then show ?thesis 
        using ys_def by simp
    next
      case xs_nonempty: False
      let ?k = "length xs - (n mod length xs)"
      
      have "rotate ?k ys = rotate ?k (rotate n xs)" 
        using ys_def by simp
      also have "... = rotate (?k + n) xs" 
        by (simp add: rotate_rotate)
      also have "... = rotate (length xs) xs"
        using xs_nonempty 
        by (metis Nat.le_imp_diff_is_add length_greater_0_conv
          mod_add_right_eq mod_le_divisor rotate_conv_mod)
      also have "... = xs" 
        by simp
      finally show ?thesis 
        by metis
    qed
    then show ?thesis 
      unfolding circular_equiv_def by auto
qed


(* Thus, "\<sim>c" is an equivalence relation *)
lemma equiv_circular: "equiv UNIV {(x, y). x \<sim>c y}"
  by (auto simp: equiv_def refl_on_def sym_def trans_def 
      intro: c_reflexive c_symmetric c_transitive)

(* The set of circular permutations of a set consists of equivalence classes,
   each class corresponding to a different circular permutation.  *)
definition circular_permutations :: "'a set \<Rightarrow> ('a list set) set" where
  "circular_permutations S = 
    {xs :: 'a list. set xs = S \<and> distinct xs} // {(x, y). x \<sim>c y}"


(* The functional definition "permutes" from library 
   and our definition of permutation using lists are equivalent *)
lemma permutations_to_lists_bijection:
  assumes card_S: "card S = n"
  assumes xs0_valid: "set xs0 = S" "distinct xs0"
  shows "bij_betw (\<lambda>p. map p xs0) {p. p permutes S} {xs. set xs = S \<and> distinct xs}"
proof -
  let ?P = "{p. p permutes S}"
  let ?L = "{xs. set xs = S \<and> distinct xs}"
  let ?f = "\<lambda>p. map p xs0"

  have len_xs0: "length xs0 = n"
    using xs0_valid card_S distinct_card by fastforce

  show "bij_betw ?f ?P ?L" unfolding bij_betw_def
  proof (intro conjI)
    (* Injectivity *)
    show "inj_on ?f ?P"
    proof (rule inj_onI)
      fix p q assume p: "p \<in> ?P" and q: "q \<in> ?P"
      assume eq: "?f p = ?f q"
      show "p = q"
      proof
        fix x
        show "p x = q x"
        proof (cases "x \<in> S")
          case x_in_S: True
          (* Find the index of x in S *)
          then obtain i where "i < length xs0" "xs0 ! i = x" 
            using xs0_valid by (metis in_set_conv_nth)
          (* List versions of p and q are equal at that index *)
          moreover have "map p xs0 ! i = map q xs0 ! i" 
            using eq by argo
          ultimately show ?thesis 
            by simp
        next
          case x_not_in_S: False
          (* p and q are same by definition *)
          then show ?thesis 
            using p q permutes_not_in by (metis mem_Collect_eq)
        qed
      qed
    qed
  next
    (* Surjectivity *)
    show "?f ` ?P = ?L"
    proof (rule subset_antisym)
      (* "\<subseteq>": Every permutation creates a valid distinct list *)
      show "?f ` ?P \<subseteq> ?L"
      proof
        fix ys assume "ys \<in> ?f ` ?P"
        then obtain p where p: "p \<in> ?P" and ys: "ys = map p xs0" 
          by auto
        (* p corresponds to ys *)
        have "set ys = p ` S" 
          using ys xs0_valid by simp
        also have "... = S" 
          using p permutes_image by simp
        finally have set_ys: "set ys = S" .

        have "distinct ys" 
          using ys xs0_valid p permutes_inj_on distinct_map by blast
        show "ys \<in> ?L" 
          using set_ys `distinct ys` by simp
      qed
    next
      (* "\<supseteq>": Every valid distinct list comes from a permutation *)
      show "?L \<subseteq> ?f ` ?P"
      proof
        fix ys assume "ys \<in> ?L"
        then have ys_valid: "set ys = S" "distinct ys" 
          by auto
        have len_ys: "length ys = n" 
          using ys_valid card_S distinct_card by force

        (* Create the p corresponding to ys *)
        let ?pairs = "zip xs0 ys"
        let ?p = "permutation_of_list ?pairs"
        have "list_permutes ?pairs S" 
          unfolding list_permutes_def using xs0_valid ys_valid len_xs0 len_ys by simp
        then have p_perm: "?p permutes S"
          using permutation_of_list_permutes by blast

        (* Prove that p maps xs0 to ys *)
        have "map ?p xs0 = ys"
        proof (rule nth_equalityI)
          show "length (map ?p xs0) = length ys"
            using len_xs0 len_ys by simp
          fix i assume i: "i < length (map ?p xs0)"
          then have pairs: "(xs0!i, ys!i) \<in> set ?pairs"
            using len_xs0 len_ys set_zip by fastforce
          have "?p (xs0!i) = ys!i"
            using permutation_of_list_unique[OF `list_permutes ?pairs S` pairs] by simp
          then show "map ?p xs0 ! i = ys ! i"
            using i by simp
        qed
        then show "ys \<in> ?f ` ?P"
          using p_perm by force
      qed
    qed
  qed
qed


(* The number of permutations (represented as lists) of an n-element set is n factorial. *)
lemma card_linear_permutations:
  assumes finite_S: "finite S"
  assumes card_S: "card S = n"
  shows  "card {xs :: 'a list. set xs = S \<and> distinct xs} = fact n"
proof -
  (* Cast the set to a list (of arbitrary order) *)
  obtain xs0 where xs0: "set xs0 = S" "distinct xs0"
    using finite_S finite_distinct_list by auto

  let ?P = "{p. p permutes S}"
  let ?L = "{xs. set xs = S \<and> distinct xs}"
  let ?f = "\<lambda>p. map p xs0"

  (* Use the established bijection *)
  have "bij_betw ?f ?P ?L"
    using permutations_to_lists_bijection xs0 by blast
  then have "card ?L = card ?P"
    using bij_betw_same_card by fastforce
  also have "... = fact n"
    using card_permutations[OF card_S finite_S] by simp
  finally show ?thesis .
qed


(* Every equivalence class of permutatations w.r.t "\<sim>c" is of size n *)
lemma circular_permutations_class_size:
  assumes n_pos: "n > 0"
  assumes finite_S: "finite S"
  assumes card_S: "card S = n"
  assumes "C \<in> circular_permutations S"
  shows "card C = n"
proof -
  (* C is the equivalence class w.r.t "\<sim>c" for some permutation xs *)
  obtain xs where xs_valid: "set xs = S" "distinct xs" and C_def: "C = {ys. xs \<sim>c ys}"
    using assms unfolding circular_permutations_def quotient_def Image_def by auto
  have len_xs: "length xs = n"
    using xs_valid card_S distinct_card by force

  (* C is the set of rotations of xs *)
  let ?rotations = "(\<lambda>i. rotate i xs) ` {0..<n}"
  have C_eq_rotations: "C = ?rotations"
  proof (intro set_eqI iffI)
    fix ys assume "ys \<in> C"
    then obtain k where "ys = rotate k xs"
      using C_def circular_equiv_def len_xs by auto
    then show "ys \<in> ?rotations"
      using len_xs n_pos rotate_conv_mod by fastforce
  next
    fix ys assume "ys \<in> ?rotations"
    then show "ys \<in> C"
      using C_def circular_equiv_def len_xs by fastforce
  qed

  (* Each of the n rotations of xs is distinct from others *)
  have "inj_on (\<lambda>i. rotate i xs) {0..<n}"
  proof (rule inj_onI)
    fix i j assume i: "i \<in> {0..<n}" and j: "j \<in> {0..<n}"
      and eq: "rotate i xs = rotate j xs"
    then show "i = j" 
      using xs_valid len_xs distinct_conv_nth
      by (metis add.right_neutral atLeastLessThan_iff mod_less n_pos nth_rotate)
  qed

  then have "card ?rotations = card {0..<n}"
    using card_image by fast
  then show ?thesis 
    using C_eq_rotations by simp 
qed


(* The sum of sizes of equivalence classes w.r.t "\<sim>c" equals the size of all linear permutations *)
lemma circular_permutations_partition:
  assumes finite_S: "finite S"
  assumes card_S: "card S = n"
  shows "card {xs. set xs = S \<and> distinct xs} = (\<Sum>C \<in> circular_permutations S. card C)"
proof -
  let ?P = "{xs. set xs = S \<and> distinct xs}"
  let ?CP = "circular_permutations S"
  let ?Eq = "{(x, y). x \<sim>c y}"

  have fin_P: "finite ?P"
    using card_linear_permutations[OF finite_S card_S] card_gt_0_iff by force
  have fin_CP: "finite ?CP"
    unfolding circular_permutations_def quotient_def using fin_P by simp

  (* The set of equivalence classes partitions the set of all permutations *)
  have partition: "?P = \<Union>?CP" unfolding circular_permutations_def 
  proof (rule set_eqI)
    fix xs
    show "xs \<in> ?P \<longleftrightarrow> xs \<in> \<Union>(?P // ?Eq)"
    proof
      assume "xs \<in> ?P"
      (* xs is in the equivalence class of xs *)
      have "xs \<in> ?Eq `` {xs}"
        using c_reflexive circular_equiv_def by blast
      (* One of the equivalence classes is the equivalence class of xs *)
      moreover have "?Eq `` {xs} \<in> ?P // ?Eq" 
        using `xs \<in> ?P` unfolding quotient_def by blast
      ultimately show "xs \<in> \<Union>(?P // ?Eq)"
        by blast
    next
      assume "xs \<in> \<Union>(?P // ?Eq)"
      then obtain C where "xs \<in> C" and "C \<in> ?P // ?Eq" 
        by blast
      (* Find ys s.t. C is the equivalence class of ys*)
      then obtain ys where "ys \<in> ?P" and "C = ?Eq `` {ys}" 
        unfolding quotient_def by auto
      then have "ys \<sim>c xs"
        using `xs \<in> C` by blast
      then obtain n where "xs = rotate n ys"
        unfolding circular_equiv_def by auto
      then show "xs \<in> ?P"
        using `ys \<in> ?P` by simp
    qed
  qed

  (* The classes are pairwise disjoint *)
  have "\<forall>A \<in> ?CP. \<forall>B \<in> ?CP. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
    unfolding circular_permutations_def quotient_def
    using equiv_circular disjoint_iff_not_equal equiv_class_eq_iff quotient_eq_iff
    by (smt (verit) Image_singleton_iff UN_E singletonD)
  moreover have "\<forall>C \<in> ?CP. finite C"
    using fin_P partition by (auto intro: finite_subset)
  ultimately have "card (\<Union>?CP) = sum card ?CP"
    using card_Union_disjoint disjoint_def by fast
  then show ?thesis
    using partition by simp
qed


theorem card_circular_permutations: 
  assumes n_pos: "n > 0"
  assumes finite_S: "finite S"
  assumes card_S: "card S = n"
  shows "card (circular_permutations S) = fact (n - 1)"
proof -
  have "fact n = card {xs. set xs = S \<and> distinct xs}"
    using card_linear_permutations[OF finite_S card_S] by simp
  also have "... = (\<Sum>C \<in> circular_permutations S. card C)"
    using circular_permutations_partition[OF finite_S card_S] by simp
  also have "... = (\<Sum>C \<in> circular_permutations S. n)"
    using circular_permutations_class_size[OF n_pos finite_S card_S] by simp
  also have "... = n * card (circular_permutations S)"
    by simp
  finally show ?thesis
    using n_pos by (simp add: fact_reduce)
qed

end