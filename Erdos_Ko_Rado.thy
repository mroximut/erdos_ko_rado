theory Erdos_Ko_Rado imports 
  Main circular_permutations Arcs List_Helper
begin

definition intersecting :: "'a set set \<Rightarrow> bool" where
  "intersecting F \<longleftrightarrow> (\<forall>A \<in> F. \<forall>B \<in> F. A \<inter> B \<noteq> {})"

locale ekr_context =
  fixes n k :: nat
  fixes S :: "'a set"
  fixes \<F> :: "'a set set"
  assumes finite_S: "finite S"
  assumes card_S: "card S = n"
  assumes n_pos: "n > 0"
  assumes k_pos: "k > 0"
  assumes n_bound: "2 * k \<le> n"
  assumes F_family_of_k_subsets: "\<F> \<subseteq> {A. A \<subseteq> S \<and> card A = k}"
  assumes intersecting_F: "intersecting \<F>"
begin

definition meets :: "'a list \<Rightarrow> 'a set \<Rightarrow> bool" (infix "meets" 50) where
  "\<sigma> meets A \<longleftrightarrow> (\<exists>i k. A = set (take k (rotate i \<sigma>)))"

definition \<S> :: "('a set \<times> 'a list set) set" where 
  "\<S> = {(A, C). A \<in> \<F> \<and> (C \<in> circular_permutations S) \<and> (\<forall>\<sigma> \<in> C. \<sigma> meets A)}"

end

context ekr_context
begin

definition arc_list :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a list" where
  "arc_list \<sigma> A = 
    take (card A) (rotate (SOME i. i < length \<sigma> \<and> A = set (take (card A) (rotate i \<sigma>))) \<sigma>)"


lemma A_props:
  assumes "A \<in> \<F>"
  shows "card A = k" and "A \<subseteq> S" and "finite A"
proof -
  show "A \<subseteq> S" and "card A = k"
    using assms F_family_of_k_subsets by auto
  show "finite A" 
    using `A \<subseteq> S` finite_S finite_subset by auto
qed

lemma \<sigma>_props:
  assumes "C \<in> circular_permutations S"
  assumes "\<sigma> \<in> C"
  shows "distinct \<sigma>" and "set \<sigma> = S" and "length \<sigma> = n" and "\<sigma> \<noteq> []"
proof -
  show "distinct \<sigma>"  
    using circular_permutations_def assms
    by (smt (verit, ccfv_SIG) Image_singleton_iff case_prod_conv circular_equiv_def distinct_rotate
        mem_Collect_eq quotientE)
  show "set \<sigma> = S"
    using circular_permutations_def assms
    by (smt (verit, best) Image_singleton_iff circular_equiv_def mem_Collect_eq quotientE
        set_rotate split_conv)
  then show "length \<sigma> = n"
    using `distinct \<sigma>` card_S distinct_card by fastforce
  then show "\<sigma> \<noteq> []"
    using n_pos by auto
qed

lemma meets_card:
  assumes "\<sigma> meets A" and "distinct \<sigma>" and "\<sigma> \<noteq> []"
  shows "\<exists>i. A = set (take (card A) (rotate i \<sigma>)) \<and> i < length \<sigma>"
proof -
  obtain i j where j: "set (take j (rotate i \<sigma>)) = A"
    using `\<sigma> meets A` unfolding meets_def by blast
  let ?L = "rotate i \<sigma>"
  have "distinct (take j ?L)"
    using `distinct \<sigma>` by simp
  then have "length (take j ?L) = card A"
    using j distinct_card by fastforce
  then have "take (card A) ?L = take j ?L"
    by (metis append_eq_conv_conj append_take_drop_id)
  then have take_card: "A = set (take (card A) ?L)"
    using j by simp
  show ?thesis
  proof (cases "i < length \<sigma>")
    case True
    then show ?thesis 
      using take_card by auto 
  next
    case False
    let ?t = "i mod (length \<sigma>)"
    have "?t < length \<sigma>"
      using assms(3) by simp
    moreover have "rotate i \<sigma> = rotate ?t \<sigma>"
      by (simp add: rotate_drop_take)
    ultimately show ?thesis 
      using take_card by auto
  qed
qed


lemma arc_list_props:
  assumes "distinct \<sigma>"
  assumes "\<sigma> \<noteq> []"
  assumes "\<sigma> meets A"
  shows "set (arc_list \<sigma> A) = A" 
    and "distinct (arc_list \<sigma> A)"
    and "\<exists>i. arc_list \<sigma> A = (take (card A) (rotate i \<sigma>)) \<and> i < length \<sigma>"
proof -
  have "\<exists>i < length \<sigma>. A = set (take (card A) (rotate i \<sigma>))"
    using assms meets_card by blast

  then show "set (arc_list \<sigma> A) = A"
    unfolding arc_list_def using someI_ex by (metis (mono_tags, lifting))

  moreover show "distinct (arc_list \<sigma> A)"
    unfolding arc_list_def using \<sigma>_props by (meson assms distinct_rotate distinct_take)

  ultimately show "\<exists>i. arc_list \<sigma> A = (take (card A) (rotate i \<sigma>)) \<and> i < length \<sigma>" 
    using meets_card assms
    by (metis (no_types, lifting) arc_list_def bot_nat_0.not_eq_extremum length_0_conv
        mod_less_divisor rotate_conv_mod)
qed


lemma arc_list_rec:
  fixes S' :: "'a set set"
  assumes "distinct \<sigma>"
  assumes "\<sigma> \<noteq> []"
  assumes "\<forall>A \<in> S'. card A = k'"
  assumes "\<forall>A \<in> S'. \<sigma> meets A"
  shows "set ` (arc_list \<sigma>) ` S' = S'"
using assms list_of_props(1) arc_list_props
by (smt (verit, ccfv_SIG) image_comp image_cong image_ident o_apply)


lemma card_circular_permutations_of_S: "card (circular_permutations S) = fact (n - 1)"
  using card_circular_permutations[OF n_pos finite_S card_S] .

lemma finite_CP: "finite (circular_permutations S)"
  using finite_S card.infinite card_circular_permutations_of_S by fastforce

lemma finite_\<F>: "finite \<F>"
  using finite_S F_family_of_k_subsets finite_Pow_iff finite_subset by fastforce


lemma meets_rotation_invariant:
  assumes "\<sigma> meets A"
  shows "(rotate m \<sigma>) meets A"
proof -
  obtain j k where "A = set (take k (rotate j \<sigma>))"
    using assms unfolding meets_def by auto
  obtain i where "rotate i (rotate m \<sigma>) = rotate j \<sigma>"
    using c_symmetric c_transitive circular_equiv_def length_rotate by metis
  then have "set (take k (rotate i (rotate m \<sigma>))) = A"
    using `A = set (take k (rotate j \<sigma>))` by simp
  then show ?thesis
    unfolding meets_def by blast
qed


lemma katona_circle_claim_trivial:
  assumes "n \<le> 2"
  assumes "C \<in> circular_permutations S"
  shows "card {A \<in> \<F>. (\<forall>\<sigma> \<in> C. \<sigma> meets A)} \<le> k"
proof -
  have "k = 1" and "n = 2"
    using k_pos n_pos n_bound assms(1) by auto

  then have "\<forall>A \<in> \<F>. \<forall>B \<in> \<F>. A = B"
  proof (intro ballI)
    fix A B assume "A \<in> \<F>" "B \<in> \<F>"
    then have "card A = 1" and "card B = 1"
      using F_family_of_k_subsets `k = 1` by auto
    moreover have "A \<inter> B \<noteq> {}"
      using intersecting_F `A \<in> \<F>` `B \<in> \<F>` by (simp add: intersecting_def) 
    ultimately show "A = B"
      using card_1_singletonE by blast 
  qed
  
  then have "card \<F> \<le> 1"
    by (simp add: card_le_Suc0_iff_eq finite_\<F>)
  let ?MetSets = "{A \<in> \<F>. (\<forall>\<sigma> \<in> C. \<sigma> meets A)}"
  have "?MetSets \<subseteq> \<F>" 
    by blast
  then have "card ?MetSets \<le> card \<F>"
    using finite_\<F> card_mono by blast
  then show ?thesis
    using `k = 1` `card \<F> \<le> 1` by linarith
qed


lemma katona_circle_claim:
  assumes "C \<in> circular_permutations S"
  shows "card {A \<in> \<F>. (\<forall>\<sigma> \<in> C. \<sigma> meets A)} \<le> k"
proof (cases "n \<le> 2")
  case True
  then show ?thesis 
    using katona_circle_claim_trivial[OF True assms] by simp
next
  case False
  then have "n \<ge> 3"
    by auto
  have "C \<noteq> {}" 
    using card_S n_pos by (metis assms card_gt_0_iff circular_permutations_class_size)
  then obtain \<sigma> where \<sigma>: "\<sigma> \<in> C"
    by auto
  let ?MetSets = "{A \<in> \<F>. (\<forall>\<sigma> \<in> C. \<sigma> meets A)}"
  let ?Arcs = "list_of (arc_list \<sigma> ` ?MetSets)"
  have "finite ?MetSets"
    using finite_\<F> by force
  have set_arcs: "set ?Arcs = arc_list \<sigma> ` ?MetSets" 
    by (simp add: `finite ?MetSets` list_of_props(1))

  interpret arc_context \<sigma> ?Arcs k
  proof
    show "length \<sigma> \<ge> 3" 
      using `n \<ge> 3` \<sigma> \<sigma>_props assms by auto
    then have "\<sigma> \<noteq> []" 
      by auto
    show "distinct \<sigma>" 
      using assms \<sigma> \<sigma>_props by simp
    show all_arcs :"\<forall>arc \<in> set ?Arcs. n_arc_of_cycle arc \<sigma> k"
    proof
      fix arc assume arc: "arc \<in> set ?Arcs"
      moreover have "\<sigma> meets (set arc)"
        using arc set_arcs arc_list_props by (metis (lifting) arc_list_def imageE meets_def)
      moreover have "distinct arc" 
        using arc_list_props set_arcs `distinct \<sigma>` \<sigma> `\<sigma> \<noteq> []` arc by fastforce
      moreover have "length arc = k" and "card (set arc) = k"
        using set_arcs A_props arc distinct_card arc_list_props `\<sigma> \<noteq> []`
        by (smt (verit, best) `distinct \<sigma>` \<sigma> imageE mem_Collect_eq)+
      ultimately obtain i where "i < length \<sigma> \<and> arc = take (card (set arc)) (rotate i \<sigma>)"   
        using `\<sigma> \<noteq> []` `distinct \<sigma>` \<sigma> arc arc_list_props
        by (smt (verit, best) imageE mem_Collect_eq set_arcs)
      then have "arc_of_cycle arc \<sigma>"
        unfolding arc_of_cycle_def using `card (set arc) = k` `length arc = k` by auto
      then show "n_arc_of_cycle arc \<sigma> k" 
        unfolding n_arc_of_cycle_def using `length arc = k` by auto
    qed
    show "k \<ge> 1" 
      using k_pos by simp
    show "2 * k \<le> length \<sigma>" 
      using assms \<sigma> \<sigma>_props(3) n_bound by simp
    have "\<forall>arc \<in> arc_list \<sigma> ` {A \<in> \<F>. \<forall>\<sigma>\<in>C. \<sigma> meets A}. arc_of_cycle arc \<sigma> \<and> length arc = k"
      using assms all_arcs n_arc_of_cycle_def set_arcs by blast
    then show "intersecting_n_arcs ?Arcs \<sigma> k" 
      unfolding intersecting_n_arcs_def intersecting_arcs_def n_arc_of_cycle_def
      using \<sigma> set_arcs intersecting_F all_arcs intersecting_lists_eq `\<sigma> \<noteq> []` `distinct \<sigma>` 
            arc_list_props(1) image_iff intersecting_def mem_Collect_eq by (smt (verit, best))
    show "distinct ?Arcs" 
      using list_of_props(2) by (metis (lifting) `finite ?MetSets` finite_imageI)
  qed
  
  have "length ?Arcs \<le> k"
    using intersecting_n_arcs_upper_limit by blast
  then have "card (set ?Arcs) \<le> k" 
    using card_length le_trans by blast
  then have card_k: "card (set ` set ?Arcs) \<le> k"
    by (meson List.finite_set card_image_le le_trans)
  have "set ` set ?Arcs = ?MetSets"
    using A_props set_arcs arc_list_props arc_list_rec \<sigma> \<sigma>_props assms
    by (smt (verit, best) mem_Collect_eq)
  then show "card ?MetSets \<le> k" 
    using card_k by simp  
qed


lemma meets_class_consistent:
  assumes "C \<in> circular_permutations S"
  assumes "\<sigma>1 \<in> C" and "\<sigma>2 \<in> C"
  shows "\<sigma>1 meets A \<longleftrightarrow> \<sigma>2 meets A"
  proof -
  from assms have "\<sigma>1 \<sim>c \<sigma>2"
    unfolding circular_permutations_def quotient_def Image_def
    using mem_Collect_eq quotient_eq_iff c_reflexive c_symmetric c_transitive
    by (smt (verit, best) imageE mem_simps(9) singletonD split_conv)
  then obtain m where "\<sigma>2 = rotate m \<sigma>1"
    unfolding circular_equiv_def by auto
  then show ?thesis
    using meets_rotation_invariant meets_def rotate_rotate by metis
qed


lemma \<S>_decomposition_C:
  shows "card \<S> = (\<Sum> C \<in> circular_permutations S. card {A \<in> \<F>. (\<forall> \<sigma> \<in> C. \<sigma> meets A)})"
proof -
  let ?CP = "circular_permutations S"
  let ?MetBy = "\<lambda>C. {A \<in> \<F>. (\<forall> \<sigma> \<in> C. \<sigma> meets A)}"
  let ?\<S>' = "(\<Union> C \<in> ?CP. {C} \<times> ?MetBy C)"

  have "bij_betw (\<lambda>(A, C). (C, A)) \<S> ?\<S>'"
    unfolding \<S>_def bij_betw_def inj_on_def by auto
  then have "card \<S> = card ?\<S>'"
    using bij_betw_same_card by auto

  also have "...  = (\<Sum> C \<in> ?CP. card ({C} \<times> ?MetBy C))"
  proof (rule card_UN_disjoint)
    show "finite ?CP" 
      using finite_CP .
    show "\<forall>C \<in> ?CP. finite ({C} \<times> ?MetBy C)"
      using finite_\<F> by simp
    show "\<forall>C \<in> ?CP. \<forall>C' \<in> ?CP. C \<noteq> C' \<longrightarrow> ({C} \<times> ?MetBy C) \<inter> ({C'} \<times> ?MetBy C') = {}"
      by auto 
  qed

  also have "... = (\<Sum> C \<in> ?CP. card (?MetBy C))"
    by (simp add: card_cartesian_product_singleton) (* card ({x} x A) = card A *)
  finally show ?thesis .
qed


lemma \<S>_decomposition_by_A:
  shows "card \<S> = (\<Sum> A \<in> \<F>. card {C \<in> circular_permutations S. (\<forall> \<sigma> \<in> C. \<sigma> meets A)})"
proof -
  let ?CP = "circular_permutations S"
  let ?Meeting = "\<lambda>A. {C \<in> ?CP. (\<forall> \<sigma> \<in> C. \<sigma> meets A)}"
  let ?\<S>' = "(\<Union> A \<in> \<F>. {A} \<times> ?Meeting A)"

  have "\<S> = ?\<S>'" 
    unfolding \<S>_def by auto
  then have "card \<S> = card ?\<S>'"
    by simp
  also have "... = (\<Sum> A \<in> \<F>. card ({A} \<times> ?Meeting A))"
  proof (rule card_UN_disjoint)
    show "finite \<F>" 
      using finite_\<F> .
    show "\<forall>A \<in> \<F>. finite ({A} \<times> ?Meeting A)"
      using finite_CP by simp
    show "\<forall>A \<in> \<F>. \<forall>A' \<in> \<F>. A \<noteq> A' \<longrightarrow> ({A} \<times> ?Meeting A) \<inter> ({A'} \<times> ?Meeting A') = {}"
      by auto 
  qed
    
  also have "... = (\<Sum> A \<in> \<F>. card (?Meeting A))"
    by (simp add: card_cartesian_product_singleton) (* card ({x} x A) = card A *)
  finally show ?thesis .
qed


(* There are k! * (n-k)! many linear permutations of S starting with A. *)
lemma card_linear_permutations_starting_with_A:
  assumes "A \<in> \<F>"
  shows "card {xs. set xs = S \<and> distinct xs \<and> set (take k xs) = A} = fact k * fact (n - k)"
proof -
  have "A \<subseteq> S" and "card A = k" and "finite A"
    using A_props[OF assms] by blast+
  let ?Rest = "S - A"
  have "card ?Rest = n - k"
    using card_S `A \<subseteq> S` `card A = k` finite_S card_Diff_subset finite_subset by meson
  have "finite ?Rest" 
    using finite_S by simp

  let ?PermsA = "{xs. set xs = A \<and> distinct xs}"
  let ?PermsRest = "{ys. set ys = ?Rest \<and> distinct ys}"
  let ?concat = "\<lambda>(xs, ys). xs @ ys"
  let ?PermsStartingWithA = "{xs. set xs = S \<and> distinct xs \<and> set (take k xs) = A}"

  (* Concatanetion function is a bijection between the two sets *)
  have "bij_betw ?concat (?PermsA \<times> ?PermsRest) ?PermsStartingWithA" unfolding bij_betw_def
  proof (intro conjI)
    (* Injectivity *)
    show "inj_on ?concat (?PermsA \<times> ?PermsRest)"
    proof (rule inj_onI)
      fix p1 p2
      assume p1: "p1 \<in> ?PermsA \<times> ?PermsRest" and p2: "p2 \<in> ?PermsA \<times> ?PermsRest"
      obtain p q where eq1: "p1 = (p, q)" by fastforce
      obtain p' q' where eq2: "p2 = (p', q')" by fastforce
      assume "?concat p1 = ?concat p2"
      then have "p @ q = p' @ q'" using eq1 eq2 by simp
      moreover have "length p = k" "length p' = k"
        using p1 p2 eq1 eq2 `card A = k` distinct_card by force+
      ultimately show "p1 = p2"
        using eq1 eq2 by simp
    qed

    (* Surjectivity *)
    show "?concat ` (?PermsA \<times> ?PermsRest) = ?PermsStartingWithA"
    proof (rule subset_antisym)
      (* "\<subseteq>": *)
      show "?concat ` (?PermsA \<times> ?PermsRest) \<subseteq> ?PermsStartingWithA"
      proof
        fix l assume "l \<in> ?concat ` (?PermsA \<times> ?PermsRest)"
        then obtain xs ys where l: "l = xs @ ys"
          and xs: "xs \<in> ?PermsA" and ys: "ys \<in> ?PermsRest" by auto
        have "set l = S" 
          using l xs ys `A \<subseteq> S` by auto
        moreover have "distinct l"
          using l xs ys by simp
        moreover have "length xs = k"
          using xs `card A = k` distinct_card by fastforce
        moreover from this have "set (take k l) = A"
          using l xs by simp
        ultimately show "l \<in> ?PermsStartingWithA" 
          by simp
      qed
    next
      (* "\<supseteq>": *)
      show "?PermsStartingWithA \<subseteq> ?concat ` (?PermsA \<times> ?PermsRest)"
      proof
        fix l assume l: "l \<in> ?PermsStartingWithA"
        let ?xs = "take k l"
        let ?ys = "drop k l"
        have "set ?xs = A" and "distinct ?xs"
          using l by simp+
        then have "?xs \<in> ?PermsA" 
          by simp

        have "set ?ys = set l - set ?xs"
        proof -
          have "distinct l" and "l = ?xs @ ?ys" 
            using l by simp+
          then have "set ?xs \<inter> set ?ys = {}"
            using distinct_append[of ?xs ?ys] by simp
          moreover have "set l = set ?xs \<union> set ?ys"
            using `l = ?xs @ ?ys` set_append by metis
          ultimately show ?thesis
            by blast
        qed
      
        then have "?ys \<in> ?PermsRest"
          using l by simp
        have "l = ?concat (?xs, ?ys)" 
          by simp
        then show "l \<in> ?concat ` (?PermsA \<times> ?PermsRest)"
          using `?xs \<in> ?PermsA` `?ys \<in> ?PermsRest` by blast
      qed
    qed
  qed

  then have "card ?PermsStartingWithA = card (?PermsA \<times> ?PermsRest)"
    using bij_betw_same_card[symmetric] by auto
  also have "... = card ?PermsA * card ?PermsRest"
    by (simp add: card_cartesian_product)
  also have "... = fact k * fact (n - k)"
    using card_linear_permutations[OF `finite A`] 
          card_linear_permutations[OF `finite ?Rest`]
          `card A = k` `card ?Rest = n - k` by simp
  finally show ?thesis .
qed


(* There is a bijection between the set of linear permutations of S starting with A 
   and the set of circular permutations of S meeting A *)
lemma bij_betw_linear_and_circular:
  assumes "A \<in> \<F>"
  shows "bij_betw (\<lambda>xs. {(x, y). x \<sim>c y} `` {xs})
          {xs. set xs = S \<and> distinct xs \<and> set (take k xs) = A}
          {C \<in> circular_permutations S. (\<forall> \<sigma> \<in> C. \<sigma> meets A)}"
proof -
  let ?PermsStartingWithA = "{xs. set xs = S \<and> distinct xs \<and> set (take k xs) = A}"
  let ?CPMeetingA = "{C \<in> circular_permutations S. (\<forall> \<sigma> \<in> C. \<sigma> meets A)}"
  let ?eq_class = "(\<lambda>xs. {(x, y). x \<sim>c y} `` {xs})"

  show "bij_betw ?eq_class ?PermsStartingWithA ?CPMeetingA" unfolding bij_betw_def
  proof (intro conjI)
    (* Injectivity: If two linear permutations starting with A are rotations 
       of one another, they are equal *)
    show "inj_on ?eq_class ?PermsStartingWithA"
    proof (rule inj_onI)
      fix xs ys assume xs: "xs \<in> ?PermsStartingWithA" and ys: "ys \<in> ?PermsStartingWithA"
      assume "?eq_class xs = ?eq_class ys"
      (* ys is a rotation of xs *)
      then have "xs \<sim>c ys"
        using c_reflexive circular_equiv_def Image_singleton_iff equiv_class_eq_iff equiv_circular 
        by auto
      then obtain m where m: "ys = rotate m xs" and "m < n"
        unfolding circular_equiv_def 
        using xs card_S distinct_card mod_less_divisor n_bound zero_less_numeral
        by (metis (mono_tags, lifting) k_pos le_antisym less_eq_nat.simps(1) 
            mem_Collect_eq mult_pos_pos not_gr_zero rotate_conv_mod)

      (* Proof of "xs = ys" by contradiction *)
      have "m = 0"
      proof (rule ccontr)
        assume "m \<noteq> 0" then have "0 < m" by simp
        (* by rotation *)
        have "xs ! m = ys ! 0"
          using m `m < n` xs card_S distinct_card nth_rotate
          by (metis (mono_tags, lifting) add.right_neutral length_pos_if_in_set
              mem_Collect_eq mod_less nth_mem)        
        (* Indices 0..k-1 are from A, in particular: *)
        also have "ys ! 0 \<in> A"
          using ys k_pos xs card_S distinct_card hd_in_set list.sel(1) take_hd_drop
          by (smt (verit) `m < n` gr_implies_not_zero hd_conv_nth hd_take length_0_conv
              mem_Collect_eq take_eq_Nil)
        finally have "xs ! m \<in> A" by simp
        (* Therefore, m < k, otherwise A would be outside of first k elements of xs *)
        then have "m < k"
          using  xs `m < n` card_S distinct_card distinct_conv_nth in_set_takeD less_trans nth_take
          by (smt (verit, ccfv_threshold) in_set_conv_nth length_take mem_Collect_eq min_less_iff_conj)

        (* A is exactly the indices 0..k-1, so: *)
        have "xs ! k \<notin> A"
          using xs n_bound k_pos card_S distinct_card
                distinct_conv_nth in_set_takeD linorder_not_less nth_take
          by (smt (verit, del_insts) add_diff_cancel_left' add_lessD1 diff_is_0_eq'
              distinct_Ex1 length_take mem_Collect_eq min_less_iff_conj mult_2 nat_less_le)

        (* Since m < k, (k - m) is positive, so by rotation: *)
        have "xs ! k = ys ! (k - m)"
          using m xs card_S distinct_card `m < n` nth_rotate `m < k` n_bound
          by (smt (verit) Nat.add_diff_assoc2 add_diff_inverse_nat add_less_same_cancel1 diff_commute 
              diff_is_0_eq' k_pos linorder_not_less mem_Collect_eq mod_less mult_2 nat_less_le)
        (* Since (k - m) < k, this is A territory *)
        also have "ys ! (k - m) \<in> A"
          by (smt (verit, best) A_props(1) `0 < m` `ys ! 0 \<in> A` add_diff_inverse_nat
              assms diff_commute diff_is_0_eq' distinct_card distinct_take less_diff_conv2
              linorder_not_less m mem_Collect_eq nat_less_le nth_mem nth_take ys)
        finally have "xs ! k \<in> A" by simp
        
        (* Contradiction: xs ! k is in A but it cannot be *)
        show False using `xs ! k \<in> A` `xs ! k \<notin> A` by simp
      qed
      then show "xs = ys" 
        using m by simp
    qed
  next
    (* Surjectivity: Every circular permutation meeting A is an equivalence class
       of a linear permutation starting with A. *)
    show "?eq_class ` ?PermsStartingWithA = ?CPMeetingA"
    proof (rule subset_antisym)
      (* "\<subseteq>": *)
      show "?eq_class ` ?PermsStartingWithA \<subseteq> ?CPMeetingA"
      proof
        fix C assume "C \<in> ?eq_class ` ?PermsStartingWithA"
        then obtain xs where "xs \<in> ?PermsStartingWithA" and "C = ?eq_class xs" 
          by auto
        then have "C \<in> circular_permutations S"
          using circular_permutations_def quotientI by (metis (lifting) mem_Collect_eq)
        (* xs starts with A, in particular meets it, so every p \<in> C meets A. *)
        have "xs meets A" 
          unfolding meets_def using `xs \<in> ?PermsStartingWithA`
          by (metis (mono_tags, lifting) mem_Collect_eq mod_self rotate_id)
        then have "\<forall>\<sigma> \<in> C. \<sigma> meets A"
          using meets_class_consistent[OF `C \<in> circular_permutations S`] `C = ?eq_class xs`
                Image_singleton_iff c_reflexive by (metis case_prod_conv mem_Collect_eq)
        then show "C \<in> ?CPMeetingA" 
          using `C \<in> circular_permutations S` by simp
      qed
    next
      (* "\<supseteq>": *)
      show "?CPMeetingA \<subseteq> ?eq_class ` ?PermsStartingWithA"
      proof
        fix C assume "C \<in> ?CPMeetingA"
        (* ys represents a circular permutation meeting A *)
        then obtain ys where "ys \<in> C" and "ys meets A" and "C \<in> circular_permutations S"
          using circular_permutations_def equiv_circular
          by (metis (no_types, lifting) UNIV_I equiv_class_self mem_Collect_eq quotientE)

        have "distinct ys" and  "ys \<noteq> []"
          using `C \<in> circular_permutations S` `ys \<in> C` \<sigma>_props by simp+
        (* Rotate ys to the position i where it starts with A *)
        obtain i j where "set (take j (rotate i ys)) = A" and "j = card A"
          using `ys meets A` meets_card[OF `ys meets A` `distinct ys` `ys \<noteq> []`] by blast
        (* since card A = k, we have: *)
        then have "set (take k (rotate i ys)) = A"
          using assms A_props by simp

        let ?xs = "rotate i ys" (* this is the rotated version of ys starting with A*)
        have "?xs \<in> ?PermsStartingWithA"
          using `ys \<in> C` `set (take k ?xs) = A` `C \<in> ?CPMeetingA` circular_permutations_def 
                quotient_def Union_iff distinct_rotate mem_Collect_eq set_rotate
          by (smt (verit, del_insts) Image_singleton_iff circular_equiv_def quotientE split_conv)
        moreover have "?eq_class ?xs = C"
          using `ys \<in> C` `C \<in> ?CPMeetingA` equiv_circular equiv_class_eq 
                circular_equiv_def length_rotate
          by (smt (verit, best) Image_singleton_iff case_prod_conv circular_permutations_def
              mem_Collect_eq  quotientE)
        ultimately show "C \<in> ?eq_class ` ?PermsStartingWithA" 
          by blast
      qed
    qed
  qed
qed


(* The number of circular permutations of S meeting A is k! * (n-k)! *)
lemma card_circular_permutations_meeting_A:
  assumes "A \<in> \<F>"
  shows "card {C \<in> circular_permutations S. (\<forall> \<sigma> \<in> C. \<sigma> meets A)} = fact k * fact (n - k)"
proof -
  let ?PermsStartingWithA = "{xs. set xs = S \<and> distinct xs \<and> set (take k xs) = A}"
  let ?eq_class = "(\<lambda>xs. {(x, y). x \<sim>c y} `` {xs})"
  let ?CPMeetingA = "{C \<in> circular_permutations S. (\<forall> \<sigma> \<in> C. \<sigma> meets A)}"

  have "bij_betw ?eq_class ?PermsStartingWithA ?CPMeetingA"
    using bij_betw_linear_and_circular[OF assms] .
  then have "card ?CPMeetingA = card ?PermsStartingWithA"
    using bij_betw_same_card by force
  also have "... = fact k * fact (n - k)"
    using card_linear_permutations_starting_with_A[OF assms] by simp
  finally show ?thesis .
qed


(* We had defined:
  "\<S> = {(A, C). A \<in> \<F> \<and> (C \<in> circular_permutations S) \<and> (\<forall>\<sigma> \<in> C. \<sigma> meets A)}"
  We double count this set. 
  On one hand, the size of \<S> is upper-bounded by (n-1)! * k, because decomposing \<S> by C,
  we have that there (n-1)! circular permutations and each of them is upper-bounded by k
  due to Katona result.
  On the other hand, the size of \<S> is exactly |\<F>| * k! * (n-k)!, because decomposing
  \<S> by A, we have |\<F>| many A's and for each them there are exactly k! * (n-k)! 
  circular permutations meeting A.  
*)
lemma \<S>_upper_bound:
  shows "card \<S> \<le> (fact (n - 1)) * k"
proof -
  have "card \<S> = (\<Sum> C \<in> circular_permutations S. card {A \<in> \<F>. (\<forall> \<sigma> \<in> C. \<sigma> meets A)})"
    using \<S>_decomposition_C by simp
  (* Use Katona to bound each term in the sum by k *)
  also have "... \<le> (\<Sum> C \<in> circular_permutations S. k)"
    using katona_circle_claim sum_mono by meson
  also have "... = card (circular_permutations S) * k"
    by simp 
  also have "... = fact (n - 1) * k"
    using card_circular_permutations_of_S by simp
  finally show ?thesis .
qed
lemma \<S>_equality:
  shows "card \<S> = card \<F> * (fact k) * (fact (n - k))"
proof -
  have "card \<S> = (\<Sum> A \<in> \<F>. card {C \<in> circular_permutations S. (\<forall> \<sigma> \<in> C. \<sigma> meets A)})"
    using \<S>_decomposition_by_A by simp
  also have "... = (\<Sum> A \<in> \<F>. fact k * fact (n - k))"
    using card_circular_permutations_meeting_A by simp
  also have "... = card \<F> * (fact k * fact (n - k))"
    by simp
  also have "... = card \<F> * fact k * fact (n - k)"
    by simp
  finally show ?thesis .
qed

(* So, the double counting argument yields that an intersecting k-family \<F> of an n-set S 
   is of size at most (n-1) choose (k-1) *)
theorem erdos_ko_rado_upper_bound:
  shows "card \<F> \<le> (n - 1) choose (k - 1)"
proof -
  have "card \<F> = (card \<S>) div ((fact k) * (fact (n - k)))" 
    using \<S>_equality by simp
  also have "... \<le> ((fact (n - 1)) * k) div ((fact k) * (fact (n - k)))"
    using \<S>_upper_bound div_le_mono by blast 
  also have "... = fact (n - 1) div (fact (k - 1) * fact (n - k))"
    by (metis div_mult2_eq div_mult_self_is_m k_pos fact_reduce of_nat_id)
  also have "... = fact (n - 1) div (fact (k - 1) * fact ((n - 1) - (k - 1)))"
    using k_pos by fastforce
  also have "... = (n - 1) choose (k - 1)" 
    using n_bound binomial_fact'
    by (metis (no_types, lifting) diff_le_mono le_add1 le_trans mult_2)
  finally show ?thesis .
qed
end


(* Moreover, this upper bound is tight. There is an intersecting family of k-subsets called "Star" 
   of an n-set s.t. Star is of size (n-1) choose (k-1) *)
lemma erdos_ko_rado_tight:
  fixes x :: 'a 
  fixes n k :: nat
  fixes S :: "'a set"
  assumes n_pos: "n > 0"
  assumes k_pos: "k > 0"
  assumes finite_S: "finite S"
  assumes card_S: "card S = n"
  assumes "x \<in> S"
  defines "Star \<equiv> {A \<in> {A. A \<subseteq> S \<and> card A = k}. x \<in> A}"
  shows "Star \<subseteq> {A. A \<subseteq> S \<and> card A = k}"
    and "intersecting Star" 
    and "card Star = (n - 1) choose (k - 1)"
proof -
  show "Star \<subseteq> {A. A \<subseteq> S \<and> card A = k}" 
    using Star_def by auto
  show "intersecting Star" 
    using Star_def intersecting_def by auto
    
  show "card Star = (n - 1) choose (k - 1)"
  proof -
    let ?S' = "S - {x}"
    let ?Comp_x = "{B. B \<subseteq> ?S' \<and> card B = k - 1}"
    have "finite ?S'" 
      using finite_S by simp
    have card_S': "card ?S' = n - 1" 
      using card_S `x \<in> S` finite_S by simp

    (* Star is the family of all k-subsets of S including x*)
    have star_eq: "Star = (insert x) ` ?Comp_x"
    proof (rule subset_antisym)
      (* "\<subseteq>": *)
      show "Star \<subseteq> (insert x) ` ?Comp_x"
      proof (rule subsetI)
        fix A assume "A \<in> Star"
        then have "A \<subseteq> S" and "card A = k" and "x \<in> A"
          using Star_def by auto
        let ?B = "A - {x}"
        have "?B \<subseteq> ?S'" 
          using `A \<subseteq> S` by auto
        moreover have "card ?B = k - 1" 
          using `card A = k` `x \<in> A` card_Diff_singleton by simp
        ultimately show "A \<in> (insert x) ` ?Comp_x"
          using `x \<in> A` image_eqI
          by (metis (full_types, lifting) insert_Diff_single insert_absorb mem_Collect_eq)
      qed    
    next
      (* "\<supseteq>": *)
      show "(insert x) ` ?Comp_x \<subseteq> Star"
      proof (rule subsetI)
        fix Y assume "Y \<in> (insert x) ` ?Comp_x"
        then obtain B where "Y = insert x B" and "B \<in> ?Comp_x" 
          by auto
        then have "B \<subseteq> S - {x}" and "card B = k - 1" 
          by auto
        have "x \<notin> B" 
          using `B \<subseteq> S - {x}` by auto
        have "finite B" 
          using `B \<subseteq> S - {x}` finite_S finite_subset by auto
        
        (* Y is in Star *)
        have "Y \<in> {A. A \<subseteq> S \<and> card A = k}"
        proof -
          have "insert x B \<subseteq> S" 
            using `B \<subseteq> S - {x}` `x \<in> S` by auto
          moreover have "card (insert x B) = k"
            using `card B = k - 1` `x \<notin> B` `finite B`
            by (metis Suc_pred' card_insert_disjoint k_pos)
          ultimately show ?thesis 
            using `Y = insert x B` by simp
        qed
        then show "Y \<in> Star"
          using Star_def `Y = insert x B` by simp
      qed
    qed

    (* Star if of size exactly the number of (k-1)-subsets "?Comp_x" of an (n-1)-set "?S'" *)
    have "card Star = card ((insert x) ` ?Comp_x)" 
      using star_eq by simp
    also have "... = card ?Comp_x"
    proof (rule card_image)
      show "inj_on (insert x) ?Comp_x"
        using inj_on_def by blast
    qed
    also have "... = (n - 1) choose (k - 1)"
      using n_subsets[OF `finite ?S'`, of "k - 1"] card_S' by simp
    finally show ?thesis .
  qed
qed


(* The final theorem: The maximum among the cardinalities of all intersecting families 
   of k-subsets of an n-set is exactly (n-1) choose (k-1). *)
theorem erdos_ko_rado:
  fixes n k :: nat
  fixes S :: "'a set"
  assumes finite_S: "finite S"
  assumes card_S: "card S = n"
  assumes n_pos: "n > 0"
  assumes k_pos: "k > 0"
  assumes n_bound: "2 * k \<le> n"
  shows "Max (card ` {F. F \<subseteq> {A. A \<subseteq> S \<and> card A = k} \<and> intersecting F}) = (n - 1) choose (k - 1)"
proof -
  let ?Families = "{F. F \<subseteq>  {A. A \<subseteq> S \<and> card A = k} \<and> intersecting F}"
  let ?Cards = "card ` ?Families"
  let ?bound = "(n - 1) choose (k - 1)"

  have "finite {A. A \<subseteq> S \<and> card A = k}" 
    using finite_S by auto
  then have fin_families: "finite ?Families" and fin_cards: "finite ?Cards" 
    by simp+
    
  (* Upper bound for all intersecting k-families *)
  have upper_bound: "\<forall>c \<in> ?Cards. c \<le> ?bound"
  proof
    (* Get an intersecting k-family of an arbitrary but fixed cardinality c *)
    fix c assume "c \<in> ?Cards"
    then obtain F where "F \<in> ?Families" and "card F = c" by auto
    interpret F_context: ekr_context n k S F
    proof
      show "finite S" by (rule finite_S)
      show "card S = n" by (rule card_S)
      show "0 < n" by (rule n_pos)
      show "0 < k" by (rule k_pos)
      show "2 * k \<le> n" by (rule n_bound)
      show "F \<subseteq> {A. A \<subseteq> S \<and> card A = k}" using `F \<in> ?Families` by auto
      show "intersecting F" using `F \<in> ?Families` by auto
    qed
    have "card F \<le> ?bound" 
      using F_context.erdos_ko_rado_upper_bound .
    then show "c \<le> ?bound" 
      using `card F = c` by simp
  qed

  (* Create an intersecting k-family "Star" claiming the bound *)
  have "S \<noteq> {}" 
    using n_bound k_pos card_S by auto
  then obtain x where "x \<in> S" 
    by blast
  let ?Star = "{A \<in> {A. A \<subseteq> S \<and> card A = k}. x \<in> A}"
  have star_in_families: "?Star \<in> ?Families" 
    using erdos_ko_rado_tight[OF n_pos k_pos finite_S card_S `x \<in> S`] by simp  
  moreover have star_card: "card ?Star = ?bound" 
    using erdos_ko_rado_tight[OF n_pos k_pos finite_S card_S `x \<in> S`] by simp
  ultimately have bound_in_counts: "?bound \<in> ?Cards"
    using image_iff by fastforce
  
  show ?thesis
    using Max_eqI bound_in_counts fin_cards upper_bound by meson 
qed

end
