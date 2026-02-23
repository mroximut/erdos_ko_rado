theory Arcs

imports Main List_Helper

begin

definition arc_of_cycle :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "arc_of_cycle arc cycle \<longleftrightarrow> (\<exists>n :: nat < length cycle. take (length arc) (rotate n cycle) = arc)"

definition n_arc_of_cycle :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "n_arc_of_cycle arc cycle n \<longleftrightarrow> arc_of_cycle arc cycle \<and> length arc = n"

definition arcs_of_cycle :: "'a list \<Rightarrow> 'a list set" where
  "arcs_of_cycle cycle = {arc :: 'a list. arc_of_cycle arc cycle}"

definition n_arcs_of_cycle :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list set" where
  "n_arcs_of_cycle cycle n = {arc \<in> arcs_of_cycle cycle. length arc = n}"

definition generate_n_arc :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "generate_n_arc cycle index arc_size = take arc_size (rotate index cycle)"

definition n_arc_indices :: "'a list \<Rightarrow> 'a list list \<Rightarrow> nat \<Rightarrow> nat set" where
  "n_arc_indices cycle arcs arc_size = {n :: nat. n < length cycle \<and> generate_n_arc cycle n arc_size \<in> set arcs}"

definition intersecting_lists :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "intersecting_lists first_list second_list \<longleftrightarrow> (\<exists>element \<in> set first_list. element \<in> set second_list)"

(*
 * A helper lemma that gives an invariant for the intersecting_lists definition
 *)
lemma intersecting_lists_eq: "intersecting_lists list1 list2 \<longleftrightarrow> set list1 \<inter> set list2 \<noteq> {}" using intersecting_lists_def by auto

definition intersecting_arcs :: "'a list list \<Rightarrow> 'a list  \<Rightarrow> bool" where
  "intersecting_arcs arcs cycle \<longleftrightarrow> (\<forall>arc \<in> set arcs. (arc_of_cycle arc cycle) \<and> (\<forall>other_arc \<in> set arcs. intersecting_lists arc other_arc))"

definition intersecting_n_arcs :: "'a list list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "intersecting_n_arcs arcs cycle n \<longleftrightarrow> intersecting_arcs arcs cycle \<and> (\<forall>arc \<in> set arcs. length arc = n)" 

definition index_distance :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "index_distance cycle_length first_index second_index = (if first_index > second_index
  then (Min {first_index - second_index, cycle_length - (first_index - second_index)})
  else (Min {second_index - first_index, cycle_length - (second_index - first_index)})) "

locale arc_context = 
  fixes cycle :: "'a list"
  fixes arcs :: "'a list list"
  fixes arc_size :: nat
  assumes cycle_size : "length cycle \<ge> 3"
  assumes cycle_elements_distinct : "distinct cycle"
  assumes fixed_arc_size: "\<forall>arc \<in> set arcs. n_arc_of_cycle arc cycle arc_size"
  assumes minimal_arc_size: "1 \<le> arc_size"
  assumes maximum_arc_size: "2 * arc_size \<le> length cycle"
  assumes intersecting_arcs: "intersecting_n_arcs arcs cycle arc_size"
  assumes distinct_arcs: "distinct arcs"
begin

(*
 * A helper that shows that the arc elements are distinct since the circle elements are distinct
 *)
lemma arcs_distinct:
  fixes arc :: "'a list"
  assumes "arc \<in> set arcs"
  shows "distinct arc" by (metis arc_of_cycle_def assms cycle_elements_distinct distinct_rotate 
    distinct_take fixed_arc_size n_arc_of_cycle_def)

lemma arc_size: "arc_size > 0" using minimal_arc_size by auto

lemma index_of_arc_elements_exist:
  fixes arc :: "'a list"
  fixes arc_element :: "'a"
  assumes "arc \<in> set arcs"
  assumes "arc_element \<in> set arc"
  shows "index_of_element arc_element cycle < length cycle"
  by (smt (verit) add.right_neutral arc_of_cycle_def assms(1,2) fixed_arc_size in_set_conv_nth 
    index_limit maximum_arc_size mod_less_divisor mult_2 n_arc_of_cycle_def nat_int_comparison(2) 
    nat_less_le not_add_less2 not_contains_impl_not_elem not_in_list nth_rotate nth_take)


(*
 *  Two n-arcs starting from different points are different n-arcs due to the cycle not containing
 *  duplicate elements 
 *)
lemma unique_index_unique_arc:
  fixes n1 n2 :: nat 
  assumes "n1 < length cycle"
  assumes "n2 < length cycle"
  shows "n1 \<noteq> n2 \<longleftrightarrow> generate_n_arc cycle n1 arc_size \<noteq> generate_n_arc cycle n2 arc_size"
  by (metis Ex_list_of_length assms(1,2) cycle_elements_distinct cycle_size distinct_conv_nth
      generate_n_arc_def hd_rotate_conv_nth hd_take length_greater_0_conv less_not_refl 
      minimal_arc_size mod_less one_eq_numeral_iff order_less_le_trans zero_neq_numeral)

(*
 * Similar lemma to the before also obtaining the fact that non-equal arcs having different 
 * generator indexes
 *)
lemma unique_generating_indices:
  fixes arc1 arc2:: "'a list"
  fixes index1 index2 :: "nat"
  assumes "arc1 \<in> set arcs"
  assumes "arc2 \<in> set arcs"
  assumes "index1 < length cycle"
  assumes "index2 < length cycle"
  assumes "generate_n_arc cycle index1 arc_size = arc1"
  assumes "generate_n_arc cycle index2 arc_size = arc2"
  shows "index1 = index2 \<longleftrightarrow> arc1 = arc2" using assms(3,4,5,6) unique_index_unique_arc by blast


(*
 * For every n-arc exists an index from which the n-arc can be generated from.
 *)
lemma generating_index_exists: "arc \<in> set arcs \<longrightarrow> (\<exists>index < length cycle. generate_n_arc cycle index arc_size = arc)"
  by (metis arc_of_cycle_def fixed_arc_size generate_n_arc_def n_arc_of_cycle_def)

(*
 * Obtains rule for getting the generator for an arc
 *)
lemma get_generator_index:
  fixes arc :: "'a list"
  assumes "arc \<in> set arcs"
  obtains index where "generate_n_arc cycle index arc_size = arc \<and> index < length cycle" 
  using generating_index_exists assms by auto


(*
 * Helper lemma
 *)
lemma generator_indices_surjective: "\<forall>arc \<in> set arcs. \<exists>index \<in> n_arc_indices cycle arcs arc_size. (generate_n_arc cycle index arc_size = arc)"
  by (metis (no_types, lifting) get_generator_index mem_Collect_eq n_arc_indices_def)


(*
 * Helper lemma
 *)
lemma generator_indices_function:
  shows "\<forall>index \<in> n_arc_indices cycle arcs arc_size. \<exists>arc \<in> set arcs. (generate_n_arc cycle index arc_size = arc)" by (simp add: n_arc_indices_def)


(*
 * The set of arcs are generated by generating the n-arcs by the indexes of the heads of the arcs
 *)
lemma generator_index_bijection: "set arcs =  (\<lambda>index. generate_n_arc cycle index arc_size) ` (n_arc_indices cycle arcs arc_size)" 
  using generator_indices_function generator_indices_surjective by fastforce


(*
 * Lemma showing that the generate_n_arc defines a bijective function using the helper lemmas
 *)
lemma indices_are_representative: "bij_betw (\<lambda>x. generate_n_arc cycle x arc_size) (n_arc_indices cycle arcs arc_size) (set arcs)" 
  by (smt (verit, ccfv_threshold) bij_betwI'
      generator_indices_surjective mem_Collect_eq n_arc_indices_def
      unique_generating_indices)

(*
 * A further fact obtained from the bijection: index set of the heads of the arcs have the same
 * cardinality to the arcs set
 *)
lemma index_set_size: "length arcs = card (n_arc_indices cycle arcs arc_size)"
  by (metis bij_betw_same_card distinct_arcs distinct_card indices_are_representative)


(*
 * The index of the first element of the n-arc is also the generator for the n-arc
 *)
lemma arc_generator_head:
  fixes arc :: "'a list"
  assumes "arc \<in> set arcs"
  shows "generate_n_arc cycle (index_of_element (hd arc) cycle) arc_size = arc" 
proof (rule ccontr)
  assume assumption: "generate_n_arc cycle (index_of_element (hd arc) cycle) arc_size \<noteq> arc"
  obtain index where "generate_n_arc cycle index arc_size = arc" using assms generator_index_bijection 
    by auto
  have "hd arc \<in> set cycle"
  proof -
    have "hd (generate_n_arc cycle index arc_size) \<in> set cycle" 
      by (metis \<open>generate_n_arc cycle index arc_size = arc\<close> assms fixed_arc_size generate_n_arc_def 
        in_set_takeD linorder_not_less list.set_sel(1) list.size(3) minimal_arc_size 
        n_arc_of_cycle_def set_rotate zero_less_one)
    then show "hd arc \<in> set cycle"  using \<open>generate_n_arc cycle index arc_size = arc\<close> by blast
  qed
  from assumption have "index \<noteq> (index_of_element (hd arc) cycle)"
  using assumption \<open>generate_n_arc cycle index arc_size = arc\<close> by fastforce
  show "False"
    by (metis One_nat_def \<open>hd arc \<in> set cycle\<close> assms assumption cycle_elements_distinct distinct_Ex1 
    generate_n_arc_def generating_index_exists hd_rotate_conv_nth hd_take index_correct index_limit 
    length_pos_if_in_set less_eq_Suc_le list.size(3) minimal_arc_size mod_if nat_less_le 
    not_contains_impl_not_elem not_in_list)
qed


(*
 * A corollary that shows that the arc heads are identifiers for that arc
 *)
lemma arc_heads_define_n_arcs:
  fixes arc1 arc2 :: "'a list"
  assumes "arc1 \<in> set arcs"
  assumes "arc2 \<in> set arcs"
  shows "hd arc1 = hd arc2 \<longleftrightarrow> arc1 = arc2" by (metis assms(2) assms(1) arc_generator_head)


(*
 * A corollary that uses the fact before to show that the list of heads generated from an arc don't
 * have duplicates
 *) 
lemma heads_eq: "distinct (map (\<lambda>x. hd x) arcs)" by (smt (verit, ccfv_SIG) arc_heads_define_n_arcs 
  distinct_arcs distinct_conv_nth length_map nth_map nth_mem)


(*
 * A lemma that relates the index of an element in an arc to the index of the same element in the 
 * circular permutation and the index of the head of the arc in the cycle.
 *)
lemma arc_indices_to_cycle_indices:
  fixes arc :: "'a list"
  fixes arc_element :: "'a"
  fixes arc_index :: "nat"
  assumes "arc_index < arc_size"
  assumes "arc \<in> set arcs"
  assumes "arc_element \<in> set arc"
  shows "arc ! arc_index = arc_element \<longrightarrow> (\<exists>rotate_number < length cycle. cycle ! ((rotate_number + arc_index) mod (length cycle)) = arc_element)"
proof
  assume "arc ! arc_index = arc_element"
  obtain rotate_index where "rotate_index < length cycle \<and> generate_n_arc cycle rotate_index arc_size = arc" 
    by (metis generating_index_exists assms(2))
  then have witness: "cycle ! ((rotate_index + arc_index) mod (length cycle)) = arc_element"
    by (smt (verit) \<open>arc ! arc_index = arc_element\<close> assms(1) generate_n_arc_def leD maximum_arc_size 
      mult_2 nat_int_comparison(2) not_add_less2 nth_rotate nth_take)
  then show "\<exists>rotate_number < length cycle. cycle ! ((rotate_number + arc_index) mod (length cycle)) = arc_element"
    using \<open>rotate_index < length cycle \<and> generate_n_arc cycle rotate_index arc_size = arc\<close> by blast
qed


(*
 *
 *)
lemma indices_in_arc:
  fixes arc :: "'a list"
  fixes arc_head :: "'a"
  fixes arc_head_index :: "nat"
  fixes arc_element :: "'a"
  assumes "arc \<in> set arcs"
  assumes "arc_element \<in> set arc"
  assumes "arc_head = hd arc"
  assumes "arc_head_index = index_of_element arc_head cycle"
  shows "\<exists>index < arc_size. cycle ! ((arc_head_index + index) mod (length cycle)) = arc_element"
  by (metis add_leE arc_generator_head assms(1,2,3,4) fixed_arc_size generate_n_arc_def in_set_conv_nth maximum_arc_size mult_2
      n_arc_of_cycle_def nth_rotate nth_take order_less_le_trans)


(*
 * A lemma that provides another invariant for checking whether an element is in an arc.
 *)
lemma elements_of_arc:
  fixes arc :: "'a list"
  fixes arc_head :: "'a"
  fixes arc_head_index :: "nat"
  fixes cycle_element :: "'a"
  assumes "arc \<in> set arcs"
  assumes "arc_head = hd arc"
  assumes "arc_head_index = index_of_element arc_head cycle"
  shows "(\<exists>shift < arc_size. cycle ! ((arc_head_index + shift) mod (length cycle)) = cycle_element) \<longrightarrow> cycle_element \<in> set arc" 
    by (metis add_leE arc_generator_head assms(1,2,3) fixed_arc_size generate_n_arc_def 
    in_set_conv_nth maximum_arc_size mult_2 n_arc_of_cycle_def nth_rotate nth_take 
    order_less_le_trans)


(*
 * 
 *)
lemma indices_of_arc_elements:
  fixes arc :: "'a list"
  fixes arc_head :: "'a"
  fixes arc_head_index :: "nat"
  fixes arc_element :: "'a"
  assumes "arc \<in> set arcs"
  assumes "arc_element \<in> set arc"
  assumes "arc_head = hd arc"
  assumes "arc_head_index = index_of_element arc_head cycle"
  shows "cycle ! ((arc_head_index + (index_of_element arc_element arc)) mod (length cycle)) = arc_element" 
  by (metis (no_types, lifting) add_leE arc_generator_head assms(1,2,3,4) fixed_arc_size generate_n_arc_def 
     index_correct index_limit maximum_arc_size mult_2 n_arc_of_cycle_def nat_less_le not_contains_impl_not_elem 
     not_in_list nth_rotate nth_take order_less_le_trans)


(*
 *
 *)
lemma arc_element_index_to_cycle_index:
  fixes arc :: "'a list"
  fixes arc_head :: "'a"
  fixes arc_head_index :: "nat"
  fixes arc_element :: "'a"
  assumes "arc \<in> set arcs"
  assumes "arc_element \<in> set arc"
  assumes "arc_head = hd arc"
  assumes "arc_head_index = index_of_element arc_head cycle"
  shows "index_of_element arc_element cycle = (arc_head_index + index_of_element arc_element arc) mod (length cycle)"
  by (metis antisym_conv1 assms(1,2,3,4) bot_nat_0.extremum_unique contains_eq_elem cycle_elements_distinct 
    cycle_size distinct_conv_nth index_correct index_limit indices_of_arc_elements linorder_le_less_linear 
    mod_less_divisor not_in_list nth_mem zero_neq_numeral) 


(*
 *
 *)
lemma head_distance_intersecting:
  fixes first_arc second_arc :: "'a list"
  fixes first_head second_head :: "'a"
  fixes first_head_index second_head_index shift_index :: "nat"
  assumes "first_arc \<in> set arcs"
  assumes "second_arc \<in> set arcs"
  assumes "first_head = hd first_arc"
  assumes "second_head = hd second_arc"
  assumes "first_head_index = index_of_element first_head cycle"
  assumes "second_head_index = index_of_element second_head cycle"
  assumes "shift_index < arc_size"
  shows "(first_head_index + shift_index) mod (length cycle) = second_head_index \<longrightarrow> intersecting_lists first_arc second_arc"
  using assms(1,2) intersecting_arcs intersecting_arcs_def intersecting_n_arcs_def by blast 


lemma non_wrapping_arcs:
  fixes arc :: "'a list"
  fixes arc_index :: "nat"
  fixes arc_element :: "'a"
  fixes arc_element_index :: "nat"
  fixes arc_element_arc_index :: "nat"
  assumes "arc \<in> set arcs"
  assumes "arc_element \<in> set arc"
  assumes "arc_index = index_of_element (hd arc) cycle"
  assumes "arc_element_index = index_of_element arc_element cycle" 
  assumes "arc_element_arc_index = index_of_element arc_element arc"
  assumes "arc_index + arc_size < length cycle + 1"
  shows "arc_index \<le> arc_element_index"
proof -
  have "arc_element_arc_index < arc_size"  by (metis assms(1,2,5) index_limit intersecting_arcs 
        intersecting_n_arcs_def nat_less_le not_contains_impl_not_elem not_in_list)
  have "arc_index + arc_element_arc_index < length cycle" using \<open>arc_element_arc_index < arc_size\<close> assms(6) by force
  have "arc_element_index = (arc_index + arc_element_arc_index) mod (length cycle)" using arc_element_index_to_cycle_index assms(1,2,3,4,5) by blast
  then have "... = arc_index + arc_element_arc_index" using \<open>arc_index + arc_element_arc_index < length cycle\<close> mod_less by blast
  then have "... \<ge> arc_index" by simp
  then show ?thesis using \<open>(arc_index + arc_element_arc_index) mod length cycle = arc_index + arc_element_arc_index\<close> 
      \<open>arc_element_index = (arc_index + arc_element_arc_index) mod length cycle\<close> by presburger
qed


lemma wrapping_arcs:
  fixes arc :: "'a list"
  fixes arc_index :: "nat"
  fixes arc_element :: "'a"
  fixes arc_element_index :: "nat"
  fixes arc_element_arc_index :: "nat"
  assumes "arc \<in> set arcs"
  assumes "arc_element \<in> set arc"
  assumes "arc_index = index_of_element (hd arc) cycle"
  assumes "arc_element_index = index_of_element arc_element cycle" 
  assumes "arc_element_arc_index = index_of_element arc_element arc"
  assumes "arc_index + arc_element_arc_index \<ge> length cycle"
  shows "arc_element_index < (arc_index + arc_size) mod (length cycle) \<and> arc_element_index < arc_index"
proof -
  have "arc_index < length cycle" by (metis assms(1,2,3) index_of_arc_elements_exist length_pos_if_in_set less_not_refl list.set_sel(1) list.size(3))
  have "arc_size < length cycle" using arc_size maximum_arc_size by auto
  have "length cycle \<le> arc_index + arc_size \<and> arc_index + arc_size \<le> 2 * length cycle" by (metis add_le_mono assms(1,3,5,6) index_limit intersecting_arcs intersecting_n_arcs_def le_add2 le_trans maximum_arc_size mult_2 nat_add_left_cancel_le)
  have "arc_index + arc_element_arc_index < arc_index + arc_size" by (metis antisym_conv2 assms(1,2,5) index_limit intersecting_arcs intersecting_n_arcs_def nat_add_left_cancel_less not_contains_impl_not_elem not_in_list)
  then have "(arc_index + arc_element_arc_index) mod (length cycle) < (arc_index + arc_size) mod (length cycle)" 
    by (smt (verit, ccfv_SIG) \<open>arc_size < length cycle\<close> \<open>length cycle \<le> arc_index + arc_size \<and> arc_index + arc_size \<le> 2 * length cycle\<close>
        \<open>length cycle \<le> arc_index + arc_size \<and> arc_index + arc_size \<le> 2 * length cycle\<close> add_less_cancel_right 
        add_mono_thms_linordered_field(4) assms(3,6) index_limit leD le_add_diff_inverse2 less_diff_conv 
        mod_if mult_2 order_less_le_trans)
  then have "arc_element_index < (arc_index + arc_size) mod (length cycle)" by (metis arc_element_index_to_cycle_index assms(1,2,3,4,5))
  show ?thesis by (smt (verit, ccfv_threshold) \<open>arc_element_index < (arc_index + arc_size) mod length cycle\<close> 
        \<open>length cycle \<le> arc_index + arc_size \<and> arc_index + arc_size \<le> 2 * length cycle\<close> add.commute
        dual_order.strict_trans1 le_add_diff_inverse2 maximum_arc_size mod_if mod_less_eq_dividend 
        mult_2 nat_add_left_cancel_less nat_less_le verit_comp_simplify1(3))
qed


lemma not_in_arc:
  fixes cycle_element :: "'a"
  fixes arc :: "'a list"
  assumes "arc \<in> set arcs"
  assumes "cycle_element \<in> set cycle"
  shows "cycle_element \<notin> set arc \<longleftrightarrow> index_of_element cycle_element cycle \<notin> (\<lambda>x . index_of_element x cycle) ` set arc" 
    by (smt (verit) assms(2) imageE imageI index_correct not_contains_impl_not_elem not_in_list)


lemma head_distance_intersecting_distance:
  fixes first_arc second_arc :: "'a list"
  fixes first_head second_head :: "'a"
  fixes first_head_index second_head_index shift_index :: "nat"
  assumes "first_arc = generate_n_arc cycle first_head_index arc_size"
  assumes "second_arc = generate_n_arc cycle second_head_index arc_size"
  assumes "first_head = hd first_arc"
  assumes "second_head = hd second_arc"
  assumes "first_head_index = index_of_element first_head cycle"
  assumes "second_head_index = index_of_element second_head cycle"
  shows "index_distance (length cycle) first_head_index second_head_index < arc_size \<longrightarrow> intersecting_lists first_arc second_arc"
proof (rule impI)
  assume "index_distance (length cycle) first_head_index second_head_index < arc_size"
  
(* Step 1: Unfold the distance definition into the 4 possible linear cases *)
  hence dist_cases: 
    "(first_head_index \<ge> second_head_index \<and> first_head_index - second_head_index < arc_size) \<or>
     (first_head_index \<ge> second_head_index \<and> length cycle - (first_head_index - second_head_index) < arc_size) \<or>
     (second_head_index \<ge> first_head_index \<and> second_head_index - first_head_index < arc_size) \<or>
     (second_head_index \<ge> first_head_index \<and> length cycle - (second_head_index - first_head_index) < arc_size)"
  proof (cases "first_head_index > second_head_index")
    case True
    then have "first_head_index \<ge> second_head_index" by simp
    moreover have "Min {first_head_index - second_head_index, length cycle - (first_head_index - second_head_index)} < arc_size"
      using \<open>index_distance (length cycle) first_head_index second_head_index < arc_size\<close> True 
      unfolding index_distance_def by simp
    ultimately show ?thesis by force
  next
    case False
    then have "second_head_index \<ge> first_head_index" by simp
    moreover have "Min {second_head_index - first_head_index, length cycle - (second_head_index - first_head_index)} < arc_size"
      using \<open>index_distance (length cycle) first_head_index second_head_index < arc_size\<close> False 
      unfolding index_distance_def by simp
    ultimately show ?thesis by force
  qed
  (* Step 2: Explicitly construct the offsets k and m where the arcs intersect *)
  have shared_element_exists: "\<exists>k < arc_size. \<exists>m < arc_size. (first_head_index + k) mod length cycle = (second_head_index + m) mod length cycle"
    using dist_cases
  proof (elim disjE)
    assume a: "first_head_index \<ge> second_head_index \<and> first_head_index - second_head_index < arc_size"
    have "(first_head_index + 0) mod length cycle = (second_head_index + (first_head_index - second_head_index)) mod length cycle"
      using a by simp
    thus ?thesis using a minimal_arc_size
    using arc_size by blast
  next
    assume a: "first_head_index \<ge> second_head_index \<and> length cycle - (first_head_index - second_head_index) < arc_size"
    have "(first_head_index + (length cycle - (first_head_index - second_head_index))) = length cycle + second_head_index"
      using a
    by (simp add: add.commute assms(5)
        index_limit
        trans_le_add2)
    hence "(first_head_index + (length cycle - (first_head_index - second_head_index))) mod length cycle = (length cycle + second_head_index) mod length cycle"
      by simp
    also have "... = second_head_index mod length cycle"
      by simp
    also have "... = (second_head_index + 0) mod length cycle"
      by simp
    finally have "(first_head_index + (length cycle - (first_head_index - second_head_index))) mod length cycle = (second_head_index + 0) mod length cycle" .
    thus ?thesis using a minimal_arc_size
    using arc_size by blast
  next
    assume a: "second_head_index \<ge> first_head_index \<and> second_head_index - first_head_index < arc_size"
    have "(second_head_index + 0) mod length cycle = (first_head_index + (second_head_index - first_head_index)) mod length cycle"
      using a by simp
    hence "(first_head_index + (second_head_index - first_head_index)) mod length cycle = (second_head_index + 0) mod length cycle"
      by simp
    thus ?thesis using a minimal_arc_size
    using arc_size by blast
  next
    assume a: "second_head_index \<ge> first_head_index \<and> length cycle - (second_head_index - first_head_index) < arc_size"
    have "(second_head_index + (length cycle - (second_head_index - first_head_index))) = length cycle + first_head_index"
      using a
    by (simp add: add.commute assms(6)
        index_limit
        trans_le_add2)
    hence "(second_head_index + (length cycle - (second_head_index - first_head_index))) mod length cycle = (length cycle + first_head_index) mod length cycle"
      by simp
    also have "... = first_head_index mod length cycle"
      by simp
    also have "... = (first_head_index + 0) mod length cycle"
      by simp
    finally have "(second_head_index + (length cycle - (second_head_index - first_head_index))) mod length cycle = (first_head_index + 0) mod length cycle" .
    hence "(first_head_index + 0) mod length cycle = (second_head_index + (length cycle - (second_head_index - first_head_index))) mod length cycle"
      by simp
    thus ?thesis using a minimal_arc_size
    using arc_size by blast
  qed

  then obtain k m where "k < arc_size" and "m < arc_size" 
    and match_eq: "(first_head_index + k) mod length cycle = (second_head_index + m) mod length cycle"
    by blast

  (* Step 3: Prove that the matched indices fall inside both arcs *)
  have elem_in_first: "cycle ! ((first_head_index + k) mod length cycle) \<in> set first_arc"
  proof -
    have "length (rotate first_head_index cycle) = length cycle" by simp
    moreover have "arc_size \<le> length cycle" using maximum_arc_size by linarith
    ultimately have "length first_arc = arc_size" 
      using assms(1) unfolding generate_n_arc_def by simp
    hence "first_arc ! k \<in> set first_arc" using \<open>k < arc_size\<close> nth_mem by blast
    moreover have "first_arc ! k = rotate first_head_index cycle ! k"
      using assms(1) \<open>k < arc_size\<close> unfolding generate_n_arc_def by simp
    moreover have "rotate first_head_index cycle ! k = cycle ! ((first_head_index + k) mod length cycle)"
    by (meson
        \<open>arc_size \<le> length cycle\<close>
        \<open>k < arc_size\<close> nth_rotate
        order_less_le_trans)
    ultimately show ?thesis by simp
  qed

  have elem_in_second: "cycle ! ((second_head_index + m) mod length cycle) \<in> set second_arc"
  proof -
    have "length (rotate second_head_index cycle) = length cycle" by simp
    moreover have "arc_size \<le> length cycle" using maximum_arc_size by linarith
    ultimately have "length second_arc = arc_size" 
      using assms(2) unfolding generate_n_arc_def by simp
    hence "second_arc ! m \<in> set second_arc" using \<open>m < arc_size\<close> nth_mem by blast
    moreover have "second_arc ! m = rotate second_head_index cycle ! m"
      using assms(2) \<open>m < arc_size\<close> unfolding generate_n_arc_def by simp
    moreover have "rotate second_head_index cycle ! m = cycle ! ((second_head_index + m) mod length cycle)"
    by (meson
        \<open>arc_size \<le> length cycle\<close>
        \<open>m < arc_size\<close> nth_rotate
        order_less_le_trans)
    ultimately show ?thesis by simp
  qed

  (* Step 4: Conclude they intersect using our definition directly *)
  show "intersecting_lists first_arc second_arc"
    unfolding intersecting_lists_def
    using elem_in_first elem_in_second match_eq by force
qed

lemma intersecting_endpoints_part1:
  fixes arc1 arc2 :: "'a list"
  fixes arc1_head_index arc2_head_index arc_distance:: "nat"
  assumes "arc1 \<in> set arcs"
  assumes "arc2 \<in> set arcs"
  assumes "arc1_head_index = index_of_element (hd arc1) cycle"
  assumes "arc2_head_index = index_of_element (hd arc2) cycle"
  assumes "arc1_head_index < arc2_head_index"
  assumes "arc_distance = arc2_head_index - arc1_head_index"
  shows "hd arc2 \<in> set arc1 \<or> last arc2 \<in> set arc1"
proof (cases)
  assume "arc_distance < arc_size"
  then have "(arc1_head_index + arc_distance) mod (length cycle) = arc2_head_index" 
    by (metis add.commute arc_size assms(2,4,5,6) index_of_arc_elements_exist intersecting_arcs 
        intersecting_n_arcs_def le_add_diff_inverse2 list.set_sel(1) list.size(3) mod_less
        nat_less_le)
  then have "hd arc2 \<in> set arc1" by (metis \<open>arc_distance < arc_size\<close> assms(1,3,4) elements_of_arc generating_index_exists index_correct less_not_refl less_zeroE mod_less_divisor not_gr_zero not_in_list)
  then show ?thesis by simp
next
  assume "\<not>(arc_distance < arc_size)"
  then have "arc_distance \<ge> arc_size" by simp
  have "arc2_head_index + arc_size \<ge> length cycle"
  proof (rule ccontr)
    assume "\<not>(arc2_head_index + arc_size \<ge> length cycle)"
    then have arc2_indices: "arc2_head_index + arc_size < length cycle" by simp
    have "\<forall>arc_element \<in> set arc1. index_of_element arc_element cycle < arc2_head_index" 
    proof
      fix x
      assume "x \<in> set arc1"
      have "arc1_head_index + arc_size < length cycle" using arc2_indices assms(5) by fastforce
      also have "index_of_element x arc1 < arc_size" by (metis \<open>x \<in> set arc1\<close> assms(1) index_limit intersecting_arcs intersecting_n_arcs_def nat_less_le not_contains_impl_not_elem not_in_list)
      then have "index_of_element x cycle = arc1_head_index + index_of_element x arc1" using \<open>x \<in> set arc1\<close> arc_element_index_to_cycle_index assms(1,3) calculation by force
      then have "... < arc2_head_index" using \<open>arc_size \<le> arc_distance\<close> \<open>index_of_element x arc1 < arc_size\<close> assms(6) by linarith
      then show "index_of_element x cycle < arc2_head_index" using \<open>index_of_element x cycle = arc1_head_index + index_of_element x arc1\<close> by auto
    qed
    have "\<forall>arc_element \<in> set arc2. index_of_element arc_element cycle \<ge> arc2_head_index" using \<open>\<not> length cycle \<le> arc2_head_index + arc_size\<close> assms(2,4) non_wrapping_arcs by auto
    then have "set arc1 \<inter> set arc2 = {}" using \<open>\<forall>arc_element\<in>set arc1. index_of_element arc_element cycle < arc2_head_index\<close> by fastforce
    then have "\<not>intersecting_lists arc1 arc2" by (simp add: intersecting_lists_eq)
    then show False by (metis \<open>\<not> intersecting_lists arc1 arc2\<close> assms(1) intersecting_arcs assms(2) intersecting_n_arcs_def intersecting_arcs_def)
  qed
 have "last arc2 \<in> set arc1"
  proof -
    have len1: "length arc1 = arc_size" and len2: "length arc2 = arc_size"
      using assms(1,2) intersecting_arcs intersecting_n_arcs_def by auto

    have "intersecting_lists arc1 arc2"
      using assms(1,2) intersecting_arcs intersecting_arcs_def intersecting_n_arcs_def by blast
    then obtain x where "x \<in> set arc1" and "x \<in> set arc2"
      unfolding intersecting_lists_def by auto

    have "\<exists>idx1 < arc_size. x = arc1 ! idx1"
      by (metis \<open>x \<in> set arc1\<close> in_set_conv_nth len1)
    then obtain idx1 where "idx1 < arc_size" and "x = arc1 ! idx1" by blast

    have "\<exists>idx2 < arc_size. x = arc2 ! idx2"
      by (metis \<open>x \<in> set arc2\<close> in_set_conv_nth len2)
    then obtain idx2 where "idx2 < arc_size" and "x = arc2 ! idx2" by blast

    have arc1_gen: "arc1 = generate_n_arc cycle arc1_head_index arc_size"
      using assms(1,3) arc_generator_head by simp
    have arc2_gen: "arc2 = generate_n_arc cycle arc2_head_index arc_size"
      using assms(2,4) arc_generator_head by simp

    have x_val1: "x = cycle ! ((arc1_head_index + idx1) mod length cycle)"
      using \<open>x = arc1 ! idx1\<close> arc1_gen \<open>idx1 < arc_size\<close>
      unfolding generate_n_arc_def
    by (metis
        \<open>arc_size \<le> arc_distance\<close>
        add_diff_inverse_nat
        assms(4,5,6) index_limit le_add2
        nat_less_le nth_rotate nth_take
        order_less_le_trans)

    have x_val2: "x = cycle ! ((arc2_head_index + idx2) mod length cycle)"
      using \<open>x = arc2 ! idx2\<close> arc2_gen \<open>idx2 < arc_size\<close>
      unfolding generate_n_arc_def
    by (metis
        \<open>arc_size \<le> arc_distance\<close>
        assms(4,6) diff_le_self
        index_limit nth_rotate nth_take
        order_less_le_trans)

    have arc1_bound: "arc1_head_index + idx1 < length cycle"
      using \<open>arc_distance \<ge> arc_size\<close> assms(5,6) \<open>idx1 < arc_size\<close>
    by (metis add_diff_inverse_nat
        assms(4) index_limit
        nat_add_left_cancel_less
        nat_less_le
        order_less_le_trans)
    hence x_cycle_idx1: "((arc1_head_index + idx1) mod length cycle) = arc1_head_index + idx1"
      by simp

    have "arc_size > 0" using minimal_arc_size by auto
    hence "hd arc2 \<in> set arc2" using len2 by (metis hd_in_set length_greater_0_conv)
    hence arc2_head_bound: "arc2_head_index < length cycle"
      using assms(2,4) index_of_arc_elements_exist by metis

    have wrap2: "arc2_head_index + idx2 \<ge> length cycle"
    proof (rule ccontr)
      assume "\<not> (arc2_head_index + idx2 \<ge> length cycle)"
      hence "arc2_head_index + idx2 < length cycle" by simp
      hence x_cycle_idx2_false: "((arc2_head_index + idx2) mod length cycle) = arc2_head_index + idx2" by simp
      
      have "cycle ! (arc1_head_index + idx1) = cycle ! (arc2_head_index + idx2)"
        using x_val1 x_val2 x_cycle_idx1 x_cycle_idx2_false by simp
      hence "arc1_head_index + idx1 = arc2_head_index + idx2"
        using cycle_elements_distinct arc1_bound \<open>arc2_head_index + idx2 < length cycle\<close>
        by (simp add: nth_eq_iff_index_eq)
      
      moreover have "arc1_head_index + idx1 < arc2_head_index"
        using assms(6) \<open>arc_distance \<ge> arc_size\<close> \<open>idx1 < arc_size\<close> by linarith
      ultimately show False by simp
    qed

    have "arc2_head_index + idx2 < 2 * length cycle"
      using arc2_head_bound \<open>idx2 < arc_size\<close> maximum_arc_size by linarith
    hence wrap2_mod: "((arc2_head_index + idx2) mod length cycle) = arc2_head_index + idx2 - length cycle"
      using wrap2 by (simp add: mod_if)

    have "cycle ! (arc1_head_index + idx1) = cycle ! (arc2_head_index + idx2 - length cycle)"
      using x_val1 x_val2 x_cycle_idx1 wrap2_mod by simp
    moreover have "arc2_head_index + idx2 - length cycle < length cycle"
      using arc2_head_bound \<open>idx2 < arc_size\<close> maximum_arc_size by linarith
    ultimately have match_idx: "arc1_head_index + idx1 = arc2_head_index + idx2 - length cycle"
      using cycle_elements_distinct arc1_bound
      by (simp add: nth_eq_iff_index_eq)

    have last_idx: "last arc2 = arc2 ! (arc_size - 1)"
      using len2 \<open>arc_size > 0\<close>
    using last_conv_nth
    by auto

    have last_val: "last arc2 = cycle ! ((arc2_head_index + arc_size - 1) mod length cycle)"
      using last_idx arc2_gen \<open>arc_size > 0\<close>
      unfolding generate_n_arc_def
    by (metis (no_types, lifting) ext
        Nat.add_diff_assoc One_nat_def
        diff_diff_cancel diff_le_self
        diff_self_eq_0 len2
        length_rotate linorder_not_less
        minimal_arc_size nat.simps(3)
        nat_less_le nth_rotate nth_take
        order_less_le_trans
        take_all_iff)

    have last_wrap: "arc2_head_index + arc_size - 1 \<ge> length cycle"
      using wrap2 \<open>idx2 < arc_size\<close> by linarith
      
    have "arc2_head_index + arc_size - 1 < 2 * length cycle"
      using arc2_head_bound maximum_arc_size by linarith
    hence mod_last: "((arc2_head_index + arc_size - 1) mod length cycle) = arc2_head_index + arc_size - 1 - length cycle"
      using last_wrap by (simp add: mod_if)

    define shift where "shift = arc2_head_index + arc_size - 1 - length cycle - arc1_head_index"
    
    have "arc2_head_index + arc_size - 1 = arc2_head_index + idx2 + (arc_size - 1 - idx2)"
      using \<open>idx2 < arc_size\<close> by linarith
    hence "shift = (arc2_head_index + idx2 + (arc_size - 1 - idx2)) - length cycle - arc1_head_index"
      unfolding shift_def by simp
    also have "... = (arc2_head_index + idx2 - length cycle) + (arc_size - 1 - idx2) - arc1_head_index"
      using wrap2 by linarith
    also have "... = arc1_head_index + idx1 + (arc_size - 1 - idx2) - arc1_head_index"
      using match_idx by simp
    finally have "shift = idx1 + (arc_size - 1 - idx2)"
      by simp
    hence "shift < arc_size"
      using \<open>idx1 < arc_size\<close> \<open>idx2 < arc_size\<close> 
    using arc2_head_bound assms(5) last_wrap local.shift_def by linarith

    have "arc1_head_index + shift = arc2_head_index + arc_size - 1 - length cycle"
      using shift_def match_idx \<open>idx2 < arc_size\<close> by linarith
    hence "(arc1_head_index + shift) mod length cycle = (arc2_head_index + arc_size - 1) mod length cycle"
      using mod_last 
    by (metis
        mod_mod_trivial)
    hence "last arc2 = cycle ! ((arc1_head_index + shift) mod length cycle)"
      using last_val by simp

    thus "last arc2 \<in> set arc1"
      using elements_of_arc[OF assms(1) refl assms(3)] \<open>shift < arc_size\<close> by auto
  qed
  then show ?thesis by simp
qed

(* * PHASE 1: If all arcs in our set share a specific element, 
 * the total number of distinct arcs cannot exceed arc_size.
 *)
lemma bound_arcs_sharing_element:
  fixes shared_element :: "'a"
  assumes "shared_element \<in> set cycle"
  assumes "\<forall>arc \<in> set arcs. shared_element \<in> set arc"
  shows "length arcs \<le> arc_size"
proof -
  (* Map each arc to the index of the shared element within that arc *)
  define f where "f = (\<lambda>arc. index_of_element shared_element arc)"
 have "inj_on f (set arcs)"
  proof (rule inj_onI)
    fix arc1 arc2
    assume a1: "arc1 \<in> set arcs" and a2: "arc2 \<in> set arcs"
    assume eq: "f arc1 = f arc2"
    
    have h1: "index_of_element shared_element cycle = 
              (index_of_element (hd arc1) cycle + f arc1) mod (length cycle)"
      using a1 assms(2) arc_element_index_to_cycle_index f_def by fastforce
      
    have h2: "index_of_element shared_element cycle = 
              (index_of_element (hd arc2) cycle + f arc2) mod (length cycle)"
      using a2 assms(2) arc_element_index_to_cycle_index f_def by fastforce
      
    have eq_mod: "(index_of_element (hd arc1) cycle + f arc1) mod (length cycle) = 
                  (index_of_element (hd arc2) cycle + f arc1) mod (length cycle)"
      using h1 h2 eq by presburger
      
    (* Explicitly prove the head elements exist in the arcs so we can bound their indices *)
    have bound1: "index_of_element (hd arc1) cycle < length cycle"
      using a1 arc_size index_of_arc_elements_exist length_greater_0_conv list.set_sel(1)
    by (metis fixed_arc_size
        n_arc_of_cycle_def)
      
    have bound2: "index_of_element (hd arc2) cycle < length cycle"
      using a2 arc_size  index_of_arc_elements_exist length_greater_0_conv list.set_sel(1)
    by (metis intersecting_arcs
        intersecting_n_arcs_def)
      

(* Step 1: Cancel the common '+ f arc1' inside the modulo *)
    have "index_of_element (hd arc1) cycle mod length cycle = 
          index_of_element (hd arc2) cycle mod length cycle"
    proof -
      (* First, strictly bound the shift f arc1 *)
      have "shared_element \<in> set arc1" using a1 assms(2) by blast
      moreover have "length arc1 = arc_size" 
        using a1 intersecting_arcs intersecting_n_arcs_def by auto
      ultimately have "f arc1 < arc_size" unfolding f_def 
        by (metis index_limit nat_less_le not_contains_impl_not_elem not_in_list)
      then have f_bound: "f arc1 < length cycle" 
        using maximum_arc_size by linarith

      (* Define variables to force Isabelle to use simple linear arithmetic *)
      define A where "A = index_of_element (hd arc1) cycle"
      define B where "B = index_of_element (hd arc2) cycle"
      define C where "C = f arc1"
      define N where "N = length cycle"
      
      have "A < N" and "B < N" and "C < N" 
        using bound1 bound2 f_bound A_def B_def C_def
      using N_def by fastforce+
        
      have "(A + C) mod N = (B + C) mod N" 
        using eq_mod A_def B_def C_def N_def by simp
        
      (* Use mod_if to unroll the modulo into two pure algebraic possibilities *)
      have "A + C < 2 * N" using \<open>A < N\<close> \<open>C < N\<close> by linarith
      then have A_cases: "(A + C) mod N = A + C \<or> (A + C) mod N = A + C - N"
      by (metis add_less_cancel_right
          le_add_diff_inverse2 le_mod_geq
          linorder_not_less mod_less mult_2)
        
      have "B + C < 2 * N" using \<open>B < N\<close> \<open>C < N\<close> by linarith
      then have B_cases: "(B + C) mod N = B + C \<or> (B + C) mod N = B + C - N"
      using mod_if by auto

      (* linarith easily crushes the remaining pure linear algebra *)
      have "A = B"
        using A_cases B_cases \<open>(A + C) mod N = (B + C) mod N\<close> \<open>A < N\<close> \<open>B < N\<close>
      by (smt (z3) add_diff_cancel_left'
          add_right_cancel diff_commute diff_diff_cancel
          diff_is_0_eq' linorder_not_less mod_less
          nat_less_le)
        
      then show ?thesis 
        unfolding A_def B_def by simp
    qed
      
    (* Step 2: Because both values are strictly less than 'length cycle', 
       we can safely drop the modulo entirely *)
    then have "index_of_element (hd arc1) cycle = index_of_element (hd arc2) cycle"
      using bound1 bound2 by simp
      
    then show "arc1 = arc2"
      using a1 a2 arc_heads_define_n_arcs cycle_elements_distinct
    by (metis arc_generator_head)
  qed
  
  moreover have "f ` (set arcs) \<subseteq> {0..<arc_size}"
  proof
    fix x
    assume "x \<in> f ` (set arcs)"
    then obtain arc where "arc \<in> set arcs" and "x = f arc" by blast
    then have "x = index_of_element shared_element arc" using f_def by simp
    moreover have "length arc = arc_size" 
      using \<open>arc \<in> set arcs\<close> intersecting_arcs intersecting_n_arcs_def by auto
    ultimately show "x \<in> {0..<arc_size}"
      using \<open>arc \<in> set arcs\<close> assms(2) index_limit
    by (metis atLeast0LessThan le_antisym lessThan_iff
        linorder_not_le not_contains_impl_not_elem
        not_in_list)
  qed
  
  ultimately have "card (set arcs) \<le> card {0..<arc_size}"
    by (meson card_inj_on_le finite_atLeastLessThan)
    
  then show ?thesis
    using distinct_arcs distinct_card by fastforce
qed


(* * PHASE 2: Helly's Property for Circular Arcs.
 * Because 2 * arc_size <= length cycle and the arcs mutually intersect, 
 * there MUST be at least one global shared element among all of them.
 *)
lemma common_intersection_element:
  assumes "arcs \<noteq> []"
  shows "\<exists>shared_element \<in> set cycle. \<forall>arc \<in> set arcs. shared_element \<in> set arc"
  sorry


(* * FINAL THEOREM: Tying it together.
 *)
theorem intersecting_n_arcs_upper_limit_: 
  shows "length arcs \<le> arc_size"
proof (cases "arcs = []")
  case True
  then show ?thesis using minimal_arc_size by simp
next
  case False
  then obtain shared_element where "shared_element \<in> set cycle" 
    and "\<forall>arc \<in> set arcs. shared_element \<in> set arc"
    using common_intersection_element sorry
    
  then show ?thesis 
    using bound_arcs_sharing_element by blast
qed


lemma neighbors:
  fixes element :: "'a"
  fixes element_index :: "nat"
  fixes element_arc :: "'a list"
  fixes other_arc :: "'a list"
  fixes left_neighbor_indices :: "nat set"
  fixes left_neighbors :: "'a list set"
  fixes left_neighbor_arc :: "'a list"
  fixes right_neighbor_indices :: "nat set"
  fixes right_neighbors :: "'a list set"
  fixes right_neighbor_arc :: "'a list"
  assumes "element \<in> set cycle"
  assumes "element_index = index_of_element element cycle"
  assumes "element_arc = generate_n_arc cycle element_index arc_size"
  assumes "right_neighbor_indices = {(element_index + shift) mod (length cycle) | shift. 0 < shift \<and> shift < arc_size}"
  assumes "right_neighbors = {generate_n_arc cycle index arc_size | index. index \<in> right_neighbor_indices}"
  assumes "right_neighbor_arc \<in> right_neighbors"
  assumes "left_neigbor_indices = {index :: nat. (\<exists>shift. 0 < shift \<and> shift < arc_size \<and> cycle ! ((index + shift) mod (length cycle)) \<in> set element_arc)}"
  assumes "left_neighbors = {generate_n_arc cycle index arc_size | index. index \<in> left_neighbor_indices}"
  assumes "left_neighbor_arc \<in> left_neighbors"
  assumes "element_arc \<noteq> other_arc"
  shows "card right_neighbor_indices = arc_size - 1" 
      and "card right_neighbor_indices = card right_neighbors"
      and "hd right_neighbor_arc \<in> set element_arc"
      and "card left_neighbor_indices = arc_size - 1"
      and "card left_neighbor_indices = card left_neighbors"
      and "last left_neighbor_arc \<in> set element_arc"
      and "left_neighbors \<inter> right_neighbors = {}"
      and "right_neighbor_indices = {(index + arc_size) mod (length cycle) | index. index \<in> left_neighbor_indices}"
      and "intersecting_lists element_arc other_arc \<longleftrightarrow> (other_arc \<in> left_neighbors \<or> other_arc \<in> right_neighbors)" sorry



theorem intersecting_n_arcs_upper_limit: "length arcs \<le> arc_size"
proof cases
  assume "length arcs = 0"
  then show ?thesis by simp
next
  assume "\<not>(length arcs = 0)"
  then have "length arcs \<noteq> 0" by simp
  then have "length arcs > 0" by simp
  fix arc
  assume "arc \<in> set arcs"
  define arc_index where "arc_index = index_of_element (hd arc) cycle"
  define right_neighbor_indices where "right_neighbor_indices  = {(arc_index + shift) mod (length cycle) | shift. 0 < shift \<and> shift < arc_size}"
  define right_neighbors where "right_neighbors = {generate_n_arc cycle index arc_size | index. index \<in> right_neighbor_indices}"
  define left_neighbor_indices where "left_neighbor_indices = {index :: nat. (\<exists>shift. 0 < shift \<and> shift < arc_size \<and> cycle ! ((index + shift) mod (length cycle)) \<in> set arc)}"
  define left_neighbors where "left_neighbors = {generate_n_arc cycle index arc_size | index. index \<in> left_neighbor_indices}"
  have "\<forall>some_arc \<in> set arcs. some_arc \<noteq> arc \<longrightarrow> some_arc \<in> left_neighbors \<or> some_arc \<in> right_neighbors" using neighbors sorry 
qed


theorem maximal_intersecting_n_arcs: "\<exists>arcs :: 'a list list. intersecting_n_arcs arcs cycle arc_size \<and> distinct arcs \<and> length arcs = arc_size" sorry
end

end
