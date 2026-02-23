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
  assumes "left_neighbor_indices = {index :: nat. index < length cycle \<and> (\<exists>shift. 0 < shift \<and> shift < arc_size \<and> cycle ! ((index + shift) mod (length cycle)) = hd element_arc)}"  
  assumes "left_neighbors = {generate_n_arc cycle index arc_size | index. index \<in> left_neighbor_indices}"
  assumes "left_neighbor_arc \<in> left_neighbors"
  assumes "other_arc \<in> set arcs"
  assumes "element_arc \<noteq> other_arc"
  shows "card right_neighbor_indices = arc_size - 1" 
      and "card right_neighbor_indices = card right_neighbors"
      and "hd right_neighbor_arc \<in> set element_arc"
      and "card left_neighbor_indices = arc_size - 1"
      and "card left_neighbor_indices = card left_neighbors"
      and "last left_neighbor_arc \<in> set element_arc"
      and "element_arc \<notin> left_neighbors \<and> element_arc \<notin> right_neighbors"
      and "left_neighbors \<inter> right_neighbors = {}"
      and "right_neighbor_indices = {(index + arc_size) mod (length cycle) | index. index \<in> left_neighbor_indices}"
      and "intersecting_lists element_arc other_arc \<longleftrightarrow> (other_arc \<in> left_neighbors \<or> other_arc \<in> right_neighbors)"
proof -
  show "card right_neighbor_indices = card right_neighbors"
  proof -
    (* Define the generator function for brevity *)
    define gen where "gen = (\<lambda>index. generate_n_arc cycle index arc_size)"
    
    (* 1. Express right_neighbors as the image of right_neighbor_indices under gen *)
    have "right_neighbors = gen ` right_neighbor_indices"
      using assms(5) unfolding gen_def by blast
      
    (* 2. Establish that the cycle length is strictly positive so modulo arithmetic holds *)
    have cycle_pos: "length cycle > 0" 
      using cycle_size by auto
      
    (* 3. Prove that the generator function is injective on our specific set of indices *)
    have "inj_on gen right_neighbor_indices"
    proof (rule inj_onI)
      fix x y
      assume x_in: "x \<in> right_neighbor_indices"
      assume y_in: "y \<in> right_neighbor_indices"
      assume eq: "gen x = gen y"
      
      (* Any index in our set is strictly bounded by the cycle length due to the modulo operation *)
      have "x < length cycle"
        using x_in assms(4) cycle_pos by auto
        
      have "y < length cycle"
        using y_in assms(4) cycle_pos by auto
        
      (* Apply your pre-proven lemma to show that equal arcs with bounded indices implies equal indices *)
      show "x = y"
        using eq \<open>x < length cycle\<close> \<open>y < length cycle\<close> unique_index_unique_arc
        unfolding gen_def by blast
    qed
    
    (* 4. Conclude the cardinality equality using Isabelle's card_image theorem *)
    then show ?thesis
      using \<open>right_neighbors = gen ` right_neighbor_indices\<close> card_image by fastforce
  qed

  show "hd right_neighbor_arc \<in> set element_arc"
  proof -
    (* 1. Unpack the definitions to get the specific shift index *)
    from assms(6) obtain r_idx where "r_idx \<in> right_neighbor_indices" 
      and r_arc_def: "right_neighbor_arc = generate_n_arc cycle r_idx arc_size"
      using assms(5) by blast
      
    from \<open>r_idx \<in> right_neighbor_indices\<close> obtain shift where shift_bounds: "0 < shift" "shift < arc_size" 
      and r_idx_def: "r_idx = (element_index + shift) mod (length cycle)"
      using assms(4) by blast

    (* 2. Establish length bounds to satisfy taking elements via list indices *)
    have "length cycle > 0" using cycle_size by auto
    have "arc_size \<le> length cycle" using maximum_arc_size minimal_arc_size by linarith
    have "arc_size > 0" using minimal_arc_size by auto
    
    have len_el_arc: "length element_arc = arc_size"
      unfolding assms(3) generate_n_arc_def
      using \<open>arc_size \<le> length cycle\<close> by simp
      
    have len_r_arc: "length right_neighbor_arc = arc_size"
      unfolding r_arc_def generate_n_arc_def
      using \<open>arc_size \<le> length cycle\<close> by simp

    (* 3. Find the exact element at the head of the right neighbor arc *)
    have "hd right_neighbor_arc = right_neighbor_arc ! 0"
      using len_r_arc \<open>arc_size > 0\<close> hd_conv_nth by force
    also have "... = (take arc_size (rotate r_idx cycle)) ! 0"
      unfolding r_arc_def generate_n_arc_def by simp
    also have "... = rotate r_idx cycle ! 0"
      using \<open>arc_size > 0\<close> by simp
    also have "... = cycle ! (r_idx mod length cycle)"
      using nth_rotate 
    using \<open>0 < length cycle\<close> by fastforce
    also have "... = cycle ! r_idx"
      using r_idx_def by simp
    finally have head_val: "hd right_neighbor_arc = cycle ! r_idx" .

    (* 4. Show that this exact element exists in element_arc at index `shift` *)
    have "element_arc ! shift = (take arc_size (rotate element_index cycle)) ! shift"
      unfolding assms(3) generate_n_arc_def by simp
    also have "... = rotate element_index cycle ! shift"
      using shift_bounds by simp
    also have "... = cycle ! ((element_index + shift) mod length cycle)"
      using nth_rotate 
    using \<open>arc_size \<le> length cycle\<close>
      order_less_le_trans shift_bounds(2)
    by blast
    also have "... = cycle ! r_idx"
      using r_idx_def by simp
    finally have "element_arc ! shift = cycle ! r_idx" .
    
    (* 5. Conclude the proof: since shift < length of element_arc, it is in the set *)
    hence "hd right_neighbor_arc = element_arc ! shift"
      using head_val by simp
    moreover have "shift < length element_arc"
      using shift_bounds len_el_arc by simp
    ultimately show ?thesis
      using nth_mem by simp
  qed

  show "card left_neighbor_indices = arc_size - 1"
  proof -
    (* 1. Basic bounds and identifying the head element *)
    have cycle_pos: "length cycle > 0" using cycle_size by auto
    have arc_size_pos: "arc_size > 0" using minimal_arc_size by simp
    
    have element_idx_bound: "element_index < length cycle"
      using assms(1,2) index_limit
    by (metis not_contains_impl_not_elem
        not_in_list order_neq_le_trans)
      
    have hd_elem: "hd element_arc = cycle ! element_index"
      unfolding assms(3) generate_n_arc_def
      using arc_size_pos cycle_pos element_idx_bound
      hd_rotate_conv_nth hd_take list.size(3)
    by (metis less_nat_zero_code mod_less)

    (* 2. Define our shift domain and our mapping function *)
    define shift_set where "shift_set = {1..<arc_size}"
    define f where "f = (\<lambda>s. (element_index + length cycle - s) mod (length cycle))"
    
    (* 3. Prove that left_neighbor_indices is EXACTLY the image of shift_set under f *)
    have "left_neighbor_indices = f ` shift_set"
    proof (rule set_eqI, rule iffI)
      (* Forward direction: If it's a left neighbor, it comes from our shift mapping *)
      fix x
      assume "x \<in> left_neighbor_indices"
      
      (* 1. Unfold the set and keep it as a single boolean statement *)
      have "x < length cycle \<and> (\<exists>shift. 0 < shift \<and> shift < arc_size \<and> cycle ! ((x + shift) mod length cycle) = hd element_arc)"
        using \<open>x \<in> left_neighbor_indices\<close> unfolding assms(7) by blast
        
      (* 2. Extract the facts and the existential variable all at once *)
      then obtain shift where "x < length cycle"
        and "0 < shift"
        and "shift < arc_size"
        and "cycle ! ((x + shift) mod length cycle) = hd element_arc"
        by blast
      have "cycle ! ((x + shift) mod length cycle) = cycle ! element_index"
        using \<open>cycle ! ((x + shift) mod length cycle) = hd element_arc\<close> hd_elem by simp
        
      have "(x + shift) mod length cycle = element_index"
        using \<open>cycle ! ((x + shift) mod length cycle) = cycle ! element_index\<close> 
              cycle_elements_distinct element_idx_bound cycle_pos
        by (metis mod_less_divisor nth_eq_iff_index_eq)
              
      have "x = f shift"
      proof -
        (* 1. Establish the maximum possible bound for x + shift *)
        have "shift < length cycle" 
          using \<open>shift < arc_size\<close> maximum_arc_size minimal_arc_size by linarith
        hence "x + shift < 2 * length cycle" 
          using \<open>x < length cycle\<close> by linarith
          
        (* 2. Split into the two exact ways the modulo operator can behave *)
        then consider (no_wrap) "x + shift < length cycle" | (wrap) "x + shift \<ge> length cycle" 
          by linarith
        then show ?thesis
        proof cases
          case no_wrap
          (* If it doesn't wrap, mod does nothing *)
          hence "(x + shift) mod length cycle = x + shift" by simp
          hence "x + shift = element_index" 
            using \<open>(x + shift) mod length cycle = element_index\<close> by simp
            
          (* Substitute this back into the definition of f *)
          have "f shift = (element_index + length cycle - shift) mod length cycle"
            unfolding f_def by simp
          also have "... = (x + shift + length cycle - shift) mod length cycle"
            using \<open>x + shift = element_index\<close> by simp
          also have "... = (x + length cycle) mod length cycle"
            by simp
          also have "... = x mod length cycle"
            by simp (* Isabelle inherently knows (A + L) mod L = A mod L *)
          also have "... = x"
            using \<open>x < length cycle\<close> by simp
          finally show ?thesis by simp
          
        next
          case wrap
          (* If it wraps, mod subtracts exactly one length cycle *)
          hence "(x + shift) mod length cycle = x + shift - length cycle" 
            using \<open>x + shift < 2 * length cycle\<close> by (simp add: mod_if)
          hence "x + shift - length cycle = element_index" 
            using \<open>(x + shift) mod length cycle = element_index\<close> by simp
            
          (* Rearrange this to solve for x using linear arithmetic *)
          hence x_eq: "x = element_index + length cycle - shift" 
            using wrap by linarith
            
          (* Show this perfectly matches f shift *)
          have "f shift = (element_index + length cycle - shift) mod length cycle"
            unfolding f_def by simp
          also have "... = x mod length cycle"
            using x_eq by simp
          also have "... = x"
            using \<open>x < length cycle\<close> by simp
          finally show ?thesis by simp
        qed
      qed
        
      show "x \<in> f ` shift_set"
        unfolding shift_set_def
        using \<open>x = f shift\<close> \<open>0 < shift\<close> \<open>shift < arc_size\<close> by auto
        
    next
      (* Reverse direction: If it comes from our shift mapping, it's a left neighbor *)
      fix x
      assume "x \<in> f ` shift_set"
      then obtain shift where "shift \<in> shift_set" and "x = f shift" by blast
      hence "0 < shift" and "shift < arc_size" unfolding shift_set_def by auto
      
      have "x < length cycle" unfolding f_def using \<open>x = f shift\<close> cycle_pos
      using f_def mod_less_divisor
      by presburger
      
      have "(x + shift) mod length cycle = element_index"
        unfolding f_def using \<open>x = f shift\<close> \<open>shift < arc_size\<close> element_idx_bound
        using Nat.add_diff_assoc add.commute add_diff_inverse_nat mod_add_right_eq mod_less
      by (smt (verit) f_def less_eqE maximum_arc_size
          mod_add_self2 mult_2 nat_less_le
          trans_less_add1)
        
      hence "cycle ! ((x + shift) mod length cycle) = hd element_arc"
        using hd_elem by simp
        
      show "x \<in> left_neighbor_indices"
        unfolding assms(7)
        using \<open>x < length cycle\<close> \<open>0 < shift\<close> \<open>shift < arc_size\<close> \<open>cycle ! ((x + shift) mod length cycle) = hd element_arc\<close>
        by blast
    qed
    
(* 4. Prove that the mapping is injective (distinct shifts give distinct indices) *)
    moreover have "inj_on f shift_set"
    proof (rule inj_onI)
      fix x y
      assume "x \<in> shift_set" and "y \<in> shift_set"
      assume eq: "f x = f y"

      (* Extract the basic bounds for our shifts *)
      have "x < arc_size" and "y < arc_size"
        using \<open>x \<in> shift_set\<close> \<open>y \<in> shift_set\<close> unfolding shift_set_def by auto
      have "arc_size \<le> length cycle" 
        using maximum_arc_size minimal_arc_size by linarith
      hence "x < length cycle" and "y < length cycle" 
        using \<open>x < arc_size\<close> \<open>y < arc_size\<close> by linarith+

      (* Define the inner algebra before the modulo operation *)
      define A where "A = element_index + length cycle - x"
      define B where "B = element_index + length cycle - y"

      have eq_mod: "A mod length cycle = B mod length cycle"
        using eq unfolding f_def A_def B_def by simp

      (* Do a strict linear order case analysis to avoid SMT solvers *)
      show "x = y"
      proof (rule linorder_cases[of x y])
        assume "x = y"
        thus ?thesis .
      next
        (* CASE 1: x is strictly less than y *)
        assume "x < y"
        have "y - x > 0" and "y - x < length cycle" 
          using \<open>x < y\<close> \<open>y < length cycle\<close> by linarith+
        have "A = B + (y - x)" 
          unfolding A_def B_def using \<open>x < y\<close> \<open>y < length cycle\<close> by linarith

        (* Expand the modulo equality *)
        have "B mod length cycle = A mod length cycle" using eq_mod by simp
        also have "... = (B + (y - x)) mod length cycle" using \<open>A = B + (y - x)\<close> by simp
        also have "... = (B mod length cycle + (y - x) mod length cycle) mod length cycle"
          by (simp add: mod_add_eq)
        also have "... = (B mod length cycle + (y - x)) mod length cycle"
          using \<open>y - x < length cycle\<close> by simp
        finally have "B mod length cycle = (B mod length cycle + (y - x)) mod length cycle" .

        (* Reduce to a simple m = (m + d) mod L problem *)
        define m where "m = B mod length cycle"
        define d where "d = y - x"

        have "m = (m + d) mod length cycle"
          using \<open>B mod length cycle = (B mod length cycle + (y - x)) mod length cycle\<close>
          unfolding m_def d_def by simp

        have "m < length cycle" unfolding m_def using cycle_size 
        using cycle_pos by auto
        have "d > 0" and "d < length cycle" 
          unfolding d_def using \<open>y - x > 0\<close> \<open>y - x < length cycle\<close> by auto

        (* Split into the two absolute ways modulo arithmetic can wrap around *)
        have "m + d < 2 * length cycle" using \<open>m < length cycle\<close> \<open>d < length cycle\<close> by linarith
        then consider (no_wrap) "m + d < length cycle" | (wrap) "m + d \<ge> length cycle" by linarith
        then show ?thesis
        proof cases
          case no_wrap
          hence "(m + d) mod length cycle = m + d" by simp
          hence "m = m + d" using \<open>m = (m + d) mod length cycle\<close> by simp
          thus ?thesis using \<open>d > 0\<close> by simp (* Contradiction *)
        next
          case wrap
          hence "(m + d) mod length cycle = m + d - length cycle"
            using \<open>m + d < 2 * length cycle\<close> by (simp add: mod_if)
          hence "m = m + d - length cycle" using \<open>m = (m + d) mod length cycle\<close> by simp
          thus ?thesis using \<open>d < length cycle\<close> 
          using wrap by auto (* Contradiction *)
        qed

      next
        (* CASE 2: y is strictly less than x (Symmetric to Case 1) *)
        assume "y < x"
        have "x - y > 0" and "x - y < length cycle" 
          using \<open>y < x\<close> \<open>x < length cycle\<close> by linarith+
        have "B = A + (x - y)" 
          unfolding A_def B_def using \<open>y < x\<close> \<open>x < length cycle\<close> by linarith

        have "A mod length cycle = B mod length cycle" using eq_mod by simp
        also have "... = (A + (x - y)) mod length cycle" using \<open>B = A + (x - y)\<close> by simp
        also have "... = (A mod length cycle + (x - y) mod length cycle) mod length cycle"
          by (simp add: mod_add_eq)
        also have "... = (A mod length cycle + (x - y)) mod length cycle"
          using \<open>x - y < length cycle\<close> by simp
        finally have "A mod length cycle = (A mod length cycle + (x - y)) mod length cycle" .

        define m where "m = A mod length cycle"
        define d where "d = x - y"

        have "m = (m + d) mod length cycle"
          using \<open>A mod length cycle = (A mod length cycle + (x - y)) mod length cycle\<close>
          unfolding m_def d_def by simp

        have "m < length cycle" unfolding m_def using cycle_size
        using cycle_pos by auto
        have "d > 0" and "d < length cycle" 
          unfolding d_def using \<open>x - y > 0\<close> \<open>x - y < length cycle\<close> by auto

        have "m + d < 2 * length cycle" using \<open>m < length cycle\<close> \<open>d < length cycle\<close> by linarith
        then consider (no_wrap) "m + d < length cycle" | (wrap) "m + d \<ge> length cycle" by linarith
        then show ?thesis
        proof cases
          case no_wrap
          hence "(m + d) mod length cycle = m + d" by simp
          hence "m = m + d" using \<open>m = (m + d) mod length cycle\<close> by simp
          thus ?thesis using \<open>d > 0\<close> by simp
        next
          case wrap
          hence "(m + d) mod length cycle = m + d - length cycle"
            using \<open>m + d < 2 * length cycle\<close> by (simp add: mod_if)
          hence "m = m + d - length cycle" using \<open>m = (m + d) mod length cycle\<close> by simp
          thus ?thesis using \<open>d < length cycle\<close>
          using wrap by linarith
        qed
      qed
    qed
      
    (* 5. Conclude the cardinality *)
    ultimately show ?thesis
      using card_image shift_set_def by force
  qed

  show "card right_neighbor_indices = arc_size - 1"
  proof -
    (* 1. Setup bounds *)
    have cycle_pos: "length cycle > 0" using cycle_size by force
    have arc_size_pos: "arc_size > 0" using minimal_arc_size by simp

    (* 2. Define our shift domain and our mapping function *)
    define shift_set where "shift_set = {1..<arc_size}"
    define f where "f = (\<lambda>s. (element_index + s) mod length cycle)"

    (* 3. Prove that right_neighbor_indices is EXACTLY the image of shift_set under f *)
    have "right_neighbor_indices = f ` shift_set"
    proof (rule set_eqI, rule iffI)
      (* Forward direction: If it's a right neighbor, it comes from our shift mapping *)
      fix x
      assume "x \<in> right_neighbor_indices"
      (* Unpack the standard Isabelle syntax for {f(x) | x. P(x)} *)
      hence "x \<in> {(element_index + shift) mod length cycle | shift. 0 < shift \<and> shift < arc_size}"
        using assms(4) by simp
      then obtain shift where "0 < shift" and "shift < arc_size" 
        and "x = (element_index + shift) mod length cycle"
        by blast
        
      show "x \<in> f ` shift_set"
        unfolding f_def shift_set_def
        using \<open>x = (element_index + shift) mod length cycle\<close> \<open>0 < shift\<close> \<open>shift < arc_size\<close> 
        by auto
    next
      (* Reverse direction: If it comes from our shift mapping, it's a right neighbor *)
      fix x
      assume "x \<in> f ` shift_set"
      then obtain shift where "shift \<in> shift_set" and "x = f shift" by blast
      hence "0 < shift" and "shift < arc_size" unfolding shift_set_def by auto
      
      show "x \<in> right_neighbor_indices"
        unfolding assms(4) f_def
        using \<open>x = f shift\<close> \<open>0 < shift\<close> \<open>shift < arc_size\<close> 
      using f_def by blast
    qed

    (* 4. Prove that the mapping is injective using bulletproof linear arithmetic *)
    moreover have "inj_on f shift_set"
    proof (rule inj_onI)
      fix x y
      assume "x \<in> shift_set" and "y \<in> shift_set"
      assume eq: "f x = f y"

      (* Extract bounds *)
      have "x < arc_size" and "y < arc_size"
        using \<open>x \<in> shift_set\<close> \<open>y \<in> shift_set\<close> unfolding shift_set_def by auto
      have "arc_size \<le> length cycle" 
        using maximum_arc_size minimal_arc_size by linarith
      hence "x < length cycle" and "y < length cycle" 
        using \<open>x < arc_size\<close> \<open>y < arc_size\<close> by linarith+

      (* Define the inner algebra before modulo *)
      define A where "A = element_index + x"
      define B where "B = element_index + y"

      have eq_mod: "A mod length cycle = B mod length cycle"
        using eq unfolding f_def A_def B_def by simp

      (* Do a strict linear order case analysis to avoid SMT solvers *)
      show "x = y"
      proof (rule linorder_cases[of x y])
        assume "x = y"
        thus ?thesis .
      next
        (* CASE 1: x is strictly less than y *)
        assume "x < y"
        have "y - x > 0" and "y - x < length cycle" 
          using \<open>x < y\<close> \<open>y < length cycle\<close> by linarith+
        have "B = A + (y - x)" 
          unfolding A_def B_def using \<open>x < y\<close> by linarith

        have "A mod length cycle = B mod length cycle" using eq_mod by simp
        also have "... = (A + (y - x)) mod length cycle" using \<open>B = A + (y - x)\<close> by simp
        also have "... = (A mod length cycle + (y - x) mod length cycle) mod length cycle"
          by (simp add: mod_add_eq)
        also have "... = (A mod length cycle + (y - x)) mod length cycle"
          using \<open>y - x < length cycle\<close> by simp
        finally have "A mod length cycle = (A mod length cycle + (y - x)) mod length cycle" .

        define m where "m = A mod length cycle"
        define d where "d = y - x"

        have "m = (m + d) mod length cycle"
          using \<open>A mod length cycle = (A mod length cycle + (y - x)) mod length cycle\<close>
          unfolding m_def d_def by simp

        have "m < length cycle" unfolding m_def using cycle_size 
        using cycle_pos by auto
        have "d > 0" and "d < length cycle" 
          unfolding d_def using \<open>y - x > 0\<close> \<open>y - x < length cycle\<close> by auto

        have "m + d < 2 * length cycle" using \<open>m < length cycle\<close> \<open>d < length cycle\<close> by linarith
        then consider (no_wrap) "m + d < length cycle" | (wrap) "m + d \<ge> length cycle" by linarith
        then show ?thesis
        proof cases
          case no_wrap
          hence "(m + d) mod length cycle = m + d" by simp
          hence "m = m + d" using \<open>m = (m + d) mod length cycle\<close> by simp
          thus ?thesis using \<open>d > 0\<close> by simp
        next
          case wrap
          hence "(m + d) mod length cycle = m + d - length cycle"
            using \<open>m + d < 2 * length cycle\<close> by (simp add: mod_if)
          hence "m = m + d - length cycle" using \<open>m = (m + d) mod length cycle\<close> by simp
          thus ?thesis using \<open>d < length cycle\<close> 
          using wrap by linarith
        qed
      next
        (* CASE 2: y is strictly less than x (Symmetric to Case 1) *)
        assume "y < x"
        have "x - y > 0" and "x - y < length cycle" 
          using \<open>y < x\<close> \<open>x < length cycle\<close> by linarith+
        have "A = B + (x - y)" 
          unfolding A_def B_def using \<open>y < x\<close> by linarith

        have "B mod length cycle = A mod length cycle" using eq_mod by simp
        also have "... = (B + (x - y)) mod length cycle" using \<open>A = B + (x - y)\<close> by simp
        also have "... = (B mod length cycle + (x - y) mod length cycle) mod length cycle"
          by (simp add: mod_add_eq)
        also have "... = (B mod length cycle + (x - y)) mod length cycle"
          using \<open>x - y < length cycle\<close> by simp
        finally have "B mod length cycle = (B mod length cycle + (x - y)) mod length cycle" .

        define m where "m = B mod length cycle"
        define d where "d = x - y"

        have "m = (m + d) mod length cycle"
          using \<open>B mod length cycle = (B mod length cycle + (x - y)) mod length cycle\<close>
          unfolding m_def d_def by simp

        have "m < length cycle" unfolding m_def using cycle_size 
        using cycle_pos by auto
        have "d > 0" and "d < length cycle" 
          unfolding d_def using \<open>x - y > 0\<close> \<open>x - y < length cycle\<close> by auto

        have "m + d < 2 * length cycle" using \<open>m < length cycle\<close> \<open>d < length cycle\<close> by linarith
        then consider (no_wrap) "m + d < length cycle" | (wrap) "m + d \<ge> length cycle" by linarith
        then show ?thesis
        proof cases
          case no_wrap
          hence "(m + d) mod length cycle = m + d" by simp
          hence "m = m + d" using \<open>m = (m + d) mod length cycle\<close> by simp
          thus ?thesis using \<open>d > 0\<close> by simp
        next
          case wrap
          hence "(m + d) mod length cycle = m + d - length cycle"
            using \<open>m + d < 2 * length cycle\<close> by (simp add: mod_if)
          hence "m = m + d - length cycle" using \<open>m = (m + d) mod length cycle\<close> by simp
          thus ?thesis using \<open>d < length cycle\<close>
          using wrap by auto
        qed
      qed
    qed

    (* 5. Conclude the cardinality equality using card_image *)
    ultimately have "card right_neighbor_indices = card shift_set"
      using card_image by blast
    also have "... = arc_size - 1"
      unfolding shift_set_def by auto
    finally show ?thesis .
  qed

  show "card left_neighbor_indices = card left_neighbors"
  proof -
    (* Define the generator function for brevity *)
    define gen where "gen = (\<lambda>index. generate_n_arc cycle index arc_size)"
    
    (* 1. Express left_neighbors as the image of left_neighbor_indices under gen *)
    have "left_neighbors = gen ` left_neighbor_indices"
      using assms(8) unfolding gen_def by blast
      
    (* 2. Establish that the cycle length is positive *)
    have cycle_pos: "length cycle > 0" 
      using cycle_size by auto
      
    (* 3. Prove that the generator function is injective on our set of indices *)
    have "inj_on gen left_neighbor_indices"
    proof (rule inj_onI)
      fix x y
      assume x_in: "x \<in> left_neighbor_indices"
      assume y_in: "y \<in> left_neighbor_indices"
      assume eq: "gen x = gen y"
      
      (* Because we fixed the definition of left_neighbor_indices to include 
         index < length cycle, we can extract the bound instantly using auto *)
      have "x < length cycle"
        using x_in assms(7) by auto
        
      have "y < length cycle"
        using y_in assms(7) by auto
        
      (* Apply your pre-proven lemma to show that equal arcs with bounded indices implies equal indices *)
      show "x = y"
        using eq \<open>x < length cycle\<close> \<open>y < length cycle\<close> unique_index_unique_arc
        unfolding gen_def by blast
    qed
    
    (* 4. Conclude the cardinality equality using Isabelle's card_image theorem *)
    then show ?thesis
      using \<open>left_neighbors = gen ` left_neighbor_indices\<close> card_image by fastforce
  qed

  show "last left_neighbor_arc \<in> set element_arc"
  proof -
    (* 1. Unpack definitions to get the left neighbor's index and shift *)
    from assms(9) obtain l_idx where "l_idx \<in> left_neighbor_indices" 
      and l_arc_def: "left_neighbor_arc = generate_n_arc cycle l_idx arc_size"
      using assms(8) by blast
      
    from \<open>l_idx \<in> left_neighbor_indices\<close> obtain shift where "l_idx < length cycle"
      and shift_bounds: "0 < shift" "shift < arc_size" 
      and hd_match: "cycle ! ((l_idx + shift) mod length cycle) = hd element_arc"
      unfolding assms(7) by blast

    (* 2. Establish basic bounds *)
    have cycle_pos: "length cycle > 0" using cycle_size by auto
    have arc_size_pos: "arc_size > 0" using minimal_arc_size by simp
    have "arc_size \<le> length cycle" using maximum_arc_size minimal_arc_size by linarith
    
    have el_idx_bound: "element_index < length cycle"
      using assms(1,2) index_limit
    by (metis not_contains_impl_not_elem
        not_in_list order_le_neq_trans)

    have len_el_arc: "length element_arc = arc_size"
      unfolding assms(3) generate_n_arc_def
      using \<open>arc_size \<le> length cycle\<close> by simp
      
    have len_l_arc: "length left_neighbor_arc = arc_size"
      unfolding l_arc_def generate_n_arc_def
      using \<open>arc_size \<le> length cycle\<close> by simp

    (* 3. Map hd element_arc to its cyclic index and equate it *)
    have "hd element_arc = element_arc ! 0"
      using len_el_arc arc_size_pos hd_conv_nth by force
    also have "... = cycle ! (element_index mod length cycle)"
      unfolding assms(3) generate_n_arc_def using arc_size_pos nth_rotate
    by (metis add.comm_neutral cycle_pos
        nth_take)
    also have "... = cycle ! element_index"
      using el_idx_bound by simp
    finally have "hd element_arc = cycle ! element_index" .
    
    (* Because cycle elements are distinct, matching elements means matching indices *)
    have "(l_idx + shift) mod length cycle = element_index"
      using hd_match \<open>hd element_arc = cycle ! element_index\<close> 
            cycle_elements_distinct el_idx_bound cycle_pos
      by (metis mod_less_divisor nth_eq_iff_index_eq)

    (* 4. Define the target index inside element_arc *)
    define k where "k = arc_size - 1 - shift"
    have "k < arc_size" using shift_bounds
    using k_def by auto
    
    (* 5. Prove that the end of the left arc aligns with the k-th element of element_arc *)
    have "(element_index + k) mod length cycle = ((l_idx + shift) mod length cycle + k) mod length cycle"
      using \<open>(l_idx + shift) mod length cycle = element_index\<close> by simp
    also have "... = (l_idx + shift + k) mod length cycle"
      by (metis mod_add_left_eq) (* Standard Isabelle lemma for nested modulos! *)
    also have "... = (l_idx + arc_size - 1) mod length cycle"
      using shift_bounds k_def by auto
    finally have match_idx: "(element_index + k) mod length cycle = (l_idx + arc_size - 1) mod length cycle" .

    (* 6. Locate the last element of the left neighbor *)
    have "last left_neighbor_arc = left_neighbor_arc ! (arc_size - 1)"
      using len_l_arc arc_size_pos last_conv_nth by force
    also have "... = cycle ! ((l_idx + arc_size - 1) mod length cycle)"
      unfolding l_arc_def generate_n_arc_def 
      using \<open>arc_size > 0\<close> nth_rotate
    by (metis \<open>arc_size \<le> length cycle\<close> diff_less
        le_neq_implies_less less_imp_diff_less
        minimal_arc_size nth_take
        ordered_cancel_comm_monoid_diff_class.diff_add_assoc
        zero_less_one)
    also have "... = cycle ! ((element_index + k) mod length cycle)"
      using match_idx by simp
    
    (* 7. Locate the k-th element of element_arc *)
    also have "... = (take arc_size (rotate element_index cycle)) ! k"
      using \<open>k < arc_size\<close> nth_rotate
    by (metis \<open>arc_size \<le> length cycle\<close> nth_take
        order_less_le_trans)
    also have "... = element_arc ! k"
      unfolding assms(3) generate_n_arc_def by simp
    finally have "last left_neighbor_arc = element_arc ! k" .

    (* 8. Conclude it exists in the set *)
    moreover have "k < length element_arc"
      using \<open>k < arc_size\<close> len_el_arc by simp
    ultimately show ?thesis
      using nth_mem by auto
  qed

  show "element_arc \<notin> left_neighbors \<and>
    element_arc \<notin> right_neighbors"
  proof
    (* ======================================================================= *)
    (* PART 1: element_arc \<notin> right_neighbors                                   *)
    (* ======================================================================= *)
    show "element_arc \<notin> right_neighbors"
    proof
      assume "element_arc \<in> right_neighbors"
      
      (* 1. Unpack the offending right neighbor *)
      then obtain r_idx where "r_idx \<in> right_neighbor_indices" 
        and "element_arc = generate_n_arc cycle r_idx arc_size"
        unfolding assms(5) by blast
        
      from \<open>r_idx \<in> right_neighbor_indices\<close> obtain shift where "0 < shift" and "shift < arc_size"
        and r_idx_def: "r_idx = (element_index + shift) mod length cycle"
        unfolding assms(4) by blast
        
      (* 2. Establish basic bounds *)
      have el_bound: "element_index < length cycle"
        using assms(1,2) index_limit
      by (metis nat_less_le
          not_contains_impl_not_elem
          not_in_list)
      have r_bound: "r_idx < length cycle"
        using r_idx_def cycle_size 
      by (meson assms(1) length_pos_if_in_set
          mod_less_divisor)
        
      (* 3. Use unique_index_unique_arc to force the indices to be equal *)
      have "element_index = r_idx"
        using \<open>element_arc = generate_n_arc cycle r_idx arc_size\<close> assms(3)
              el_bound r_bound unique_index_unique_arc by metis
              
      (* 4. Prove the algebraic contradiction: E = (E + shift) mod L *)
      have "element_index = (element_index + shift) mod length cycle"
        using \<open>element_index = r_idx\<close> r_idx_def by simp
        
      have "shift < length cycle" 
        using \<open>shift < arc_size\<close> maximum_arc_size minimal_arc_size by linarith
      have "element_index + shift < 2 * length cycle" 
        using el_bound \<open>shift < length cycle\<close> by linarith
      
      (* 5. Case split the modulo to crush it natively *)
      consider (no_wrap) "element_index + shift < length cycle" | (wrap) "element_index + shift \<ge> length cycle" 
        by linarith
      then show False
      proof cases
        case no_wrap
        hence "(element_index + shift) mod length cycle = element_index + shift" by simp
        hence "element_index = element_index + shift" 
          using \<open>element_index = (element_index + shift) mod length cycle\<close> by simp
        thus False using \<open>0 < shift\<close> by simp
      next
        case wrap
        hence "(element_index + shift) mod length cycle = element_index + shift - length cycle" 
          using \<open>element_index + shift < 2 * length cycle\<close> by (simp add: mod_if)
        hence "element_index = element_index + shift - length cycle" 
          using \<open>element_index = (element_index + shift) mod length cycle\<close> by simp
        thus False using \<open>shift < length cycle\<close> 
        using wrap by linarith
      qed
    qed

  next
    (* ======================================================================= *)
    (* PART 2: element_arc \<notin> left_neighbors                                    *)
    (* ======================================================================= *)
    show "element_arc \<notin> left_neighbors"
    proof
      assume a: "element_arc \<in> left_neighbors"
      
      (* 1. Unpack the offending left neighbor *)
      then obtain l_idx where "l_idx \<in> left_neighbor_indices"
        and "element_arc = generate_n_arc cycle l_idx arc_size"
        unfolding assms(8) by blast
        
      from \<open>l_idx \<in> left_neighbor_indices\<close> obtain shift where "l_idx < length cycle"
        and "0 < shift" and "shift < arc_size"
        and hd_match: "cycle ! ((l_idx + shift) mod length cycle) = hd element_arc"
        unfolding assms(7) by blast
        
      (* 2. Establish basic bounds *)
      have cycle_pos: "length cycle > 0" using cycle_size by auto
      have el_bound: "element_index < length cycle"
        using assms(1,2) index_limit 
      by (metis le_antisym linorder_not_le
          not_contains_impl_not_elem
          not_in_list)
        
      (* 3. Use unique_index_unique_arc to force the indices to be equal *)
      have "element_index = l_idx"
        using \<open>element_arc = generate_n_arc cycle l_idx arc_size\<close> assms(3)
              el_bound \<open>l_idx < length cycle\<close> unique_index_unique_arc by metis
              
      (* 4. Map hd element_arc to its cyclic index *)
      have "hd element_arc = cycle ! element_index"
        unfolding assms(3) generate_n_arc_def
        using minimal_arc_size cycle_size el_bound
        hd_rotate_conv_nth hd_take list.size(3)
      by (metis add.commute add.right_neutral
          arc_size
          canonically_ordered_monoid_add_class.lessE
          cycle_pos mod_less)
        
      (* 5. Translate matching elements to matching indices *)
      have "(l_idx + shift) mod length cycle = element_index"
        using hd_match \<open>hd element_arc = cycle ! element_index\<close>
              cycle_elements_distinct el_bound cycle_pos
        by (metis mod_less_divisor nth_eq_iff_index_eq)
        
      hence "(element_index + shift) mod length cycle = element_index"
        using \<open>element_index = l_idx\<close> by simp
        
      (* 6. Prove the exact same algebraic contradiction as Part 1! *)
      have "shift < length cycle" 
        using \<open>shift < arc_size\<close> maximum_arc_size minimal_arc_size by linarith
      have "element_index + shift < 2 * length cycle" 
        using el_bound \<open>shift < length cycle\<close> by linarith
      
      consider (no_wrap) "element_index + shift < length cycle" | (wrap) "element_index + shift \<ge> length cycle" 
        by linarith
      then show False
      proof cases
        case no_wrap
        hence "(element_index + shift) mod length cycle = element_index + shift" by simp
        hence "element_index = element_index + shift" 
          using \<open>(element_index + shift) mod length cycle = element_index\<close> by simp
        thus False using \<open>0 < shift\<close> by simp
      next
        case wrap
        hence "(element_index + shift) mod length cycle = element_index + shift - length cycle" 
          using \<open>element_index + shift < 2 * length cycle\<close> by (simp add: mod_if)
        hence "element_index = element_index + shift - length cycle" 
          using \<open>(element_index + shift) mod length cycle = element_index\<close> by simp
        thus False using \<open>shift < length cycle\<close>
        using wrap by auto
      qed
    qed
  qed

  show "left_neighbors \<inter> right_neighbors = {}"
  proof (rule equals0I)
    fix x
    assume "x \<in> left_neighbors \<inter> right_neighbors"
    hence "x \<in> left_neighbors" and "x \<in> right_neighbors" by auto

    (* ======================================================================= *)
    (* 1. Unpack the offending right neighbor                                  *)
    (* ======================================================================= *)
    from \<open>x \<in> right_neighbors\<close> obtain r_idx where "r_idx \<in> right_neighbor_indices" 
      and x_r_def: "x = generate_n_arc cycle r_idx arc_size"
      unfolding assms(5) by blast

    from \<open>r_idx \<in> right_neighbor_indices\<close> obtain r_shift where "0 < r_shift" and "r_shift < arc_size"
      and r_idx_def: "r_idx = (element_index + r_shift) mod length cycle"
      unfolding assms(4) by blast

    (* ======================================================================= *)
    (* 2. Unpack the offending left neighbor                                   *)
    (* ======================================================================= *)
    from \<open>x \<in> left_neighbors\<close> obtain l_idx where "l_idx \<in> left_neighbor_indices"
      and x_l_def: "x = generate_n_arc cycle l_idx arc_size"
      unfolding assms(8) by blast

    from \<open>l_idx \<in> left_neighbor_indices\<close> obtain l_shift where "l_idx < length cycle"
      and "0 < l_shift" and "l_shift < arc_size"
      and hd_match: "cycle ! ((l_idx + l_shift) mod length cycle) = hd element_arc"
      unfolding assms(7) by auto

    (* ======================================================================= *)
    (* 3. Prove that l_idx and r_idx must be exactly the same index            *)
    (* ======================================================================= *)
    have cycle_pos: "length cycle > 0" using cycle_size by auto
    have el_idx_bound: "element_index < length cycle"
      using assms(1,2) index_limit
    by (metis nat_less_le
        not_contains_impl_not_elem
        not_in_list)
    have r_idx_bound: "r_idx < length cycle"
      using r_idx_def cycle_size
    using cycle_pos by fastforce

    have "generate_n_arc cycle l_idx arc_size = generate_n_arc cycle r_idx arc_size"
      using x_l_def x_r_def by simp

    have "l_idx = r_idx"
      using \<open>generate_n_arc cycle l_idx arc_size = generate_n_arc cycle r_idx arc_size\<close>
            \<open>l_idx < length cycle\<close> r_idx_bound unique_index_unique_arc
      by metis

    (* ======================================================================= *)
    (* 4. Translate hd element_arc to its cyclic index                         *)
    (* ======================================================================= *)
    have "hd element_arc = cycle ! element_index"
      unfolding assms(3) generate_n_arc_def
      using minimal_arc_size cycle_size el_idx_bound
      hd_rotate_conv_nth hd_take list.size(3)
    by (metis add.commute add.right_neutral
        arc_size
        canonically_ordered_monoid_add_class.lessE
        cycle_pos mod_less)

    (* ======================================================================= *)
    (* 5. Combine the shifts to find the contradiction                         *)
    (* ======================================================================= *)
    have "(l_idx + l_shift) mod length cycle = element_index"
      using hd_match \<open>hd element_arc = cycle ! element_index\<close>
            cycle_elements_distinct el_idx_bound cycle_pos
      by (metis mod_less_divisor nth_eq_iff_index_eq)

    hence "(((element_index + r_shift) mod length cycle + l_shift) mod length cycle = element_index)"
      using \<open>l_idx = r_idx\<close> r_idx_def by simp

    (* Collapse the nested modulo into a single addition *)
    also have "(((element_index + r_shift) mod length cycle + l_shift) mod length cycle = element_index) 
 \<longleftrightarrow> ((element_index + r_shift + l_shift) mod length cycle = element_index)" by presburger
      
    finally have combined_eq: "(element_index + (r_shift + l_shift)) mod length cycle = element_index"
      by (simp add: add.assoc)

    (* Define the total shift amount *)
    define total_shift where "total_shift = r_shift + l_shift"
    
    have "total_shift > 0" 
      using \<open>0 < r_shift\<close> \<open>0 < l_shift\<close> total_shift_def by simp
      
    (* This is where the maximum_arc_size assumption saves the day! *)
    have "total_shift < 2 * arc_size" 
      using \<open>r_shift < arc_size\<close> \<open>l_shift < arc_size\<close> total_shift_def by linarith
    hence "total_shift < length cycle" 
      using maximum_arc_size by linarith

    (* ======================================================================= *)
    (* 6. Case split the modulo to show total_shift = 0 or L, which is False   *)
    (* ======================================================================= *)
    have "element_index + total_shift < 2 * length cycle"
      using el_idx_bound \<open>total_shift < length cycle\<close> by linarith

    consider (no_wrap) "element_index + total_shift < length cycle" | (wrap) "element_index + total_shift \<ge> length cycle" 
      by linarith
    then show False
    proof cases
      case no_wrap
      hence "(element_index + total_shift) mod length cycle = element_index + total_shift" by simp
      hence "element_index = element_index + total_shift" 
        using combined_eq unfolding total_shift_def by simp
      thus False using \<open>total_shift > 0\<close> by simp
    next
      case wrap
      hence "(element_index + total_shift) mod length cycle = element_index + total_shift - length cycle" 
        using \<open>element_index + total_shift < 2 * length cycle\<close> by (simp add: mod_if)
      hence "element_index = element_index + total_shift - length cycle" 
        using combined_eq unfolding total_shift_def by simp
      thus False using \<open>total_shift < length cycle\<close>
      using wrap by auto
    qed
  qed

  show "right_neighbor_indices = {(index + arc_size) mod length cycle |index. index \<in> left_neighbor_indices}"
  proof (rule set_eqI, rule iffI)
    (* ======================================================================= *)
    (* PART 1: Forward direction (RHS \<subseteq> LHS)                                   *)
    (* ======================================================================= *)
    fix x
    assume "x \<in> {(index + arc_size) mod length cycle |index. index \<in> left_neighbor_indices}"
    then obtain l_idx where "l_idx \<in> left_neighbor_indices" 
      and x_def: "x = (l_idx + arc_size) mod length cycle" by blast

    (* Unpack the left neighbor *)
    from \<open>l_idx \<in> left_neighbor_indices\<close> obtain l_shift where "l_idx < length cycle"
      and "0 < l_shift" and "l_shift < arc_size"
      and hd_match: "cycle ! ((l_idx + l_shift) mod length cycle) = hd element_arc"
      unfolding assms(7) by auto

    have el_idx_bound: "element_index < length cycle"
      using assms(1,2) index_limit
    by (metis le_antisym linorder_not_le not_contains_impl_not_elem
        not_in_list)
    have cycle_pos: "length cycle > 0" using cycle_size by auto

    (* Identify the head element's index *)
    have "hd element_arc = cycle ! element_index"
      unfolding assms(3) generate_n_arc_def
      using minimal_arc_size cycle_size el_idx_bound
      hd_rotate_conv_nth hd_take list.size(3)
    by (metis add.commute add.right_neutral arc_size
        canonically_ordered_monoid_add_class.lessE cycle_pos
        mod_less)

    have "(l_idx + l_shift) mod length cycle = element_index"
      using hd_match \<open>hd element_arc = cycle ! element_index\<close>
            cycle_elements_distinct el_idx_bound cycle_pos
      mod_less_divisor nth_eq_iff_index_eq
    by metis

    (* Define the mirror right shift *)
    define r_shift where "r_shift = arc_size - l_shift"
    have "0 < r_shift" and "r_shift < arc_size"
      using \<open>0 < l_shift\<close> \<open>l_shift < arc_size\<close> r_shift_def by auto
      
    have "arc_size = l_shift + r_shift" 
      using r_shift_def \<open>l_shift < arc_size\<close> by simp
    
    (* Collapse the shift into the right neighbor form *)
    have "x = (l_idx + l_shift + r_shift) mod length cycle"
      using x_def \<open>arc_size = l_shift + r_shift\<close> by (simp add: add.assoc)
    also have "... = ((l_idx + l_shift) mod length cycle + r_shift) mod length cycle"
      by (metis mod_add_left_eq)
    also have "... = (element_index + r_shift) mod length cycle"
      using \<open>(l_idx + l_shift) mod length cycle = element_index\<close> by simp
    finally have "x = (element_index + r_shift) mod length cycle" .

    show "x \<in> right_neighbor_indices"
      unfolding assms(4)
      using \<open>x = (element_index + r_shift) mod length cycle\<close> \<open>0 < r_shift\<close> \<open>r_shift < arc_size\<close>
      by blast

  next
    (* ======================================================================= *)
    (* PART 2: Reverse direction (LHS \<subseteq> RHS)                                   *)
    (* ======================================================================= *)
    fix x
    assume "x \<in> right_neighbor_indices"
    then obtain r_shift where "0 < r_shift" and "r_shift < arc_size"
      and x_def: "x = (element_index + r_shift) mod length cycle"
      unfolding assms(4) by blast

    (* Define the mirror left shift and corresponding index *)
    define l_shift where "l_shift = arc_size - r_shift"
    have "0 < l_shift" and "l_shift < arc_size"
      using \<open>0 < r_shift\<close> \<open>r_shift < arc_size\<close> l_shift_def by auto

    define l_idx where "l_idx = (element_index + length cycle - l_shift) mod length cycle"
    
    have el_idx_bound: "element_index < length cycle"
      using assms(1,2) index_limit 
    by (metis nless_le not_contains_impl_not_elem not_in_list)
    have cycle_pos: "length cycle > 0" using cycle_size by auto

    have "l_idx < length cycle" unfolding l_idx_def using cycle_pos by simp

    (* Prove the algebraic connection: shifting l_idx forward by l_shift hits element_index *)
    have "(l_idx + l_shift) mod length cycle = element_index"
    proof -
      have "l_shift < length cycle" 
        using \<open>l_shift < arc_size\<close> maximum_arc_size by linarith
      hence "element_index + length cycle - l_shift + l_shift = element_index + length cycle"
        by linarith
      hence "(l_idx + l_shift) mod length cycle = ((element_index + length cycle - l_shift) mod length cycle + l_shift) mod length cycle"
        unfolding l_idx_def by simp
      also have "... = (element_index + length cycle - l_shift + l_shift) mod length cycle"
        by (metis mod_add_left_eq)
      also have "... = (element_index + length cycle) mod length cycle"
        using \<open>element_index + length cycle - l_shift + l_shift = element_index + length cycle\<close> by simp
      also have "... = element_index mod length cycle"
        by simp
      also have "... = element_index"
        using el_idx_bound by simp
      finally show ?thesis .
    qed

    (* Verify this makes it a valid left neighbor *)
    have "hd element_arc = cycle ! element_index"
      unfolding assms(3) generate_n_arc_def
      using minimal_arc_size cycle_size el_idx_bound
      hd_rotate_conv_nth hd_take list.size(3)
    by (metis add.commute add.right_neutral arc_size
        canonically_ordered_monoid_add_class.lessE cycle_pos mod_less)

    hence "cycle ! ((l_idx + l_shift) mod length cycle) = hd element_arc"
      using \<open>(l_idx + l_shift) mod length cycle = element_index\<close> by simp

    have "l_idx \<in> left_neighbor_indices"
      unfolding assms(7)
      using \<open>l_idx < length cycle\<close> \<open>0 < l_shift\<close> \<open>l_shift < arc_size\<close>
            \<open>cycle ! ((l_idx + l_shift) mod length cycle) = hd element_arc\<close>
      by blast

    (* Map it back to x *)
    have "arc_size = l_shift + r_shift" 
      using l_shift_def \<open>r_shift < arc_size\<close> by simp
    
    have "(l_idx + arc_size) mod length cycle = (l_idx + l_shift + r_shift) mod length cycle"
      using \<open>arc_size = l_shift + r_shift\<close> by (simp add: add.assoc)
    also have "... = ((l_idx + l_shift) mod length cycle + r_shift) mod length cycle"
      by (metis mod_add_left_eq)
    also have "... = (element_index + r_shift) mod length cycle"
      using \<open>(l_idx + l_shift) mod length cycle = element_index\<close> by simp
    finally have "(l_idx + arc_size) mod length cycle = x"
      using x_def by simp

    thus "x \<in> {(index + arc_size) mod length cycle |index. index \<in> left_neighbor_indices}"
      using \<open>l_idx \<in> left_neighbor_indices\<close> by blast
  qed

  show "intersecting_lists element_arc other_arc \<longleftrightarrow> (other_arc \<in> left_neighbors \<or> other_arc \<in> right_neighbors)"
  proof
    (* ======================================================================= *)
    (* DIRECTION 1: NEIGHBOR \<Longrightarrow> INTERSECTS                                     *)
    (* ======================================================================= *)
    assume dir1_assm: "other_arc \<in> left_neighbors \<or> other_arc \<in> right_neighbors"
    have cycle_pos: "length cycle > 0" using cycle_size by auto
    have arc_pos: "arc_size > 0" using minimal_arc_size by simp
    
    from dir1_assm show "intersecting_lists element_arc other_arc"
    proof 
      (* CASE 1: Left Neighbor *)
      assume "other_arc \<in> left_neighbors"
      then obtain l_idx where "l_idx \<in> left_neighbor_indices"
        and "other_arc = generate_n_arc cycle l_idx arc_size"
        unfolding assms(8) by blast
        
      from \<open>l_idx \<in> left_neighbor_indices\<close> obtain shift where "l_idx < length cycle"
        and "0 < shift" and "shift < arc_size"
        and hd_match: "cycle ! ((l_idx + shift) mod length cycle) = hd element_arc"
        unfolding assms(7) by auto
        
      have "length element_arc = arc_size" and "length other_arc = arc_size"
        unfolding assms(3) \<open>other_arc = generate_n_arc cycle l_idx arc_size\<close> generate_n_arc_def 
        using maximum_arc_size minimal_arc_size by simp_all
        
      have "other_arc ! shift = cycle ! ((l_idx + shift) mod length cycle)"
        unfolding \<open>other_arc = generate_n_arc cycle l_idx arc_size\<close> generate_n_arc_def
        using \<open>shift < arc_size\<close> nth_rotate
      by (metis add_leE maximum_arc_size mult_2 nth_take
          order_less_le_trans)
      also have "... = hd element_arc"
        using hd_match by simp
      also have "... = element_arc ! 0"
        unfolding assms(3) generate_n_arc_def using hd_conv_nth arc_pos
      by (metis \<open>length element_arc = arc_size\<close> assms(3) generate_n_arc_def
          linorder_not_less list.size(3) minimal_arc_size zero_less_one)
      finally have "other_arc ! shift = element_arc ! 0" .
      
      have "element_arc ! 0 \<in> set element_arc"
        using \<open>length element_arc = arc_size\<close> arc_pos nth_mem by force
      moreover have "other_arc ! shift \<in> set other_arc"
        using \<open>length other_arc = arc_size\<close> \<open>shift < arc_size\<close> nth_mem by force
      ultimately show "intersecting_lists element_arc other_arc"
        unfolding intersecting_lists_def using \<open>other_arc ! shift = element_arc ! 0\<close> by auto
        
    next
      (* CASE 2: Right Neighbor *)
      assume "other_arc \<in> right_neighbors"
      then obtain r_idx where "r_idx \<in> right_neighbor_indices"
        and "other_arc = generate_n_arc cycle r_idx arc_size"
        unfolding assms(5) by blast
        
      from \<open>r_idx \<in> right_neighbor_indices\<close> obtain shift where "0 < shift" and "shift < arc_size"
        and "r_idx = (element_index + shift) mod length cycle"
        unfolding assms(4) by auto
        
      have "length element_arc = arc_size" and "length other_arc = arc_size"
        unfolding assms(3) \<open>other_arc = generate_n_arc cycle r_idx arc_size\<close> generate_n_arc_def 
        using maximum_arc_size minimal_arc_size by simp_all
        
      have "element_arc ! shift = cycle ! ((element_index + shift) mod length cycle)"
        unfolding assms(3) generate_n_arc_def using \<open>shift < arc_size\<close> nth_rotate
      by (metis le_add2 maximum_arc_size mult_2 nth_take
          order_less_le_trans)
      also have "... = cycle ! (r_idx mod length cycle)"
        using \<open>r_idx = (element_index + shift) mod length cycle\<close> by simp
      also have "... = other_arc ! 0"
        unfolding \<open>other_arc = generate_n_arc cycle r_idx arc_size\<close> generate_n_arc_def
        using arc_pos nth_rotate
      by (metis cycle_pos nth_take verit_sum_simplify)
      finally have "element_arc ! shift = other_arc ! 0" .
      
      have "other_arc ! 0 \<in> set other_arc"
        using \<open>length other_arc = arc_size\<close> arc_pos nth_mem by force
      moreover have "element_arc ! shift \<in> set element_arc"
        using \<open>length element_arc = arc_size\<close> \<open>shift < arc_size\<close> nth_mem by force
      ultimately show "intersecting_lists element_arc other_arc"
        unfolding intersecting_lists_def using \<open>element_arc ! shift = other_arc ! 0\<close> by auto
    qed

  next
    (* ======================================================================= *)
    (* DIRECTION 2: INTERSECTS \<Longrightarrow> NEIGHBOR                                     *)
    (* ======================================================================= *)
    assume "intersecting_lists element_arc other_arc"
    
    have cycle_pos: "length cycle > 0" using cycle_size by auto
    have el_bound: "element_index < length cycle"
      using assms(1,2) index_limit 
    by (metis nat_less_le not_contains_impl_not_elem not_in_list)
      
    (* 1. Extract the shared element and its indices *)
    then obtain x where "x \<in> set element_arc" and "x \<in> set other_arc"
      unfolding intersecting_lists_def
    by (meson \<open>intersecting_lists element_arc other_arc\<close>
        intersecting_lists_def)
      
    (* Extract the generator index for other_arc *)
    from assms(10) have "\<exists>idx < length cycle. generate_n_arc cycle idx arc_size = other_arc"
      using generating_index_exists by auto
    then obtain other_idx where "other_idx < length cycle"
      and other_arc_def: "other_arc = generate_n_arc cycle other_idx arc_size"
      by blast

    have len_el: "length element_arc = arc_size" 
      unfolding assms(3) generate_n_arc_def using maximum_arc_size minimal_arc_size by simp
    have len_ot: "length other_arc = arc_size" 
      unfolding other_arc_def generate_n_arc_def using maximum_arc_size minimal_arc_size by simp
      
    from \<open>x \<in> set element_arc\<close> obtain i where "i < arc_size" and "x = element_arc ! i"
      by (metis in_set_conv_nth len_el)
    from \<open>x \<in> set other_arc\<close> obtain j where "j < arc_size" and "x = other_arc ! j"
      by (metis in_set_conv_nth len_ot)
      
    have el_val: "element_arc ! i = cycle ! ((element_index + i) mod length cycle)"
      unfolding assms(3) generate_n_arc_def using \<open>i < arc_size\<close> nth_rotate
    by (metis maximum_arc_size mult_2 nth_take order_less_le_trans
        trans_less_add1)
    have ot_val: "other_arc ! j = cycle ! ((other_idx + j) mod length cycle)"
      unfolding other_arc_def generate_n_arc_def using \<open>j < arc_size\<close> nth_rotate
    by (metis add_leE maximum_arc_size mult_2 nth_take
        order_less_le_trans)
      
    have bound_i: "(element_index + i) mod length cycle < length cycle" using cycle_pos by simp
    have bound_j: "(other_idx + j) mod length cycle < length cycle" using cycle_pos by simp
    
    have "cycle ! ((element_index + i) mod length cycle) = cycle ! ((other_idx + j) mod length cycle)"
      using \<open>x = element_arc ! i\<close> \<open>x = other_arc ! j\<close> el_val ot_val by simp
      
    hence idx_eq: "(element_index + i) mod length cycle = (other_idx + j) mod length cycle"
      using cycle_elements_distinct bound_i bound_j nth_eq_iff_index_eq by metis

    (* 2. Case split to map the index shift strictly to a left or right neighbor *)
    show "other_arc \<in> left_neighbors \<or> other_arc \<in> right_neighbors"
    proof (rule linorder_cases[of i j])
      (* IF THEY ALIGN EXACTLY, IT'S THE SAME ARC (CONTRADICTION) *)
      assume "i = j"
      have "(element_index + i) mod length cycle = (other_idx + i) mod length cycle"
        using idx_eq \<open>i = j\<close> by simp
        
      define K where "K = length cycle - i"
      have "((element_index + i) mod length cycle + K) mod length cycle = ((other_idx + i) mod length cycle + K) mod length cycle"
        using \<open>(element_index + i) mod length cycle = (other_idx + i) mod length cycle\<close> by simp
      moreover have "((element_index + i) mod length cycle + K) mod length cycle = (element_index + i + K) mod length cycle"
        by (metis mod_add_left_eq)
      moreover have "i + K = length cycle" using K_def \<open>i < arc_size\<close> maximum_arc_size by simp
      ultimately have LHS: "((element_index + i) mod length cycle + K) mod length cycle = element_index mod length cycle"
      by (metis ab_semigroup_add_class.add_ac(1) mod_add_self2)
        
      have "((other_idx + i) mod length cycle + K) mod length cycle = (other_idx + i + K) mod length cycle"
        by (metis mod_add_left_eq)
      hence RHS: "((other_idx + i) mod length cycle + K) mod length cycle = other_idx mod length cycle"
        using \<open>i + K = length cycle\<close>
      by (metis add.commute add.left_commute mod_add_self2)
        
      have "element_index mod length cycle = other_idx mod length cycle"
        using LHS RHS \<open>((element_index + i) mod length cycle + K) mod length cycle = ((other_idx + i) mod length cycle + K) mod length cycle\<close> by simp
      hence "element_index = other_idx"
        using el_bound \<open>other_idx < length cycle\<close> by simp
      hence "element_arc = other_arc"
        using assms(3) other_arc_def by simp
        
      thus ?thesis using assms(11) by simp

    next
      (* OTHER_ARC IS SHIFTED FORWARD (RIGHT NEIGHBOR) *)
      assume "j < i"
      define shift where "shift = i - j"
      have "0 < shift" and "shift < arc_size" using \<open>j < i\<close> \<open>i < arc_size\<close> shift_def by auto
      have "i = j + shift" using shift_def \<open>j < i\<close> by simp
      
      have "(element_index + shift + j) mod length cycle = (other_idx + j) mod length cycle"
        using idx_eq \<open>i = j + shift\<close> 
      by (simp add: add.commute add.left_commute)
        
      define K where "K = length cycle - j"
      have "((element_index + shift + j) mod length cycle + K) mod length cycle = ((other_idx + j) mod length cycle + K) mod length cycle"
        using \<open>(element_index + shift + j) mod length cycle = (other_idx + j) mod length cycle\<close> by simp
        
      moreover have "((element_index + shift + j) mod length cycle + K) mod length cycle = (element_index + shift + j + K) mod length cycle"
        by (metis mod_add_left_eq)
      moreover have "j + K = length cycle" using K_def \<open>j < arc_size\<close> maximum_arc_size by simp
      ultimately have LHS: "((element_index + shift + j) mod length cycle + K) mod length cycle = (element_index + shift) mod length cycle"
      by (metis group_cancel.add1 mod_add_self2)
        
      have "((other_idx + j) mod length cycle + K) mod length cycle = (other_idx + j + K) mod length cycle"
        by (metis mod_add_left_eq)
      hence RHS: "((other_idx + j) mod length cycle + K) mod length cycle = other_idx mod length cycle"
        using \<open>j + K = length cycle\<close>
      by (metis add.assoc mod_add_self2)
        
      have "(element_index + shift) mod length cycle = other_idx mod length cycle"
        using LHS RHS \<open>((element_index + shift + j) mod length cycle + K) mod length cycle = ((other_idx + j) mod length cycle + K) mod length cycle\<close> by simp
      hence "other_idx = (element_index + shift) mod length cycle"
        using \<open>other_idx < length cycle\<close> by simp
        
      have "other_idx \<in> right_neighbor_indices"
        using \<open>0 < shift\<close> \<open>shift < arc_size\<close> \<open>other_idx = (element_index + shift) mod length cycle\<close>
      using assms(4) by blast
      thus ?thesis using other_arc_def
        using assms(5) by blast

    next
      (* OTHER_ARC IS SHIFTED BACKWARD (LEFT NEIGHBOR) *)
      assume "i < j"
      define shift where "shift = j - i"
      have "0 < shift" and "shift < arc_size" using \<open>i < j\<close> \<open>j < arc_size\<close> shift_def by auto
      have "j = i + shift" using shift_def \<open>i < j\<close> by simp
      
      have "(element_index + i) mod length cycle = (other_idx + shift + i) mod length cycle"
        using idx_eq \<open>j = i + shift\<close>
      by presburger
        
      define K where "K = length cycle - i"
      have "((element_index + i) mod length cycle + K) mod length cycle = ((other_idx + shift + i) mod length cycle + K) mod length cycle"
        using \<open>(element_index + i) mod length cycle = (other_idx + shift + i) mod length cycle\<close> by simp
        
      moreover have "((element_index + i) mod length cycle + K) mod length cycle = (element_index + i + K) mod length cycle"
        by (metis mod_add_left_eq)
      moreover have "i + K = length cycle" using K_def \<open>i < arc_size\<close> maximum_arc_size by simp
      ultimately have LHS: "((element_index + i) mod length cycle + K) mod length cycle = element_index mod length cycle"
      by (metis add.assoc mod_add_self2)
        
      have "((other_idx + shift + i) mod length cycle + K) mod length cycle = (other_idx + shift + i + K) mod length cycle"
        by (metis mod_add_left_eq)
      hence RHS: "((other_idx + shift + i) mod length cycle + K) mod length cycle = (other_idx + shift) mod length cycle"
        using \<open>i + K = length cycle\<close>
      by (metis ab_semigroup_add_class.add_ac(1)
          mod_add_self2)
        
      have "element_index mod length cycle = (other_idx + shift) mod length cycle"
        using LHS RHS \<open>((element_index + i) mod length cycle + K) mod length cycle = ((other_idx + shift + i) mod length cycle + K) mod length cycle\<close> by simp
      hence "(other_idx + shift) mod length cycle = element_index"
        using el_bound by simp
        
      have "cycle ! ((other_idx + shift) mod length cycle) = cycle ! element_index"
        using \<open>(other_idx + shift) mod length cycle = element_index\<close> by simp
      also have "... = hd element_arc"
        unfolding assms(3) generate_n_arc_def using minimal_arc_size cycle_size el_bound
       hd_rotate_conv_nth hd_take list.size(3)
      by (metis arc_size less_nat_zero_code
          mod_less)
      finally have "cycle ! ((other_idx + shift) mod length cycle) = hd element_arc" .
      
      have "other_idx \<in> left_neighbor_indices"
        unfolding assms(7)
        using \<open>other_idx < length cycle\<close> \<open>0 < shift\<close> \<open>shift < arc_size\<close> \<open>cycle ! ((other_idx + shift) mod length cycle) = hd element_arc\<close>
        by blast
        
      thus ?thesis using other_arc_def
      using assms(8) by blast
    qed
  qed

qed


theorem intersecting_n_arcs_upper_limit: "length arcs \<le> arc_size"
proof cases
  assume "arc_size = 1"
  show ?thesis
  proof (rule ccontr)
      assume "\<not> (length arcs \<le> arc_size)"
      then have "length arcs > arc_size" by simp
      then have "length arcs > 1" by (metis \<open>arc_size < length arcs\<close> \<open>arc_size = 1\<close>)
      
      have "card (set arcs) = length arcs" using distinct_arcs distinct_card by auto
      hence "card (set arcs) > 1" using \<open>length arcs > 1\<close> by simp
      
      then obtain arc1 arc2 where "arc1 \<in> set arcs" and "arc2 \<in> set arcs" and "arc1 \<noteq> arc2"
        using card_le_Suc0_iff_eq linorder_not_less
      by (metis One_nat_def list.set_finite)
        
      have "length arc1 = 1" and "length arc2 = 1"
        using \<open>arc1 \<in> set arcs\<close> \<open>arc2 \<in> set arcs\<close> \<open>arc_size = 1\<close> intersecting_arcs intersecting_n_arcs_def by auto
        
      have "intersecting_lists arc1 arc2"
        using \<open>arc1 \<in> set arcs\<close> \<open>arc2 \<in> set arcs\<close> intersecting_arcs intersecting_arcs_def intersecting_n_arcs_def by blast
        
      then obtain e where "e \<in> set arc1" and "e \<in> set arc2" unfolding intersecting_lists_def by auto
      hence "arc1 = [e]" and "arc2 = [e]"
        using \<open>length arc1 = 1\<close> \<open>length arc2 = 1\<close> length_0_conv length_Suc_conv set_ConsD by (metis One_nat_def hd_in_set in_set_replicate)+
        
      thus False using \<open>arc1 \<noteq> arc2\<close> by simp
  qed
next
  assume "arc_size \<noteq> 1"
  then have "arc_size > 1" using minimal_arc_size nat_less_le by blast
  show ?thesis
  proof cases
    assume "length arcs = 0"
    then show ?thesis by simp
  next
    assume "\<not> (length arcs = 0)"
    then have "length arcs \<noteq> 0" by simp
    then have "length arcs > 0" by simp
    have "length arcs = 1 \<longrightarrow> ?thesis" by (metis minimal_arc_size)
    fix element_arc other_arc
    assume "length arcs > 1"
    assume "element_arc \<in> set arcs"
    define element where "element = hd element_arc"
    assume "other_arc \<in> set arcs"
    assume "element_arc \<noteq> other_arc"
    have "hd element_arc \<in> set cycle" by (metis \<open>element_arc \<in> set arcs\<close> arc_element_index_to_cycle_index arc_size fixed_arc_size in_set_conv_nth index_of_arc_elements_exist indices_of_arc_elements list.set_sel(1) list.size(3)
        n_arc_of_cycle_def nat_less_le)
    define arc_index where "arc_index = index_of_element element cycle"
    have "element_arc = generate_n_arc cycle arc_index arc_size" by (simp add: \<open>element_arc \<in> set arcs\<close> arc_generator_head arc_index_def element_def)
    define right_neighbor_indices where "right_neighbor_indices  = {(arc_index + shift) mod (length cycle) | shift. 0 < shift \<and> shift < arc_size}"
    have "right_neighbor_indices \<noteq> {}" using \<open>1 < arc_size\<close> right_neighbor_indices_def by auto
    define right_neighbors where "right_neighbors = {generate_n_arc cycle index arc_size | index. index \<in> right_neighbor_indices}"
    have "right_neighbors \<noteq> {}" using \<open>right_neighbor_indices \<noteq> {}\<close> right_neighbors_def by blast
    define left_neighbor_indices where "left_neighbor_indices = {index :: nat. index < length cycle \<and> (\<exists>shift. 0 < shift \<and> shift < arc_size \<and> cycle ! ((index + shift) mod (length cycle)) = hd element_arc)}"
     have "left_neighbor_indices \<noteq> {}"
   proof -
      define l_shift where "l_shift = (1::nat)"
      have "0 < l_shift" and "l_shift < arc_size" using \<open>arc_size > 1\<close> l_shift_def by auto
      
      define l_idx where "l_idx = (arc_index + length cycle - l_shift) mod length cycle"
      have hd_arc_idx: "hd element_arc = cycle ! arc_index"
        using  \<open>element_arc = generate_n_arc cycle arc_index arc_size\<close> arc_generator_head arc_index_def element_def
      by (metis \<open>hd element_arc \<in> set cycle\<close> index_correct not_contains_impl_not_elem)
        
      have "(l_idx + l_shift) mod length cycle = arc_index"
        unfolding l_idx_def using \<open>arc_size > 1\<close> maximum_arc_size l_shift_def 
        using le_add_diff_inverse mod_add_left_eq mod_add_right_eq nat_less_le
      by (smt (verit, best) \<open>element_arc \<in> set arcs\<close> arc_context.fixed_arc_size arc_context.index_of_arc_elements_exist arc_context_axioms arc_index_def arc_size element_def le_add2
          le_add_diff_inverse2 list.set_sel(1) list.size(3) mod_add_self2 mod_less mult_2 n_arc_of_cycle_def order_less_le_trans)
        
      have "l_idx < length cycle" unfolding l_idx_def using cycle_size
      by (meson \<open>hd element_arc \<in> set cycle\<close> length_pos_if_in_set mod_less_divisor)
      
      have "l_idx \<in> left_neighbor_indices"
        unfolding left_neighbor_indices_def 
        using \<open>l_idx < length cycle\<close> \<open>0 < l_shift\<close> \<open>l_shift < arc_size\<close> hd_arc_idx \<open>(l_idx + l_shift) mod length cycle = arc_index\<close> 
        by auto
        
      thus ?thesis by blast
    qed
    define left_neighbors where "left_neighbors = {generate_n_arc cycle index arc_size | index. index \<in> left_neighbor_indices}"
    have "left_neighbors \<noteq> {}" using \<open>left_neighbor_indices \<noteq> {}\<close> left_neighbors_def by blast
    fix right_neighbor_arc left_neighbor_arc
    assume "right_neighbor_arc \<in> right_neighbors"
    assume "left_neighbor_arc \<in> left_neighbors"
    have "left_neighbors \<inter> right_neighbors = {}"
      using neighbors[of element arc_index element_arc right_neighbor_indices right_neighbors
          right_neighbor_arc left_neighbor_indices left_neighbors left_neighbor_arc other_arc]
        \<open>hd element_arc \<in> set cycle\<close>[folded element_def] arc_index_def
        \<open>element_arc = generate_n_arc cycle arc_index arc_size\<close> right_neighbor_indices_def
        right_neighbors_def \<open>right_neighbor_arc \<in> right_neighbors\<close> left_neighbor_indices_def
        left_neighbors_def \<open>left_neighbor_arc \<in> left_neighbors\<close> \<open>element_arc \<noteq> other_arc\<close> using \<open>other_arc \<in> set arcs\<close> by fastforce
    define left_arc_neighbors where  "left_arc_neighbors = set arcs \<inter> left_neighbors"
    define right_arc_neighbors where "right_arc_neighbors = set arcs \<inter> right_neighbors"
    have "left_arc_neighbors \<inter> right_arc_neighbors = {}" using \<open>left_neighbors \<inter> right_neighbors = {}\<close> left_arc_neighbors_def right_arc_neighbors_def by blast
    have "element_arc \<notin> left_arc_neighbors \<and> element_arc \<notin> right_arc_neighbors" using neighbors[of element arc_index element_arc right_neighbor_indices right_neighbors
          right_neighbor_arc left_neighbor_indices left_neighbors left_neighbor_arc other_arc]
        \<open>hd element_arc \<in> set cycle\<close>[folded element_def] arc_index_def
        \<open>element_arc = generate_n_arc cycle arc_index arc_size\<close> right_neighbor_indices_def
        right_neighbors_def \<open>right_neighbor_arc \<in> right_neighbors\<close> left_neighbor_indices_def
        left_neighbors_def \<open>left_neighbor_arc \<in> left_neighbors\<close> \<open>element_arc \<noteq> other_arc\<close>
        left_arc_neighbors_def right_arc_neighbors_def using \<open>other_arc \<in> set arcs\<close> by fastforce
    have "left_arc_neighbors \<union> right_arc_neighbors \<union> {element_arc}= set arcs" sorry
    have "card left_neighbors = arc_size - 1" using neighbors[of element arc_index element_arc right_neighbor_indices right_neighbors
          right_neighbor_arc left_neighbor_indices left_neighbors left_neighbor_arc other_arc]
        \<open>hd element_arc \<in> set cycle\<close>[folded element_def] arc_index_def
        \<open>element_arc = generate_n_arc cycle arc_index arc_size\<close> right_neighbor_indices_def
        right_neighbors_def \<open>right_neighbor_arc \<in> right_neighbors\<close> left_neighbor_indices_def
        left_neighbors_def \<open>left_neighbor_arc \<in> left_neighbors\<close> \<open>element_arc \<noteq> other_arc\<close> using \<open>other_arc \<in> set arcs\<close> by argo
    then have "card left_arc_neighbors \<le> arc_size - 1" by (metis \<open>arc_size \<noteq> 1\<close> card.infinite card_mono diff_is_0_eq diffs0_imp_equal inf_le2 left_arc_neighbors_def minimal_arc_size)
    have "length arcs = card left_arc_neighbors + card right_arc_neighbors + 1"
      by (metis (no_types, lifting) Int_insert_right_if0 Int_left_commute One_nat_def UnE Un_Int_eq(2) \<open>element_arc \<notin> left_arc_neighbors \<and> element_arc \<notin> right_arc_neighbors\<close>
        \<open>left_arc_neighbors \<inter> right_arc_neighbors = {}\<close> \<open>left_arc_neighbors \<union> right_arc_neighbors \<union> {element_arc} = set arcs\<close> bij_betw_same_card card.empty card_Un_disjoint card_insert_disjoint
        equals0D finite_Un finite_insert index_set_size indices_are_representative list.set_finite)
    have "card right_neighbors = arc_size - 1" using neighbors[of element arc_index element_arc right_neighbor_indices right_neighbors
          right_neighbor_arc left_neighbor_indices left_neighbors left_neighbor_arc other_arc]
        \<open>hd element_arc \<in> set cycle\<close>[folded element_def] arc_index_def
        \<open>element_arc = generate_n_arc cycle arc_index arc_size\<close> right_neighbor_indices_def
        right_neighbors_def \<open>right_neighbor_arc \<in> right_neighbors\<close> left_neighbor_indices_def
        left_neighbors_def \<open>left_neighbor_arc \<in> left_neighbors\<close> \<open>element_arc \<noteq> other_arc\<close> 
    by (metis arc_index_def \<open>right_neighbor_arc \<in> right_neighbors\<close> \<open>element_arc = generate_n_arc cycle arc_index arc_size\<close> \<open>left_neighbor_arc \<in> left_neighbors\<close> \<open>element_arc \<noteq> other_arc\<close> \<open>element \<in> set cycle\<close> \<open>other_arc \<in> set arcs\<close>)
    then have "card right_arc_neighbors \<le> arc_size - 1"
      by (metis \<open>1 < arc_size\<close> card.infinite card_mono diff_is_0_eq inf_commute inf_sup_ord(1) linorder_not_less right_arc_neighbors_def)
    have "length arcs = card left_arc_neighbors + card right_arc_neighbors + 1"
      by (metis (no_types, lifting) Int_insert_right_if0 Int_left_commute One_nat_def UnE Un_Int_eq(2) \<open>element_arc \<notin> left_arc_neighbors \<and> element_arc \<notin> right_arc_neighbors\<close>
        \<open>left_arc_neighbors \<inter> right_arc_neighbors = {}\<close> \<open>left_arc_neighbors \<union> right_arc_neighbors \<union> {element_arc} = set arcs\<close> bij_betw_same_card card.empty card_Un_disjoint card_insert_disjoint
        equals0D finite_Un finite_insert index_set_size indices_are_representative list.set_finite)
    define left_arc_neighbor_indices where "left_arc_neighbor_indices = {index_of_element (hd x) cycle |x .  x \<in> left_arc_neighbors}"
    have "card left_arc_neighbor_indices = card left_arc_neighbors" sorry
    define right_pairs_of_left where "right_pairs_of_left = {(index + arc_size) mod (length cycle)| index. index \<in> left_arc_neighbor_indices}"
    have "card right_pairs_of_left = card left_arc_neighbor_indices" using neighbors[of element arc_index element_arc right_neighbor_indices right_neighbors
          right_neighbor_arc left_neighbor_indices left_neighbors left_neighbor_arc other_arc]
        \<open>hd element_arc \<in> set cycle\<close>[folded element_def] arc_index_def
        \<open>element_arc = generate_n_arc cycle arc_index arc_size\<close> right_neighbor_indices_def
        right_neighbors_def \<open>right_neighbor_arc \<in> right_neighbors\<close> left_neighbor_indices_def
        left_neighbors_def \<open>left_neighbor_arc \<in> left_neighbors\<close> \<open>element_arc \<noteq> other_arc\<close>
      using right_pairs_of_left_def sorry
    define right_arc_pairs_of_left where "right_arc_pairs_of_left = {generate_n_arc cycle index arc_size | index . index \<in> right_pairs_of_left}"
    have "card right_pairs_of_left = card right_arc_pairs_of_left" using neighbors[of element arc_index element_arc right_neighbor_indices right_neighbors
          right_neighbor_arc left_neighbor_indices left_neighbors left_neighbor_arc other_arc]
        \<open>hd element_arc \<in> set cycle\<close>[folded element_def] arc_index_def
        \<open>element_arc = generate_n_arc cycle arc_index arc_size\<close> right_neighbor_indices_def
        right_neighbors_def \<open>right_neighbor_arc \<in> right_neighbors\<close> left_neighbor_indices_def
        left_neighbors_def \<open>left_neighbor_arc \<in> left_neighbors\<close> \<open>element_arc \<noteq> other_arc\<close>
        right_pairs_of_left_def right_arc_pairs_of_left_def sorry
    have subset_arcs: "right_arc_pairs_of_left \<subseteq> right_neighbors" using neighbors[of element arc_index element_arc right_neighbor_indices right_neighbors
          right_neighbor_arc left_neighbor_indices left_neighbors left_neighbor_arc other_arc]
        \<open>hd element_arc \<in> set cycle\<close>[folded element_def] arc_index_def
        \<open>element_arc = generate_n_arc cycle arc_index arc_size\<close> right_neighbor_indices_def
        right_neighbors_def \<open>right_neighbor_arc \<in> right_neighbors\<close> left_neighbor_indices_def
        left_neighbors_def \<open>left_neighbor_arc \<in> left_neighbors\<close> \<open>element_arc \<noteq> other_arc\<close>
        right_arc_pairs_of_left_def right_pairs_of_left_def sorry
    have "\<forall>arc \<in> right_arc_pairs_of_left. arc \<notin> set arcs"
    proof
      fix arc
      assume "arc \<in> right_arc_pairs_of_left"
      obtain right_index where "arc = generate_n_arc cycle right_index arc_size \<and> right_index \<in> right_pairs_of_left" using \<open>arc \<in> right_arc_pairs_of_left\<close> right_arc_pairs_of_left_def by auto
      obtain left_index where "(left_index + arc_size) mod (length cycle) = right_index \<and> left_index \<in> left_arc_neighbor_indices" using \<open>arc = generate_n_arc cycle right_index arc_size \<and> right_index \<in> right_pairs_of_left\<close> right_pairs_of_left_def by blast
      define left_arc where "left_arc = generate_n_arc cycle left_index arc_size"
      have "left_arc \<in> left_arc_neighbors" sorry
      have "\<not> intersecting_lists left_arc arc" sorry
      have "left_arc \<in> set arcs" using \<open>left_arc \<in> left_arc_neighbors\<close> left_arc_neighbors_def by fastforce
      show "arc \<notin> set arcs" by (metis \<open>\<not> intersecting_lists left_arc arc\<close> intersecting_arcs_def intersecting_n_arcs_def intersecting_arcs \<open>left_arc \<in> set arcs\<close>)
    qed
    then have "right_arc_neighbors \<subseteq> right_neighbors - right_arc_pairs_of_left" using right_arc_neighbors_def by blast
    then have "card right_arc_neighbors \<le> card (right_neighbors - right_arc_pairs_of_left)" by (metis \<open>card right_arc_neighbors \<le> arc_size - 1\<close> \<open>card right_neighbors = arc_size - 1\<close> card.infinite card_mono finite_Diff)
    then have "... = card right_neighbors - card right_arc_pairs_of_left"
      by (metis \<open>1 < arc_size\<close> \<open>card right_neighbors = arc_size - 1\<close> card_Diff_subset card_gt_0_iff finite_subset subset_arcs zero_less_diff)
    then have "... = card right_neighbors - card left_arc_neighbors" using \<open>card left_arc_neighbor_indices = card left_arc_neighbors\<close> \<open>card right_pairs_of_left = card left_arc_neighbor_indices\<close> \<open>card right_pairs_of_left = card right_arc_pairs_of_left\<close> by presburger
    have "card left_arc_neighbors + card right_arc_neighbors \<le> arc_size - 1"
      using \<open>card (right_neighbors - right_arc_pairs_of_left) = card right_neighbors - card right_arc_pairs_of_left\<close> \<open>card left_arc_neighbors \<le> arc_size - 1\<close>
      \<open>card right_arc_neighbors \<le> card (right_neighbors - right_arc_pairs_of_left)\<close> \<open>card right_neighbors - card right_arc_pairs_of_left = card right_neighbors - card left_arc_neighbors\<close>
      \<open>card right_neighbors = arc_size - 1\<close> by linarith
    then have "length arcs \<le> arc_size" using \<open>length arcs = card left_arc_neighbors + card right_arc_neighbors + 1\<close> minimal_arc_size by linarith
  qed
qed


end

end
