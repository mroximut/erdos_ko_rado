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
  have "last arc2 \<in> set arc1" sorry
  then show ?thesis by simp
qed


theorem intersecting_n_arcs_upper_limit: "length arcs \<le> arc_size"
proof -
  define arc_heads where "arc_heads = map (\<lambda>x. hd x) arcs"
  have "distinct arc_heads" using arc_heads_def heads_eq by blast
  then have "length arc_heads = length arcs" using \<open>distinct arc_heads\<close> arc_heads_def by auto
  define arc_head_indices where "arc_head_indices = map (\<lambda>x. index_of_element x cycle) arc_heads"
  have "distinct arc_head_indices" by (metis (no_types, lifting) \<open>arc_heads \<equiv> map hd arcs\<close>
     arc_generator_head arc_head_indices_def distinct_arcs distinct_conv_nth length_map nth_map nth_mem)
  then have "length arc_head_indices = length arcs" using \<open>distinct arc_head_indices\<close> \<open>arc_heads \<equiv> map hd arcs\<close> arc_head_indices_def by auto
  define minimum_index where "minimum_index = Min (set arc_head_indices)"
  define right_neighbor_indices where "right_neighbor_indices = set arc_heads \<inter> set (generate_n_arc cycle minimum_index arc_size)"
  then have "card right_neighbor_indices \<le> arc_size"
qed


theorem maximal_intersecting_n_arcs: "\<exists>arcs :: 'a list list. intersecting_n_arcs arcs cycle arc_size \<and> distinct arcs \<and> length arcs = arc_size" sorry
end

end
