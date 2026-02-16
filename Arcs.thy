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

definition intersecting_arcs :: "'a list list \<Rightarrow> 'a list  \<Rightarrow> bool" where
  "intersecting_arcs arcs cycle \<longleftrightarrow> (\<forall>arc \<in> set arcs. (arc_of_cycle arc cycle) \<and> (\<forall>other_arc \<in> set arcs. set arc \<inter> set other_arc \<noteq> {}))"

definition intersecting_n_arcs :: "'a list list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "intersecting_n_arcs arcs cycle n \<longleftrightarrow> intersecting_arcs arcs cycle \<and> (\<forall>arc \<in> set arcs. length arc = n)" 

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


lemma unique_index_unique_arc:
  fixes n1 n2 :: nat 
  assumes "n1 < length cycle"
  assumes "n2 < length cycle"
  shows "n1 \<noteq> n2 \<longleftrightarrow> generate_n_arc cycle n1 arc_size \<noteq> generate_n_arc cycle n2 arc_size"
  by (metis Ex_list_of_length assms(1,2)
      cycle_elements_distinct cycle_size distinct_conv_nth
      generate_n_arc_def hd_rotate_conv_nth hd_take
      length_greater_0_conv less_not_refl minimal_arc_size
      mod_less one_eq_numeral_iff order_less_le_trans
      zero_neq_numeral)


lemma generating_index_exists: "arc \<in> set arcs \<longrightarrow> (\<exists>index < length cycle. generate_n_arc cycle index arc_size = arc)"
  by (metis arc_of_cycle_def fixed_arc_size generate_n_arc_def n_arc_of_cycle_def)

lemma get_generator_index:
  fixes arc :: "'a list"
  assumes "arc \<in> set arcs"
  obtains index where "generate_n_arc cycle index arc_size = arc \<and> index < length cycle" 
  using generating_index_exists assms by auto

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


lemma arc_indices_are_indices: 
  shows "\<forall>index \<in> n_arc_indices cycle arcs arc_size. \<exists>arc \<in> set arcs. (generate_n_arc cycle index arc_size = arc)" by (simp add: n_arc_indices_def)

lemma arc_indices_exist: "\<forall>arc \<in> set arcs. \<exists>index \<in> n_arc_indices cycle arcs arc_size. (generate_n_arc cycle index arc_size = arc)" 
  by (metis (no_types, lifting) get_generator_index mem_Collect_eq n_arc_indices_def)

lemma generator_index_bijection: "set arcs =  (\<lambda>index. generate_n_arc cycle index arc_size) ` (n_arc_indices cycle arcs arc_size)" using arc_indices_are_indices arc_indices_exist by fastforce

lemma index_set_size: "length arcs = card (n_arc_indices cycle arcs arc_size)"
proof -
  have "length arcs = card (set arcs)" using distinct_arcs by (simp add: distinct_card)
  then have "... = card (n_arc_indices cycle arcs arc_size)" sorry
  show "length arcs = card (n_arc_indices cycle arcs arc_size)"  sorry
qed


lemma index_distance:
  fixes n1 n2 :: nat
  assumes "n1 < length cycle"
  assumes "n2 < length cycle"
  shows "n1 \<le> n2 \<and> n2 < n1 + arc_size \<longrightarrow> (cycle ! n2) \<in> set (generate_n_arc cycle n1 arc_size)" sorry

theorem intersecting_n_arcs_upper_limit: "length arcs \<le> arc_size" sorry

theorem maximal_intersecting_n_arcs: "\<exists>arcs :: 'a list list. intersecting_n_arcs arcs cycle arc_size \<and> distinct arcs \<and> length arcs = arc_size" 
proof
  define indices where "indices = [0..<arc_size]"
  define arcs where "arcs = map (\<lambda>index. generate_n_arc cycle index arc_size) indices"
  show "intersecting_n_arcs arcs cycle arc_size \<and> distinct arcs \<and> length arcs = arc_size" sorry
qed


end

end
