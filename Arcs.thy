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

theorem intersecting_n_arcs_upper_limit: "length arcs \<le> arc_size" sorry

theorem maximal_intersecting_n_arcs: "\<exists>arcs. length arcs = arc_size" sorry

end
