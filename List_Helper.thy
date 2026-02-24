theory List_Helper

(*
 * This theory introduces helper lemmas for lists.
 * Circular permutations are defined as lists with distinct elements in this project.
 * For the project, a function is needed which returns the index of an element in a list.
 * This theory introduces this function and proves properties for this function.
 *)

imports Main

begin

(*
 * A boolean function that returns true if an element is in a list.
 *)
fun contains_element :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "contains_element element []  \<longleftrightarrow> False" |
  "contains_element element (x#xs) \<longleftrightarrow> (if element = x then True else contains_element element xs)"


(*
 * The function which returns the index of an element in a list. If the element is not in the list,
 * the value returned is the length of a list (a design with maybe could also have been more
 * appropriate).
 *)
fun index_of_element :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "index_of_element element Nil = 0" |
  "index_of_element element (Cons x xs)  = (if x = element then 0 else (1 + index_of_element element xs))"


(*
 * The first lemma that gives an upper limit to the value of index_of_element.
 *)
lemma index_limit:
  fixes sequence :: "'a list"
  fixes sequence_item :: "'a"
  shows "index_of_element sequence_item sequence \<le> length sequence"
proof (induction sequence)
  case Nil
  show ?case by simp
  case (Cons first_element rest)
  show ?case using Cons.IH by simp
qed

 
(*
 * A lemma that proves that the head of a list is not the searched element if the index of the
 * searched element is returned as the length of the list. Hence this lemma is the first step
 * to prove the behaviour of index_of_element if the element is not in the list.
 *)
lemma not_contains_head:
  fixes sequence :: "'a list"
  fixes first_element :: "'a"
  fixes searched_element :: "'a"
  shows "index_of_element searched_element (Cons first_element sequence) 
    = length (Cons first_element sequence) \<longrightarrow> first_element \<noteq> searched_element"
proof
  have length_geq_0: "length (Cons first_element sequence) > 0" by simp
  assume premise: "index_of_element searched_element (Cons first_element sequence) 
    = length (Cons first_element sequence)"
  with length_geq_0 have index_geq_0: "index_of_element searched_element (Cons first_element sequence) > 0" by simp
  show "first_element \<noteq> searched_element" 
  proof (rule ccontr)
    assume "\<not>(first_element \<noteq> searched_element)"
    then have "first_element = searched_element" by simp
    then have "index_of_element searched_element (Cons first_element sequence) = 0" by simp
    with local.index_geq_0 show "False" by simp
  qed
qed


(*
 * This lemma proves that the searched element is not in the list iff the index_of_element returns
 * the length of the list as value.
 *)
lemma not_in_list:
  fixes sequence :: "'a list"
  fixes sequence_item :: "'a"
  shows "index_of_element sequence_item sequence = length sequence \<longleftrightarrow> \<not>(contains_element sequence_item sequence)"
proof (induction sequence)
  show "index_of_element sequence_item Nil = length Nil \<longleftrightarrow> \<not>(contains_element sequence_item Nil)" by simp
next 
  fix x xs assume IH: "index_of_element sequence_item xs = length xs \<longleftrightarrow> \<not>(contains_element sequence_item xs)"
  from IH show "index_of_element sequence_item (x#xs) = length (x#xs) \<longleftrightarrow> \<not>(contains_element sequence_item (x#xs))" by simp
qed


(*
 * The counterpart of the lemma not_in_list which states that the value index_of_element being less
 * than the length of the list being equivalent to the element being in the list.
 *)
lemma in_list:
  fixes tail :: "'a list"
  fixes sequence_item :: "'a"
  fixes searched_item :: "'a"
  assumes sequence_nempty: "sequence = sequence_item # tail"
  shows "index_of_element searched_item sequence < length sequence \<longleftrightarrow> contains_element searched_item sequence" 
  by (simp add: index_limit nat_less_le not_in_list)


(*
 * This lemma states that the index_of_element actually returns the index of the searched element.
 *)
lemma index_correct:
  fixes sequence :: "'a list"
  fixes item :: "'a"
  shows "contains_element item sequence \<longrightarrow>  sequence ! (index_of_element item sequence) = item"
proof (induction sequence)
  show "contains_element item Nil \<longrightarrow>  Nil ! (index_of_element item Nil) = item" by simp
next
  fix x xs assume IH: "contains_element item xs \<longrightarrow>  xs ! (index_of_element item xs) = item"
  then show "contains_element item (x # xs) \<longrightarrow>  (x # xs) ! (index_of_element item (x # xs)) = item" by simp
qed


(*
 * A lemma that binds the defined contains_element boolean function to the set of a list.
 * If contains_element is false, then the searched item is not in the set of the elements of the
 * list.
 *)
lemma not_contains_impl_not_elem: 
  fixes sequence :: "'a list"
  fixes item :: "'a"
  shows "\<not>(contains_element item sequence) \<longrightarrow> item \<notin> set sequence" 
proof (induction sequence)
  show "\<not>(contains_element item Nil) \<longrightarrow> item \<notin> set Nil" by auto
next
  fix x xs assume IH: "\<not>(contains_element item xs) \<longrightarrow> item \<notin> set xs"
  then show "\<not>(contains_element item (x # xs)) \<longrightarrow> item \<notin> set (x # xs)" by simp
qed


(*
 * This lemma utilizes the lemma above to state that the contains_element function is a logical
 * equivalent to the set containment.
 *)
lemma contains_eq_elem:
  fixes sequence :: "'a list"
  fixes item :: "'a"
  shows "contains_element item sequence \<longleftrightarrow> item \<in> set sequence"
proof
  assume "contains_element item sequence"
  then show "item \<in> set sequence" by (metis in_list index_correct nth_mem contains_element.elims(1))
next
  assume "item \<in> set sequence"
  then show "contains_element item sequence" using not_contains_impl_not_elem by fastforce
qed


(*
 * A helper lemma that proves that the head of a list has index 0.
 *)
lemma first_index:
  fixes list ::"'a list"
  shows "list \<noteq> [] \<longrightarrow> index_of_element (hd list) list = 0"
    by (metis index_of_element.elims list.sel(1))


(*
 * A helper lemma that proves that if the list contains unique elements that the index of the last
 * element of the list is one less than the length of the list.
 * Unique elements is necessary since the last element could also occur in other places in the list,
 * index_of_element returns the first index of a value.
 *)
lemma last_index:
  fixes list ::"'a list"
  shows "list \<noteq> [] \<and> distinct list  \<longrightarrow> index_of_element (last list) list = length list - 1"
    by (metis One_nat_def diff_less diff_self_eq_0 distinct_Ex1 index_correct index_limit last_conv_nth 
    last_in_set lessI less_imp_diff_less nat_less_le not_contains_impl_not_elem not_in_list)


definition list_of :: "'a set \<Rightarrow> 'a list" where
  "list_of A = (SOME l. set l = A \<and> distinct l)"


lemma list_of_props:
  assumes "finite S"
  shows "set (list_of S) = S" and "distinct (list_of S)"
proof -
  let ?witness = "(SOME l. set l = S \<and> distinct l)"
  have "\<exists>l. set l = S \<and> distinct l"
    using assms finite_distinct_list by auto
  then have "set ?witness = S \<and> distinct ?witness"
    by (rule someI_ex)
  then show "set (list_of S) = S" and "distinct (list_of S)"
    unfolding list_of_def by auto
qed


lemma list_of_rec:
  fixes S :: "'a set set"
  assumes "finite S" and "\<forall> s \<in> S. finite s"
  shows "set ` list_of ` S = S"
    using assms(2) list_of_props(1) by fastforce


end