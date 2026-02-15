theory List_Helper

imports Main

begin


fun contains_element :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "contains_element element []  \<longleftrightarrow> False" |
  "contains_element element (x#xs) \<longleftrightarrow> (if element = x then True else contains_element element xs)"


fun index_of_element :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "index_of_element element Nil = 0" |
  "index_of_element element (Cons x xs)  = (if x = element then 0 else (1 + index_of_element element xs))"


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


lemma not_contains_head:
  fixes sequence :: "'a list"
  fixes first_element :: "'a"
  fixes searched_element :: "'a"
  shows "index_of_element searched_element (Cons first_element sequence) = length (Cons first_element sequence) \<longrightarrow> first_element \<noteq> searched_element"
proof
  have length_geq_0: "length (Cons first_element sequence) > 0" by simp
  assume premise: "index_of_element searched_element (Cons first_element sequence) = length (Cons first_element sequence)"
  with length_geq_0 have index_geq_0: "index_of_element searched_element (Cons first_element sequence) > 0" by simp
  show "first_element \<noteq> searched_element" 
  proof (rule ccontr)
    assume "\<not>(first_element \<noteq> searched_element)"
    then have "first_element = searched_element" by simp
    then have "index_of_element searched_element (Cons first_element sequence) = 0" by simp
    with local.index_geq_0 show "False" by simp
  qed
qed


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


lemma in_list:
  fixes tail :: "'a list"
  fixes sequence_item :: "'a"
  fixes searched_item :: "'a"
  assumes sequence_nempty: "sequence = sequence_item # tail"
  shows "index_of_element searched_item sequence < length sequence \<longleftrightarrow> contains_element searched_item sequence" 
  by (simp add: index_limit nat_less_le not_in_list)


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

end