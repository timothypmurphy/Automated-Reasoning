theory Practical
imports Main
begin

(***************************First-order logic*************************************)

(*1 mark*)
lemma "A\<or>A \<longrightarrow> A"
  apply (rule impI)
  by (erule disjE)
  

(*1 mark*)
lemma "(P\<longrightarrow>R)\<longrightarrow>(\<not>P\<or>R)"
  apply (rule impI)
  apply (rule classical)
  apply (erule impE)
   apply (rule classical)
   apply (erule notE)
  apply (rule disjI1)
   apply assumption
  by (rule disjI2)

(*1 mark*)
lemma "(P\<and>Q\<longrightarrow>R)\<longrightarrow>P\<longrightarrow>Q\<longrightarrow>R"
  apply (rule impI)+
  apply (rule classical)
  apply (erule impE)
  by (rule conjI)

(*3 marks*)
lemma "\<not>\<not>P \<or> \<not>P"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule notI)
  apply (erule notE)
  by (rule disjI2)

(*4 marks*)
lemma "(P\<or>R)\<longleftrightarrow>(\<not>(\<not>P\<and> \<not>R))"
 apply (rule iffI) 
   apply (rule classical)
   apply (rule notI)
   apply (erule notE)
   apply (erule conjE)
   apply (rule classical)
   apply (rule notI)
   apply (erule notE)
   apply (erule conjE)
   apply (erule disjE)
    apply assumption
   apply (erule notE)
   apply assumption
  apply (rule classical)
  apply (erule notE)
  apply (rule conjI)
   apply (rule classical)
   apply (rule notI)
   apply (erule notE)
  apply (rule disjI1)
   apply assumption
  apply (rule classical)
  apply (rule notI)
  apply (erule notE)
  by (rule disjI2)

(*  apply (rule iffI) 
   apply (rule classical)
   apply (rule notI)
   apply (erule notE)
   apply (erule conjE)
   apply (rule classical)
   apply (rule notI)
   apply (erule notE)
   apply (erule conjE)
   apply (erule disjE)
    apply assumption
   apply (erule notE)
   apply assumption
  apply (rule classical)
  apply (erule notE)
  apply (rule conjI)
   apply (rule classical)
   apply (rule notI)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption
  apply (rule classical)
  apply (rule notI)
  apply (erule notE)
  by (rule disjI2) *)

(*1 mark*)
lemma "(\<forall> x . F x) \<and> (\<forall> x . G x ) \<longrightarrow> (\<forall> x . F x \<and> G x )"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (erule_tac x="x" in allE)+
  apply (rule conjI)
  by assumption  

(*1 mark*)
lemma "(\<forall> x y. R x y) \<longrightarrow> (\<forall> x . R x x )"
  apply (rule impI)
  apply (rule allI)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  by assumption
  
(*3 marks*)
lemma "(\<forall>x. P x)\<or>(\<exists>x.\<not>P x)"

  apply (rule classical)
  apply (rule disjI1)
  apply (rule allI)
  apply (rule classical)
  apply (erule notE)
  apply (rule disjI2)
  by (rule_tac x="x" in exI)

(*3 marks*)
lemma "(\<forall>x. \<not> (P x \<longrightarrow> Q x)) \<longrightarrow> \<not>(\<exists>x. \<not>P x \<and> Q x)"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule conjE)
  apply (erule notE)
  apply (erule allE)
  apply (rule classical)
  apply (erule notE)
  by (rule impI)

(*3 marks*)
lemma "\<exists>Bob. (drunk Bob \<longrightarrow> (\<forall>y. drunk y))"
  apply (rule classical)
  apply (rule_tac x="Bob" in exI)
  apply (rule impI)
  apply (rule allI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule exI)
  apply (rule impI)
  apply (rule allI)
  by (erule notE)


(*4 marks*)
lemma "\<not> (\<exists> barber . man barber \<and> (\<forall> x . man x \<and> \<not>shaves x x \<longleftrightarrow> shaves barber x ))"
  apply (rule notI)
  apply (erule exE)
  apply (erule conjE)
  apply (erule_tac x="barber" in allE)
  apply (erule iffE)
  apply (erule impE)
   apply (rule conjI)
    apply assumption
   apply (rule classical)
   apply (rule notI)
   apply (erule notE)
   apply (erule impE)
    apply assumption
   apply (erule conjE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule conjE)
  by (erule notE)

locale incidence =
  fixes incidence_points_on_sections :: "'point \<Rightarrow> 'section \<Rightarrow> bool" (infix " \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t " 80)
  fixes region_to_section :: "'region \<Rightarrow> 'section" 
  assumes section_nonempty: "\<exists>point. point \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t section"   
(*Write here your axiom stating that every section has 
                                            a point incident to it*) (*2 marks*)
  and section_uniqueness:"(\<And>p. (p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t s1 \<longleftrightarrow> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t s2)) \<Longrightarrow> s1 = s2" 
(*Write here your axiom stating that two sections are the same
                                      if the same points are incident to each*) (*2 marks*)
begin

definition isPartOf ::"'section \<Rightarrow> 'section \<Rightarrow> bool" (infix "isPartOf" 80) where 
"a isPartOf b \<equiv> (\<forall>p.(p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t a \<longrightarrow> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t b))"
(*write your formalisation of definition D1 here*) (*1 mark*)

definition inclusion ::"'region \<Rightarrow> 'section \<Rightarrow> bool"(infix "isIncludedIn" 80) where
"R isIncludedIn s \<equiv> (region_to_section R) isPartOf s"
(*write your formalisation of definition D2 here*) (*1 mark*)

definition overlaps ::"'region \<Rightarrow> 'section \<Rightarrow> bool"(infix "overlaps" 80) where
"R overlaps s \<equiv> \<exists>p. p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t (region_to_section R) \<and> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t s"
(*write your formalisation of definition D3 here*) (*1 mark*)

lemma region_overlaps_itself: "R overlaps (region_to_section R)"
proof-
  from section_nonempty
  have " \<exists>p. p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t (region_to_section R)" by blast
  hence "\<exists>p. p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t (region_to_section R) \<and> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t (region_to_section R)" by blast
  thus "R overlaps (region_to_section R)" using overlaps_def by blast
qed


  
(*Write your structured proof here*) (*2 marks*)

(*Formalise and prove that isPartOf is reflexive, transitive and antisymmetric*) (*3 marks*)
 lemma isPartOf_reflexive: "R isPartOf R"
 proof-
   from section_uniqueness
   have "\<forall>p. p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t R \<longrightarrow> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t R" by blast
   thus "R isPartOf R" using isPartOf_def by blast
 qed
(*Formalise and prove that isPartOf is reflexive here*)
 
 

lemma isPartOf_transitive:
  assumes 1:"(a isPartOf b) \<and> (b isPartOf c)" shows "a isPartOf c"
proof-
  from 1
  have "(\<forall>p1. p1 \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t a \<longrightarrow> p1 \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t b) \<and> (\<forall>p2. p2 \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t b \<longrightarrow> p2 \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t c)" using isPartOf_def by blast
  hence "\<forall>p. (p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t a \<longrightarrow> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t b) \<and> (p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t b \<longrightarrow> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t c)" by blast
  hence "\<forall>p. (\<not>(p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t a) \<or> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t b) \<and> (\<not>(p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t b) \<or> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t c)" by blast
  hence "\<forall>p. (\<not>(p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t a) \<or> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t c) \<and> (\<not>(p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t b) \<or> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t b)" by blast
  hence "\<forall>p. (\<not>(p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t a) \<or> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t c)" by blast
  hence "\<forall>p. p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t a \<longrightarrow> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t c" by blast
  thus "a isPartOf c" using isPartOf_def by blast
qed
(*Formalise and prove that isPartOf is transitive here*)


lemma isPartOf_antisymmetric:
  assumes 1:"a isPartOf b \<and> b isPartOf a" shows "a = b"
proof-
  from 1
  have "\<And>p. (p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t a \<longrightarrow> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t b) \<and> (p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t b \<longrightarrow> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t a)" using isPartOf_def by blast 
  hence "\<And>p. (\<not>(p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t a) \<or> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t b) \<and> (\<not>(p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t b) \<or> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t a)" by blast
  hence "\<And>p. (p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t a) \<longleftrightarrow> (p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t b)" by blast
  thus "a = b" using section_uniqueness by blast
qed
(*Formalise and prove that isPartOf is antisymmetric here*)

end


locale section_bundles =  incidence incidence_points_on_sections region_to_section 
  for  incidence_points_on_sections :: "'point \<Rightarrow> 'section \<Rightarrow> bool" 
  and region_to_section :: "'region \<Rightarrow> 'section" +
  fixes crossing :: "'region \<Rightarrow> 'section \<Rightarrow> bool" (infix "crosses" 80)
  and incidence_sections_on_bundles :: "'section \<Rightarrow> 'bundle \<Rightarrow> bool" (infix "\<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n" 80) 
assumes SC1: "(R crosses S \<Longrightarrow> R overlaps S)"
 (*Write your formalisation of Axiom SC1 here*) (*1 mark*)
 and SI1: "\<And>s. (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n S1 \<longleftrightarrow> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n S2) \<Longrightarrow> S1 = S2"
 (*Write your formalisation of Axiom SI1 here*)     (*1 mark*)
begin

definition atLeastAsRestrictiveAs :: "'section \<Rightarrow> 'bundle \<Rightarrow> 'section \<Rightarrow> bool" where 
"atLeastAsRestrictiveAs s1 b s2 \<equiv> s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s2 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s1 isPartOf s2"
(*Write your formalisation of atLeastAsRestrictiveAs here*) (*1 mark*)

notation 
  atLeastAsRestrictiveAs ("_ \<le>\<^sub>_ _" [80, 80, 80] 80)


(*Formalise and prove that atLeastAsRestrictiveAs is reflexive, transitive and antisymmetric*) (*2 marks*)

(*Kulik and Eschenbach say 'The relation \<ge> is reflexive, transitive and antisymmetric for a given 
sector bundle.' So, do they mean, given that the sections under consideration are in the bundle?
This is what we assume for reflexivity.*)
lemma atLeastAsRestrictiveAs_reflexive: 
  assumes 1:"s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b"  shows "s \<le>\<^sub>b s"
proof-
  from isPartOf_reflexive
  have "s isPartOf s" by blast
  hence "s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b  \<and> s isPartOf s" using 1 by blast
  thus "s \<le>\<^sub>b s" using atLeastAsRestrictiveAs_def by blast
qed

lemma atLeastAsRestrictiveAs_transitive:
  assumes 0:"s1 \<le>\<^sub>b s2 \<and> s2 \<le>\<^sub>b s3" shows "s1 \<le>\<^sub>b s3"
(*Formalise and prove that atLeastAsRestrictiveAs is transitive*)
proof-
  from 0
  have 1:"(s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s2 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s1 isPartOf s2 ) \<and> (s3 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s2 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s2 isPartOf s3)" using atLeastAsRestrictiveAs_def by blast
  hence 2: "s1 isPartOf s3" using isPartOf_transitive by blast
  hence "s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s3 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s1 isPartOf s3" using 1 2 by blast
  thus "s1 \<le>\<^sub>b s3" using atLeastAsRestrictiveAs_def by blast
qed

lemma atLeastAsRestrictiveAs_antisymmetric: 
  assumes 1:"s1 \<le>\<^sub>b s2 \<and> s2 \<le>\<^sub>b s1" shows "s1 = s2"
(*Formalise and prove that atLeastAsRestrictiveAs is antisymmetric*)
proof-
  from 1
  have "(s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s1 isPartOf s2 ) \<and> (s2 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b  \<and> s2 isPartOf s1)" using atLeastAsRestrictiveAs_def by blast
    hence "s1 isPartOf s2 \<and> s2 isPartOf s1" by blast
      thus "s1 = s2" using isPartOf_antisymmetric by blast
qed

end

locale comparison = section_bundles incidence_points_on_sections region_to_section 
 crossing incidence_sections_on_bundles
  for  incidence_points_on_sections :: "'point \<Rightarrow> 'section \<Rightarrow> bool" (infix "\<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t" 80) 
  and region_to_section :: "'region \<Rightarrow> 'section" 
  and crossing :: "'region \<Rightarrow> 'section \<Rightarrow> bool" (infix "crosses" 80) 
  and incidence_sections_on_bundles :: "'section \<Rightarrow> 'bundle \<Rightarrow> bool" (infix "\<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n" 80)+
assumes SB2: "s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s2 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<Longrightarrow> s1 \<le>\<^sub>b s2 \<or> s2 \<le>\<^sub>b s1"
(*Write your formalisation of Axiom SB2 here*) (*1 mark*)
begin

lemma T1:
  assumes 1: "R overlaps s1" shows "(s1 \<le>\<^sub>b s2 \<Longrightarrow> R overlaps s2)"
  using assms atLeastAsRestrictiveAs_def isPartOf_def overlaps_def by auto
(*Write your formalisation and proof of Theorem T1 here*) (*1 mark*)
(* proof-
  from 1
  have 2:"\<exists>p. p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t (region_to_section R) \<and> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t s1" using overlaps_def by blast
  have 3:" s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s2 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s1 isPartOf s2" using 1 atLeastAsRestrictiveAs_def by blast
  hence "(\<forall>p.(p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t s1 \<longrightarrow> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t s2))" using isPartOf_def by blast
  hence "\<exists>p. p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t (region_to_section R) \<and> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t s2" using 2 3 by blast
  thus "R overlaps s2" using overlaps_def by blast
qed *)

lemma T2:
(*Write your formalisation and proof of Theorem T2 here*) (*1 mark*)
  assumes 1:"R isIncludedIn s" "s \<le>\<^sub>b s'" shows " (s \<le>\<^sub>b s' \<Longrightarrow> R isIncludedIn s')"
  using assms(1) atLeastAsRestrictiveAs_def inclusion_def isPartOf_transitive by blast

definition isCore (infix "isCoreOf" 80) where
"s isCoreOf b = (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> (\<forall>s'. s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> s \<le>\<^sub>b s'))"

definition isHull (infix "isHullOf" 80) where
"s isHullOf b = (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> (\<forall>s'. s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> s' \<le>\<^sub>b s))"
(*Write your definition of hull here*) (*1 mark*)

end

locale crossing_sector = comparison incidence_points_on_sections 
          region_to_section crossing incidence_sections_on_bundles
          for incidence_points_on_sections :: "'point \<Rightarrow> 'section \<Rightarrow> bool" (infix "\<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t" 80) 
and region_to_section :: "'region \<Rightarrow> 'section" 
and crossing :: "'region \<Rightarrow> 'section \<Rightarrow> bool" (infix "crosses" 80)  
and incidence_sections_on_bundles :: "'section \<Rightarrow> 'bundle \<Rightarrow> bool" (infix "\<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n" 80) +
assumes SC2: "R crosses s1 \<Longrightarrow> \<forall>s2. atLeastAsRestrictiveAs s2 S s1 \<longrightarrow> R crosses s2"
(*Write your formalisation of Axiom SC2 here*) (*1 mark*)
begin


lemma overlaps_core: 
  assumes 1:"((R overlaps s) \<and> (s isCoreOf b))" shows "((s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R overlaps s'))"
proof-
  from 1
  have "((R overlaps s) \<and> (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> (s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> s \<le>\<^sub>b s')))" using isCore_def by blast
  hence "((s \<le>\<^sub>b s' \<longrightarrow> R overlaps s') \<and> (s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> s \<le>\<^sub>b s'))" using T1 by blast
  hence "((\<not>(s \<le>\<^sub>b s') \<or>  R overlaps s') \<and> (\<not>(s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b) \<or> s \<le>\<^sub>b s'))" by blast
  hence "(\<not>(s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b) \<or> R overlaps s') \<and> (\<not>(s \<le>\<^sub>b s') \<or> s \<le>\<^sub>b s')" by blast
  thus "(s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R overlaps s')" by blast
qed
(*Write your formalisation and structured proof of the remark `If a region 
overlaps the core of a section bundle then it overlaps every section of the section bundle'*) 
(*4 marks*)

lemma crosses_hull: 
  assumes 1:"R crosses s \<and> s isHullOf b" shows "((s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R overlaps s'))"
proof-
  from 1
  have "((s' \<le>\<^sub>b s \<longrightarrow> R crosses s')) \<and> s isHullOf b" using SC2 by blast
  hence "((s' \<le>\<^sub>b s \<longrightarrow> R crosses s')) \<and> (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> (s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> s' \<le>\<^sub>b s))" using isHull_def by blast
  hence "(\<not>(s' \<le>\<^sub>b s) \<or> R crosses s') \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> (\<not>(s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b) \<or>  s' \<le>\<^sub>b s)" by blast
  hence "(\<not>(s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b) \<or> R crosses s') \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> (\<not>(s' \<le>\<^sub>b s) \<or> s' \<le>\<^sub>b s)" by blast
  thus "(s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b) \<longrightarrow> R overlaps s'" using SC1 by blast
qed
(*Write your formalisation and structured proof of the remark `If a region 
crosses the hull of a section bundle then it crosses every sector of the section bundle'*) 
(*4 marks*)

lemma not_overlap_hull:  
  assumes 1: "\<not>R overlaps s \<and> s isHullOf b" shows "s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> \<not>R overlaps s'"
proof-
  from 1
  have "\<not>R overlaps s \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> (s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> s' \<le>\<^sub>b s)" using isHull_def by blast
  hence "\<not>R overlaps s \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> (\<not>(s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b) \<or> s' \<le>\<^sub>b s)" by blast
  hence "\<not>R overlaps s \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> \<not>(s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b) \<or> \<not>R overlaps s \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s' \<le>\<^sub>b s" by blast
  hence "\<not>(R overlaps s \<or> \<not>s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<or> (s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b)) \<or> \<not>R overlaps s \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s' \<le>\<^sub>b s" by blast
  hence "(R overlaps s \<or> \<not>s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<or> (s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b)) \<longrightarrow> \<not>R overlaps s \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s' \<le>\<^sub>b s" by blast
  hence "s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> \<not>R overlaps s \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s' \<le>\<^sub>b s" by blast
  hence "s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> \<not>R overlaps s' \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s' \<le>\<^sub>b s" using T1 by blast
  thus "s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> \<not>R overlaps s'" by blast
qed
(*Write your formalisation and structured proof of the remark `If a region 
does not overlap the hull of a section bundle, it does not overlap any of its sections'*) 
(*4 marks*)

definition overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  where 
"overlapsAsMuchAs R b R' == (\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R' overlaps s \<longrightarrow> R overlaps s)"

notation 
  overlapsAsMuchAs ("_ \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)

definition eq_overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  where 
"eq_overlapsAsMuchAs R b R' == R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<and> R' \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R"

notation 
  eq_overlapsAsMuchAs ("_ \<cong>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)

abbreviation
rev_overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  ("_ \<le>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)
where"rev_overlapsAsMuchAs R b R' == overlapsAsMuchAs R' b R"

definition more_overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  where 
"more_overlapsAsMuchAs R b R' == R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<and> \<not>(R' \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R)"

notation 
  more_overlapsAsMuchAs ("_ >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)

abbreviation
less_overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  ("_ <\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)
where"less_overlapsAsMuchAs R b R' == more_overlapsAsMuchAs R' b R"

(*Formalise and prove that overlapsAsMuchAs is reflexive and transitive*) (*2 marks*)

lemma overlapsAsMuchAs_reflexive:"R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R"
  by (simp add: overlapsAsMuchAs_def)
(*Write your formalisation and proof that overlapsAsMuchAs is reflexive here*) 

lemma overlapsAsMuchAs_transitive:"A \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b B \<and> B \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b C \<Longrightarrow> A \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b C"
  by (simp add: overlapsAsMuchAs_def)
(*Write your formalisation and proof that overlapsAsMuchAs is transitive here*)

lemma T3: "(R >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R') = (\<exists>s. (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> R overlaps s \<and> \<not>(R' overlaps s)))"
 proof- 
   { assume 1:"(\<exists>s. (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> R overlaps s \<and> \<not>(R' overlaps s)))"
  from 1
  have "\<forall>s'.\<exists>s.(s \<le>\<^sub>b s' \<or> s' \<le>\<^sub>b s \<or> \<not> s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b) \<and> R overlaps s \<and> \<not>(R' overlaps s) \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b" using SB2 by blast
  hence "\<forall>s'.\<exists>s.(R overlaps s' \<or> \<not>(R' overlaps s') \<or> \<not> s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b) \<and> R overlaps s \<and> \<not>(R' overlaps s) \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b" using T1 by blast
  hence "\<forall>s'.\<exists>s.(R' overlaps s'\<longrightarrow> R overlaps s' \<or> \<not> s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b) \<and> R overlaps s \<and> \<not>(R' overlaps s) \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b" by blast
  hence "\<forall>s'.\<exists>s.(s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R' overlaps s'\<longrightarrow> R overlaps s') \<and> R overlaps s \<and> \<not>(R' overlaps s) \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b" by blast
  hence "\<exists>s. (R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<and> R overlaps s \<and> \<not>(R' overlaps s) \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b)" using overlapsAsMuchAs_def by blast
  hence "\<exists>s. \<not>(\<not>R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<or> \<not>R overlaps s \<or> R' overlaps s \<or> \<not>s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b)" by blast
  hence "\<exists>s. \<not>(\<not>R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<or> (R overlaps s \<longrightarrow> R' overlaps s) \<or> \<not>s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b)" by blast
  hence "\<exists>s. \<not>(\<not>R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<or> (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R overlaps s \<longrightarrow> R' overlaps s))" by blast
  hence "\<exists>s. R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<and> \<not>(s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R overlaps s \<longrightarrow> R' overlaps s)" by blast
  hence "R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<and> \<not>R' \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R" using overlapsAsMuchAs_def by blast
  hence f1:"R >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R'" using more_overlapsAsMuchAs_def by blast}

  moreover
  {assume 2: "R >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R'"
  from 2
  have "R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<and> \<not>(R' \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R)" using more_overlapsAsMuchAs_def by blast
  hence "(\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R' overlaps s \<longrightarrow> R overlaps s) \<and> \<not>(\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R overlaps s \<longrightarrow> R' overlaps s)" using overlapsAsMuchAs_def by blast
  hence "(\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> \<not> R' overlaps s \<or> R overlaps s) \<and> \<not>(\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> \<not> R overlaps s \<or>  R' overlaps s)" by blast
  hence "(\<forall>s. \<not> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<or> \<not> R' overlaps s \<or> R overlaps s) \<and> \<not>(\<forall>s. \<not> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<or> \<not> R overlaps s \<or> R' overlaps s)" by blast
  hence "(\<forall>s. \<not> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<or> \<not> R' overlaps s \<or> R overlaps s) \<and> (\<exists>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> R overlaps s \<and> \<not> R' overlaps s)" by blast
  hence "\<exists>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> R overlaps s \<and> \<not> R' overlaps s" by blast
  hence f2:"(\<exists>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> R overlaps s \<and> \<not> R' overlaps s)"  by blast}

  ultimately
  have  "(R >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R') = (\<exists>s. (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> R overlaps s \<and> \<not>(R' overlaps s)))" by blast
  thus "(R >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R') = (\<exists>s. (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> R overlaps s \<and> \<not>(R' overlaps s)))" by blast 

qed

(* "overlapsAsMuchAs R b R' == (\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R' overlaps s \<longrightarrow> R overlaps s)" *)
(* assumes SB2: "s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s2 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<Longrightarrow> s1 \<le>\<^sub>b s2 \<or> s2 \<le>\<^sub>b s1" *)
(*   assumes 1:"R overlaps s1" shows "(s1 \<le>\<^sub>b s2 \<Longrightarrow> R overlaps s2)"  *)

  (* by (smt T1 comparison.SB2 comparison_axioms more_overlapsAsMuchAs_def overlapsAsMuchAs_def) *)
(*Write your formalisation and structured proof of Theorem T3 here. You must attempt to 
formalise Kulik et al.'s reasoning*) (*11 marks*)

(*In under 200 words, compare and contrast the mechanical proof that you produced with the 
pen-and-paper proof by Kulik et al.\. In particular, indicate any reasoning, proof parts, and/or 
useful lemmas that you had to make explicit during the mechanisation but may have been glossed over
 or assumed by the pen-and-paper proof. Also highlight any inaccuracies in their language or 
notation. Note any parts where you had to diverge from their reasoning, and why.
Write your answer in a comment here.*) (*4 marks*)

lemma T4: "R >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<or> R \<cong>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<or> R <\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R'"
  using T3 eq_overlapsAsMuchAs_def overlapsAsMuchAs_def by auto
(*Write your formalisation and proof of Theorem T4 here*) (*1 mark*)

lemma T5: "R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<or> R \<le>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R'"
(*  using T4 eq_overlapsAsMuchAs_def more_overlapsAsMuchAs_def by auto *)
proof-
  from T4
  have "(R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<and> \<not>(R' \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R)) \<or> R \<cong>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<or> (R' \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R \<and> \<not>(R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R'))" using more_overlapsAsMuchAs_def by blast
  hence "(R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<and> \<not>(R' \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R)) \<or> (R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<and> R' \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R) \<or> (R' \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R \<and> \<not>(R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R'))" using eq_overlapsAsMuchAs_def by blast
  thus "(R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<or> R' \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R)" by blast
qed
 (*Write your formalisation and structured proof of Theorem T5 here. 
You must show it follows from T4*) (*3 marks*)

(********************Challenge problem****************************************)

(* definition isCore (infix "isCoreOf" 80) where
"s isCoreOf b = (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> (\<forall>s'. s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> s \<le>\<^sub>b s'))" *)

definition crosses_isIncludedIn :: "'region \<Rightarrow>'section \<Rightarrow> bool" where
"crosses_isIncludedIn R s = (R crosses s \<or> region_to_section R isPartOf s)"


(*Write your definition of the relation ci here.
Kulik et al. say `If a region crosses or is included in a section we write ci'.*) (*2 marks*)

definition crosses_isIncludedInAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  where 
"crosses_isIncludedInAsMuchAs R b R' = (\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R' crosses s \<longrightarrow> R crosses s)"
(*Write your definition of `crosses or is included in as much
as' here*) (*2 marks*)

notation 
  crosses_isIncludedInAsMuchAs ("_ \<ge>\<^sub>c\<^sub>i \<^sub>_ _" [80, 80, 80] 80)

definition belongsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool" where
"belongsAsMuchAs R b R' = (R \<ge>\<^sub>c\<^sub>i \<^sub>b R' \<or> R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R')"
(*Write your definition of `belongs as much as here: definition D8 in
the paper.*) (*2 marks*)

notation 
  belongsAsMuchAs ("_ \<ge> \<^sub>_ _" [80, 80, 80] 80)

(*Formalise and write structured proofs of Theorems T6-T8 for both crossesIncludedInAsMuchAs and
belongsAsMuchAs*) (*14 marks*)

lemma T6_crosses_isIncludedInAsMuchAs: 
  assumes 1:"\<not> R overlaps s \<and> s isHullOf b" shows "(R' \<ge>\<^sub>c\<^sub>i \<^sub>b R)"
  using SC1 assms crosses_isIncludedInAsMuchAs_def not_overlap_hull by blast
(* proof-
  from 1

qed *)
(* lemma not_overlap_hull:  
  assumes 1: "\<not>R overlaps s \<and> s isHullOf b" shows "s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> \<not>R overlaps s'"

"crosses_isIncludedInAsMuchAs R b R' = (\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R' crosses s \<longrightarrow> R crosses s)"

assumes SC1: "(R crosses S \<Longrightarrow> R overlaps S)" 

"R overlaps s \<equiv> \<exists>p. p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t (region_to_section R) \<and> p \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t s" 

"s isHullOf b = (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> (\<forall>s'. s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> s' \<le>\<^sub>b s))" 

"overlapsAsMuchAs R b R' == (\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R' overlaps s \<longrightarrow> R overlaps s)" *)

(*  using SC1 crosses_isIncludedInAsMuchAs_def not_overlap_hull by blast *)

lemma T6_belongsAsMuchAs: 
  assumes 1:"\<not> R overlaps s \<and> s isHullOf b" shows "\<forall>R'.(R' \<ge> \<^sub>b R)"
proof-
  from 1
  have "\<forall>R'.(R' \<ge>\<^sub>c\<^sub>i \<^sub>b R) \<or> \<not>(s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R crosses s \<longrightarrow> R' crosses s) \<and> s isHullOf b" using T6_crosses_isIncludedInAsMuchAs crosses_isIncludedInAsMuchAs_def by blast
  hence "\<forall>R'.(R' \<ge>\<^sub>c\<^sub>i \<^sub>b R) \<or> \<not>(s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> (\<not>R crosses s \<or> R' crosses s)) \<and> s isHullOf b" by blast
  hence "\<forall>R'.(R' \<ge>\<^sub>c\<^sub>i \<^sub>b R) \<or> \<not>(\<not>s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<or> \<not>R crosses s \<or> R' crosses s) \<and> s isHullOf b" by blast
  hence "\<forall>R'.(R' \<ge>\<^sub>c\<^sub>i \<^sub>b R) \<or> (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> R crosses s \<and> \<not>R' crosses s) \<and> s isHullOf b" by blast
  hence "\<forall>R'.(R' \<ge>\<^sub>c\<^sub>i \<^sub>b R) \<or> (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> R overlaps s \<and> \<not>R' crosses s) \<and> s isHullOf b" using SC1 by blast
  hence "\<forall>R'.(R' \<ge>\<^sub>c\<^sub>i \<^sub>b R) \<or> (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> R overlaps s \<and> \<not>R' crosses s \<and> (s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> s' \<le>\<^sub>b s))" using isHull_def by blast
  hence "\<forall>R'.(R' \<ge>\<^sub>c\<^sub>i \<^sub>b R) \<or> (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> R overlaps s \<and> \<not>R' crosses s \<and> (\<not>s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<or> (s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s' isPartOf s)))" using atLeastAsRestrictiveAs_def by blast
qed

(*  using T6_crosses_isIncludedInAsMuchAs assms belongsAsMuchAs_def by blast 

"crosses_isIncludedInAsMuchAs R b R' = (\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R' crosses s \<longrightarrow> R crosses s)"

assumes SC1: "(R crosses S \<Longrightarrow> R overlaps S)" 

lemma T6_crosses_isIncludedInAsMuchAs: 
  assumes 1:"\<not> R overlaps s \<and> s isHullOf b" shows "\<forall>R'.(R' \<ge>\<^sub>c\<^sub>i \<^sub>b R)" 

"overlapsAsMuchAs R b R' == (\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R' overlaps s \<longrightarrow> R overlaps s)"

"belongsAsMuchAs R b R' = (R \<ge>\<^sub>c\<^sub>i \<^sub>b R' \<or> R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R')" *)

lemma T7_crosses_isIncludedInAsMuchAs: "R isIncludedIn s \<and> s isCoreOf b \<Longrightarrow> \<forall>R'.(R \<ge>\<^sub>c\<^sub>i \<^sub>b R')"
  sorry

lemma T7_belongsAsMuchAs: "R isIncludedIn s \<and> s isCoreOf b \<Longrightarrow> \<forall>R'.(R \<ge> \<^sub>b R')"
  by (meson T1 belongsAsMuchAs_def inclusion_def isCore_def isPartOf_def overlapsAsMuchAs_def overlaps_def region_overlaps_itself)

lemma T8_crosses_isIncludedInAsMuchAs: "R crosses s \<and> s isHullOf b \<Longrightarrow> \<forall>R'.(R \<ge>\<^sub>c\<^sub>i \<^sub>b R')"
  using SC2 crosses_isIncludedInAsMuchAs_def isHull_def by blast

lemma T8_belongsAsMuchAs: "R crosses s \<and> s isHullOf b \<Longrightarrow> \<forall>R'.(R \<ge> \<^sub>b R')"
  by (simp add: T8_crosses_isIncludedInAsMuchAs belongsAsMuchAs_def)

end

end