theory Lab1
imports Main
begin
lemma I: "A \<longrightarrow> A"

  apply (rule impI)
  apply assumption
  done

lemma "A \<and> B \<longrightarrow> B \<and> A"

  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
  apply assumption
  done

lemma " (A \<and> B) \<longrightarrow> (A \<or> B)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule disjI2)
  apply assumption
  done

lemma "((A \<or> B) \<or> C) \<longrightarrow> A \<or> (B \<or> C)"
  apply (rule impI)
  apply (erule disjE)
  done

end