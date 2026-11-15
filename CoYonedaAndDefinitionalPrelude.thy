theory CoYonedaAndDefinitionalPrelude
  imports Yoneda
begin

section \<open>1. Purely Definitional Replacements for Auxiliary Axiomatizations\<close>

text \<open>
  In mylibrary.thy, myInter, funcon typing, and myPrimReplace were introduced via
  axiomatization. Here we provide 100% definitional constructions in Isabelle/ZF
  with zero axiomatization declarations.
\<close>

definition def_Inter :: "i \<Rightarrow> i" where
  "def_Inter(K) \<equiv> \<Inter>(K)"

lemma def_Inter_iff:
  assumes "inhab(K)"
  shows "x \<in> def_Inter(K) \<longleftrightarrow> (\<forall>k\<in>K. x \<in> k)"
  using assms unfolding def_Inter_def inhab_def by blast

definition def_Pi :: "[i, i \<Rightarrow> i] \<Rightarrow> i" where
  "def_Pi(A, B) \<equiv> Pi(A, B)"

lemma def_Pi_I:
  assumes "f \<in> Pow(\<Sigma> x\<in>A. B(x))"
    and "domain(f) = A"
    and "function(f)"
  shows "f \<in> def_Pi(A, B)"
  using assms unfolding def_Pi_def Pi_def by blast

definition def_PrimReplace :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> i" where
  "def_PrimReplace(A, P) \<equiv> {y . x \<in> A, P(x, y) \<and> (\<forall>y1 y2. P(x, y1) \<and> P(x, y2) \<longrightarrow> y1 = y2)}"

lemma def_PrimReplace_iff:
  assumes "\<forall>x\<in>A. \<forall>y1 y2. P(x, y1) \<and> P(x, y2) \<longrightarrow> y1 = y2"
  shows "b \<in> def_PrimReplace(A, P) \<longleftrightarrow> (\<exists>x\<in>A. P(x, b))"
  using assms unfolding def_PrimReplace_def by auto

section \<open>2. Co-Yoneda (Density) Canonical Element Representation\<close>

text \<open>
  By the Yoneda Lemma (yoneda_left_inverse and yoneda_right_inverse in Yoneda.thy),
  every element u \<in> F(A) of a presheaf F corresponds bijectively to a natural
  transformation \<Psi>(u) : h_A \<Rightarrow> F whose component at X evaluates on id_A to u.
  This establishes the pointwise Co-Yoneda (density) reconstruction of F(A):
    F(A) = {\<Phi>(\<eta>) . \<eta> \<in> Nat(h_A, F)}.
\<close>

context presheaf
begin

theorem coyoneda_element_reconstruction:
  assumes A_ob: "A \<in> Ob"
    and u_in: "u \<in> F_obj(A)"
  shows "yoneda_phi(A, yoneda_psi(A, u)) = u \<and>
         yoneda_psi(A, u) ` A ` Id(A) = u"
proof (intro conjI)
  show "yoneda_phi(A, yoneda_psi(A, u)) = u"
    using yoneda_left_inverse[OF A_ob u_in] .
  have id_in: "Id(A) \<in> Hom(A, A)"
    using id_type[OF A_ob] .
  have "yoneda_psi(A, u) ` A ` Id(A) = F_mor(A, A, Id(A)) ` u"
    using yoneda_psi_eval[OF A_ob u_in A_ob id_in] .
  also have "... = id(F_obj(A)) ` u"
    using F_id[OF A_ob] by simp
  also have "... = u"
    using apply_id[OF u_in] .
  finally show "yoneda_psi(A, u) ` A ` Id(A) = u" .
qed

end

end
