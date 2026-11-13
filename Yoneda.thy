theory Yoneda imports mylibrary
begin

(*
  Formalization of Category Theory, Presheaves, Natural Transformations,
  and the Yoneda Lemma in Isabelle/ZF.
*)

(* Transitive universe structure *)
definition Tr :: "i \<Rightarrow> o"
  where Tr_def : "Tr(x) == \<forall>y\<in>x. y\<subseteq>x"

axiomatization U0 :: "i"
  where Un1: "Tr(U0)"

(* Equality types *)
definition eqtype :: \<open>[i,i] \<Rightarrow> i\<close>
  where "eqtype(x,y) == {_\<in>{0}. x=y}"

definition eqtyperefl :: \<open>i \<Rightarrow> i\<close>
  where "eqtyperefl(U) == \<Prod>x\<in>U. eqtype(x,x)"

lemma q1 : "0 \<in> eqtype(x,x)"
proof(unfold eqtype_def)
  show \<open>0 \<in> {_ \<in> {0} . x = x}\<close>
  proof
    show \<open>0 \<in> {0}\<close> by auto
    show \<open>x = x\<close> by auto
  qed
qed

lemma q2 : \<open>(\<lambda>x\<in>U. 0) \<in> eqtyperefl(U)\<close>
proof(unfold eqtyperefl_def)
  show \<open>(\<lambda>x\<in>U. 0) \<in> (\<Prod>x\<in>U. eqtype(x, x))\<close>
  proof(rule func.lam_type)
    fix x
    assume H1:\<open>x\<in>U\<close>
    show \<open>0 \<in> eqtype(x, x)\<close>
      by (rule q1)
  qed
qed

(* Category Locale: objects, hom-sets, composition, and identity *)
locale catloc = 
  fixes U :: "i"
  fixes C :: "i"
  fixes Hom :: "i"
  assumes homfun : \<open>Hom : C\<times>C \<rightarrow> U\<close>
  fixes compo :: "i"
  assumes compodef: \<open>compo : (\<Prod>X\<in>C. \<Prod>Y\<in>C. \<Prod>Z\<in>C.
 (Hom ` <X,Y> \<times> Hom ` <Y,Z> \<rightarrow> Hom ` <X,Z>))\<close>
  fixes id :: "i"
  assumes idinhom: \<open>id : (\<Prod>A\<in>C.  (Hom ` <A,A>))\<close>

context catloc
begin

lemma l1: \<open>domain(id) = C\<close>
  by (rule func.domain_of_fun, rule idinhom)

end

(* Fully axiomatic category with associativity and identity laws *)
locale category = catloc +
  assumes comp_assoc:
    "\<lbrakk>X \<in> C; Y \<in> C; Z \<in> C; W \<in> C;
      f \<in> Hom ` <X,Y>; g \<in> Hom ` <Y,Z>; h \<in> Hom ` <Z,W>\<rbrakk> \<Longrightarrow>
     compo ` X ` Z ` W ` <compo ` X ` Y ` Z ` <f, g>, h> =
     compo ` X ` Y ` W ` <f, compo ` Y ` Z ` W ` <g, h>>"
  assumes comp_id_left:
    "\<lbrakk>X \<in> C; Y \<in> C; f \<in> Hom ` <X,Y>\<rbrakk> \<Longrightarrow>
     compo ` X ` X ` Y ` <id ` X, f> = f"
  assumes comp_id_right:
    "\<lbrakk>X \<in> C; Y \<in> C; f \<in> Hom ` <X,Y>\<rbrakk> \<Longrightarrow>
     compo ` X ` Y ` Y ` <f, id ` Y> = f"

(* Opposite Category Abstraction *)
definition op_Hom :: "[i, i] \<Rightarrow> i"
  where "op_Hom(C, Hom) \<equiv> \<lambda>p\<in>(C\<times>C). Hom ` <snd(p), fst(p)>"

definition op_compo :: "[i, i] \<Rightarrow> i"
  where "op_compo(C, compo) \<equiv>
    \<lambda>X\<in>C. \<lambda>Y\<in>C. \<lambda>Z\<in>C. \<lambda>p\<in>(Hom ` <Y,X> \<times> Hom ` <Z,Y>).
      compo ` Z ` Y ` X ` <snd(p), fst(p)>"

(* Presheaf Functor Locale (Contravariant Functor C^op to Set) *)
locale presheaf = category +
  fixes P_obj :: "i \<Rightarrow> i"
  fixes P_mor :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
  assumes P_mor_type:
    "\<lbrakk>X \<in> C; Y \<in> C; f \<in> Hom ` <X,Y>\<rbrakk> \<Longrightarrow> P_mor(X,Y,f) : P_obj(Y) \<rightarrow> P_obj(X)"
  assumes P_mor_id:
    "\<lbrakk>X \<in> C; u \<in> P_obj(X)\<rbrakk> \<Longrightarrow> P_mor(X,X, id ` X) ` u = u"
  assumes P_mor_comp:
    "\<lbrakk>X \<in> C; Y \<in> C; Z \<in> C; f \<in> Hom ` <X,Y>; g \<in> Hom ` <Y,Z>; u \<in> P_obj(Z)\<rbrakk> \<Longrightarrow>
     P_mor(X,Z, compo ` X ` Y ` Z ` <f, g>) ` u = P_mor(X,Y,f) ` (P_mor(Y,Z,g) ` u)"

(* Representable Presheaf (Hom-functor h_A = Hom(-, A)) *)
definition h_obj :: "[i, i, i] \<Rightarrow> i"
  where "h_obj(Hom, A, X) \<equiv> Hom ` <X, A>"

definition h_mor :: "[i, i, i, i, i, i] \<Rightarrow> i"
  where "h_mor(Hom, compo, A, X, Y, f) \<equiv>
    \<lambda>g \<in> Hom ` <Y,A>. compo ` X ` Y ` A ` <f, g>"

lemma h_mor_eval:
  assumes "g \<in> Hom ` <Y,A>"
  shows "h_mor(Hom, compo, A, X, Y, f) ` g = compo ` X ` Y ` A ` <f, g>"
proof (unfold h_mor_def)
  from assms show "(\<lambda>g \<in> Hom ` <Y,A>. compo ` X ` Y ` A ` <f, g>) ` g = compo ` X ` Y ` A ` <f, g>"
    by (rule func.beta)
qed

(* Natural Transformation Locale between Presheaves *)
locale natural_transformation =
  fixes C :: "i"
  fixes Hom :: "i"
  fixes compo :: "i"
  fixes id :: "i"
  fixes P_obj :: "i \<Rightarrow> i"
  fixes P_mor :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
  fixes Q_obj :: "i \<Rightarrow> i"
  fixes Q_mor :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
  fixes alpha :: "i \<Rightarrow> i"
  assumes alpha_type: "\<And>X. X \<in> C \<Longrightarrow> alpha(X) : P_obj(X) \<rightarrow> Q_obj(X)"
  assumes naturality_square:
    "\<lbrakk>X \<in> C; Y \<in> C; f \<in> Hom ` <X,Y>; u \<in> P_obj(Y)\<rbrakk> \<Longrightarrow>
     alpha(X) ` (P_mor(X,Y,f) ` u) = Q_mor(X,Y,f) ` (alpha(Y) ` u)"

(* Yoneda Map: Natural Transformations to Presheaf Evaluation *)
definition yoneda_phi :: "[i, (i \<Rightarrow> i), i] \<Rightarrow> i"
  where "yoneda_phi(A, alpha, id) \<equiv> alpha(A) ` (id ` A)"

(* Yoneda Extension: Presheaf Element to Natural Transformation *)
definition yoneda_psi :: "[i, (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i), i, i, i] \<Rightarrow> i"
  where "yoneda_psi(A, P_mor, u, Hom, X) \<equiv>
    \<lambda>f \<in> Hom ` <X,A>. P_mor(X,A,f) ` u"

lemma yoneda_psi_eval:
  assumes "f \<in> Hom ` <X,A>"
  shows "yoneda_psi(A, P_mor, u, Hom, X) ` f = P_mor(X,A,f) ` u"
proof (unfold yoneda_psi_def)
  from assms show "(\<lambda>f \<in> Hom ` <X,A>. P_mor(X,A,f) ` u) ` f = P_mor(X,A,f) ` u"
    by (rule func.beta)
qed

(* Yoneda Extension Naturality Square Verification *)
theorem yoneda_psi_naturality:
  assumes h_cat: "category(U, C, Hom, compo, id)"
      and h_psh: "presheaf(U, C, Hom, compo, id, P_obj, P_mor)"
      and h_A: "A \<in> C"
      and h_u: "u \<in> P_obj(A)"
      and h_X: "X \<in> C" and h_Y: "Y \<in> C"
      and h_f: "f \<in> Hom ` <X,Y>"
      and h_g: "g \<in> Hom ` <Y,A>"
  shows "(yoneda_psi(A, P_mor, u, Hom, X)) ` (h_mor(Hom, compo, A, X, Y, f) ` g) =
         P_mor(X,Y,f) ` ((yoneda_psi(A, P_mor, u, Hom, Y)) ` g)"
proof -
  have comp_g: "compo ` X ` Y ` A ` <f, g> \<in> Hom ` <X,A>"
  proof -
    from h_cat interpret category U C Hom compo id by auto
    from compodef have "compo ` X ` Y ` A \<in> Hom ` <X,Y> \<times> Hom ` <Y,A> \<rightarrow> Hom ` <X,A>"
      using h_X h_Y h_A by auto
    then show ?thesis using h_f h_g by auto
  qed
  have step1: "h_mor(Hom, compo, A, X, Y, f) ` g = compo ` X ` Y ` A ` <f, g>"
    using h_g by (rule h_mor_eval)
  have step2: "yoneda_psi(A, P_mor, u, Hom, X) ` (compo ` X ` Y ` A ` <f, g>) =
               P_mor(X,A, compo ` X ` Y ` A ` <f, g>) ` u"
    using comp_g by (rule yoneda_psi_eval)
  have step3: "P_mor(X,A, compo ` X ` Y ` A ` <f, g>) ` u =
               P_mor(X,Y,f) ` (P_mor(Y,A,g) ` u)"
  proof -
    from h_psh interpret presheaf U C Hom compo id P_obj P_mor by auto
    show ?thesis using h_X h_Y h_A h_f h_g h_u by (rule P_mor_comp)
  qed
  have step4: "yoneda_psi(A, P_mor, u, Hom, Y) ` g = P_mor(Y,A,g) ` u"
    using h_g by (rule yoneda_psi_eval)
  from step1 step2 step3 step4
  show ?thesis by auto
qed

(* Yoneda Lemma Bijection: Left Inverse Roundtrip *)
theorem yoneda_left_inverse:
  assumes h_cat: "category(U, C, Hom, compo, id)"
      and h_psh: "presheaf(U, C, Hom, compo, id, P_obj, P_mor)"
      and h_A: "A \<in> C"
      and h_u: "u \<in> P_obj(A)"
  shows "yoneda_phi(A, yoneda_psi(A, P_mor, u, Hom), id) = u"
proof -
  from h_cat interpret category U C Hom compo id by auto
  from h_psh interpret presheaf U C Hom compo id P_obj P_mor by auto
  have id_in: "id ` A \<in> Hom ` <A,A>"
    using idinhom h_A by auto
  have phi_eval: "yoneda_phi(A, yoneda_psi(A, P_mor, u, Hom), id) =
                  yoneda_psi(A, P_mor, u, Hom, A) ` (id ` A)"
    by (unfold yoneda_phi_def, auto)
  have psi_eval: "yoneda_psi(A, P_mor, u, Hom, A) ` (id ` A) = P_mor(A,A, id ` A) ` u"
    using id_in by (rule yoneda_psi_eval)
  have id_act: "P_mor(A,A, id ` A) ` u = u"
    using h_A h_u by (rule P_mor_id)
  from phi_eval psi_eval id_act show ?thesis by auto
qed

(* Yoneda Lemma Bijection: Right Inverse Roundtrip *)
theorem yoneda_right_inverse:
  assumes h_cat: "category(U, C, Hom, compo, id)"
      and h_psh: "presheaf(U, C, Hom, compo, id, P_obj, P_mor)"
      and h_A: "A \<in> C"
      and h_nat: "natural_transformation(C, Hom, compo, id,
                    (\<lambda>X. Hom ` <X,A>),
                    (\<lambda>X Y f. h_mor(Hom, compo, A, X, Y, f)),
                    P_obj, P_mor, alpha)"
      and h_X: "X \<in> C"
      and h_f: "f \<in> Hom ` <X,A>"
  shows "(yoneda_psi(A, P_mor, yoneda_phi(A, alpha, id), Hom, X)) ` f = alpha(X) ` f"
proof -
  from h_cat interpret category U C Hom compo id by auto
  from h_nat interpret natural_transformation C Hom compo id
                    "(\<lambda>X. Hom ` <X,A>)"
                    "(\<lambda>X Y f. h_mor(Hom, compo, A, X, Y, f))"
                    P_obj P_mor alpha by auto
  have id_in: "id ` A \<in> Hom ` <A,A>"
    using idinhom h_A by auto
  have phi_def: "yoneda_phi(A, alpha, id) = alpha(A) ` (id ` A)"
    by (unfold yoneda_phi_def, auto)
  have psi_eval: "(yoneda_psi(A, P_mor, yoneda_phi(A, alpha, id), Hom, X)) ` f =
                  P_mor(X, A, f) ` (alpha(A) ` (id ` A))"
    using h_f by (unfold phi_def, rule yoneda_psi_eval)
  have nat_square: "alpha(X) ` (h_mor(Hom, compo, A, X, A, f) ` (id ` A)) =
                    P_mor(X, A, f) ` (alpha(A) ` (id ` A))"
    using h_X h_A h_f id_in by (rule naturality_square)
  have h_mor_id: "h_mor(Hom, compo, A, X, A, f) ` (id ` A) = compo ` X ` A ` A ` <f, id ` A>"
    using id_in by (rule h_mor_eval)
  have comp_id: "compo ` X ` A ` A ` <f, id ` A> = f"
    using h_X h_A h_f by (rule comp_id_right)
  from h_mor_id comp_id have h_red: "h_mor(Hom, compo, A, X, A, f) ` (id ` A) = f"
    by auto
  from nat_square h_red have "alpha(X) ` f = P_mor(X, A, f) ` (alpha(A) ` (id ` A))"
    by auto
  with psi_eval show ?thesis by auto
qed

(* Yoneda Embedding Functor on Morphisms *)
definition yoneda_embed_mor :: "[i, i, i, i, i, i] \<Rightarrow> i"
  where "yoneda_embed_mor(Hom, compo, A, B, f, X) \<equiv>
    \<lambda>g \<in> Hom ` <X,A>. compo ` X ` A ` B ` <g, f>"

lemma yoneda_embed_mor_eval:
  assumes "g \<in> Hom ` <X,A>"
  shows "yoneda_embed_mor(Hom, compo, A, B, f, X) ` g = compo ` X ` A ` B ` <g, f>"
proof (unfold yoneda_embed_mor_def)
  from assms show "(\<lambda>g \<in> Hom ` <X,A>. compo ` X ` A ` B ` <g, f>) ` g = compo ` X ` A ` B ` <g, f>"
    by (rule func.beta)
qed

(* Faithfulness of the Yoneda Embedding: Injectivity on Hom-sets *)
theorem yoneda_embedding_faithful:
  assumes h_cat: "category(U, C, Hom, compo, id)"
      and h_A: "A \<in> C" and h_B: "B \<in> C"
      and h_f: "f \<in> Hom ` <A,B>"
      and h_f': "f' \<in> Hom ` <A,B>"
      and h_eq: "\<forall>X\<in>C. yoneda_embed_mor(Hom, compo, A, B, f, X) =
                        yoneda_embed_mor(Hom, compo, A, B, f', X)"
  shows "f = f'"
proof -
  from h_cat interpret category U C Hom compo id by auto
  have id_A: "id ` A \<in> Hom ` <A,A>"
    using idinhom h_A by auto
  from h_eq h_A have "yoneda_embed_mor(Hom, compo, A, B, f, A) =
                      yoneda_embed_mor(Hom, compo, A, B, f', A)"
    by auto
  then have "yoneda_embed_mor(Hom, compo, A, B, f, A) ` (id ` A) =
             yoneda_embed_mor(Hom, compo, A, B, f', A) ` (id ` A)"
    by auto
  then have "compo ` A ` A ` B ` <id ` A, f> = compo ` A ` A ` B ` <id ` A, f'>"
    using id_A by (simp only: yoneda_embed_mor_eval)
  then show "f = f'"
    using h_A h_B h_f h_f' comp_id_left by auto
qed

(* Fullness of the Yoneda Embedding: Surjectivity on Natural Transformations *)
theorem yoneda_embedding_full:
  assumes h_cat: "category(U, C, Hom, compo, id)"
      and h_A: "A \<in> C" and h_B: "B \<in> C"
      and h_nat: "natural_transformation(C, Hom, compo, id,
                    (\<lambda>X. Hom ` <X,A>),
                    (\<lambda>X Y f. h_mor(Hom, compo, A, X, Y, f)),
                    (\<lambda>X. Hom ` <X,B>),
                    (\<lambda>X Y f. h_mor(Hom, compo, B, X, Y, f)),
                    alpha)"
  obtains f where "f \<in> Hom ` <A,B>"
              and "\<forall>X\<in>C. \<forall>g \<in> Hom ` <X,A>. alpha(X) ` g = compo ` X ` A ` B ` <g, f>"
proof -
  from h_cat interpret category U C Hom compo id by auto
  from h_nat interpret natural_transformation C Hom compo id
                    "(\<lambda>X. Hom ` <X,A>)"
                    "(\<lambda>X Y f. h_mor(Hom, compo, A, X, Y, f))"
                    "(\<lambda>X. Hom ` <X,B>)"
                    "(\<lambda>X Y f. h_mor(Hom, compo, B, X, Y, f))"
                    alpha by auto
  have id_A: "id ` A \<in> Hom ` <A,A>"
    using idinhom h_A by auto
  define f where "f \<equiv> alpha(A) ` (id ` A)"
  have f_in: "f \<in> Hom ` <A,B>"
  proof (unfold f_def)
    have "alpha(A) : Hom ` <A,A> \<rightarrow> Hom ` <A,B>"
      using h_A by (rule alpha_type)
    then show "alpha(A) ` (id ` A) \<in> Hom ` <A,B>"
      using id_A by auto
  qed
  have mor_match: "\<And>X g. \<lbrakk>X \<in> C; g \<in> Hom ` <X,A>\<rbrakk> \<Longrightarrow> alpha(X) ` g = compo ` X ` A ` B ` <g, f>"
  proof -
    fix X g
    assume h_XC: "X \<in> C" and h_g: "g \<in> Hom ` <X,A>"
    have nat_sq: "alpha(X) ` (h_mor(Hom, compo, A, X, A, g) ` (id ` A)) =
                  h_mor(Hom, compo, B, X, A, g) ` (alpha(A) ` (id ` A))"
      using h_XC h_A h_g id_A by (rule naturality_square)
    have lhs_eval: "h_mor(Hom, compo, A, X, A, g) ` (id ` A) = compo ` X ` A ` A ` <g, id ` A>"
      using id_A by (rule h_mor_eval)
    have lhs_id: "compo ` X ` A ` A ` <g, id ` A> = g"
      using h_XC h_A h_g by (rule comp_id_right)
    have rhs_eval: "h_mor(Hom, compo, B, X, A, g) ` f = compo ` X ` A ` B ` <g, f>"
      using f_in by (rule h_mor_eval)
    from nat_sq lhs_eval lhs_id rhs_eval show "alpha(X) ` g = compo ` X ` A ` B ` <g, f>"
      by (unfold f_def, auto)
  qed
  from f_in mor_match that show ?thesis by auto
qed

(* Representability Criterion via Universal Elements *)
theorem representability_criterion:
  assumes h_cat: "category(U, C, Hom, compo, id)"
      and h_psh: "presheaf(U, C, Hom, compo, id, P_obj, P_mor)"
      and h_univ: "has_universal_element(C, Hom, P_obj, P_mor, A, u)"
  shows "A \<in> C \<and> u \<in> P_obj(A) \<and>
         (\<forall>X\<in>C. \<forall>x\<in>P_obj(X). \<exists>!f. f \<in> Hom ` <X,A> \<and> (yoneda_psi(A, P_mor, u, Hom, X)) ` f = x)"
proof -
  from h_univ have h_A: "A \<in> C" and h_u: "u \<in> P_obj(A)"
    by (unfold has_universal_element_def, auto)
  have h_fact: "\<forall>X\<in>C. \<forall>x\<in>P_obj(X). \<exists>!f. f \<in> Hom ` <X,A> \<and> (yoneda_psi(A, P_mor, u, Hom, X)) ` f = x"
  proof (intro ballI)
    fix X x
    assume h_X: "X \<in> C" and h_x: "x \<in> P_obj(X)"
    from h_univ h_X h_x obtain f where
      h_uniq: "f \<in> Hom ` <X,A> \<and> P_mor(X,A,f) ` u = x" and
      h_only: "\<And>f'. f' \<in> Hom ` <X,A> \<and> P_mor(X,A,f') ` u = x \<Longrightarrow> f' = f"
      by (unfold has_universal_element_def, auto)
    have psi_f: "(yoneda_psi(A, P_mor, u, Hom, X)) ` f = x"
      using h_uniq yoneda_psi_eval by auto
    have psi_uniq: "\<And>f'. f' \<in> Hom ` <X,A> \<Longrightarrow> (yoneda_psi(A, P_mor, u, Hom, X)) ` f' = x \<Longrightarrow> f' = f"
      using yoneda_psi_eval h_only by auto
    show "\<exists>!f. f \<in> Hom ` <X,A> \<and> (yoneda_psi(A, P_mor, u, Hom, X)) ` f = x"
      using h_uniq psi_f psi_uniq by auto
  qed
  from h_A h_u h_fact show ?thesis by auto
qed

(* Pure proposition logic verification *)
theorem somethm : "\<And>n::o\<Rightarrow>o. (\<And>P::o. (P\<longrightarrow>n(P))) \<Longrightarrow> (\<And>P::o. (P\<longrightarrow>n(n(P))))"
proof
  fix n
  assume H1:"(\<And>P::o. (P\<longrightarrow>n(P)))"
  fix P
  assume H2:"P"
  have H3:"n(P)"
    by (rule mp[OF H1 H2])
  show H4:"n(n(P))"
    by (rule mp[OF H1 H3])
qed

end
