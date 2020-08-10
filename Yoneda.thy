theory Yoneda imports ZF
begin
(*
definition add_g :: \<open>i\<close>
  where add_g_def : \<open>add_g == \<lambda>x\<in>(nat*nat). succ(fst(x))\<close>
*)
(* Definition of a category *)
(*
We will not use classes, but we will use universes.
not the class of objects  i\<Rightarrow>o, but a set of objects i

I'm pretty sure that elements of Grothendieck universe and
 functions between them forms a category.
*)

(* U is a Grothendieck universe iff
1) Tr(U)
2) \<forall>x,y\<in>U.{x,y}\<in>U
3) \<forall>x\<in>U.Pow(x)\<in>U
4) \<And>F::(i\<Rightarrow>i).   \<forall>I\<in>U. F[I]\<subseteq>U \<longrightarrow> Union(F[I])\<in>U
4') \<forall>f. Fun(f) \<longrightarrow> (\<forall>I\<in>U. f[I]\<subseteq>U \<longrightarrow> Union(f[I])\<in>U)
*)
(* We will use 4' since 
pros: I don't wanna lift 
a function f to a class function (i\<Rightarrow>i) back and forward.
cons: But it may handy to use f(x) = y abbreviation
 instead of (f`y)...
pros: We may want one day to interpret obtained theorems from Isabelle
 to another maybe 1st order prover.
pros: (f`x) = y is more reliable from theoretical aspects.
Rule of thumb: use classes only if it's impossible to use sets.
pros: We are not required to limit the number of universes.
*)
(*
How to search theorem? "Query"\<rightarrow>"Find"
How to make abstract context? 
a) locale
b) when something is needed twice -- use lemma.
*)

(* Universes are under construction, I'll continue when we need one.*)
definition Tr :: "i \<Rightarrow> o"
  where Tr_def : "Tr(x) == \<forall>y\<in>x. y\<subseteq>x"  (* y \<subseteq> Pow(y) *)

(* Universe *)
axiomatization U0 :: "i"
  where Un1:"Tr(U0)"

(* here can be defined a function from ordinals to universes *)

(* definition of the set of U-small categories *)

(*
A category is small if it has a small set of
 objects and a small set of morphisms.
*)

(* Too complicated
definition Cat :: \<open>i\<Rightarrow>i\<close>
  where \<open>Cat == (\<Prod>C\<in>U. \<Prod>hom \<in> C\<rightarrow>(C\<rightarrow>U). U)\<close>
*)

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

(* locale *)
(* for U-small categiries *)
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
(*
(*  assumes idinhom: \<open>A\<in>C \<Longrightarrow> (id ` A) : Hom ` <A,A>\<close> *)

definition IsCat :: \<open>[i, [i, i] \<Rightarrow> i] \<Rightarrow> o\<close>
*)

(* Obviously, every small category is locally small. *)

(*

Comp : Pi().

definition IsCat :: \<open>[i, [i, i] \<Rightarrow> i] \<Rightarrow> o\<close>
  where \<open>IsCat(C, Comp) == C=C\<close>
*)

end