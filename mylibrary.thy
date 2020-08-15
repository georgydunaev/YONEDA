theory mylibrary imports ZF
begin

(*
 {x: ... } should be a notation for \<lambda>x. ...
 (only for terms of type (i\<Rightarrow>o) )
*)

(* Binary relation *)
definition Rel :: \<open>i \<Rightarrow> o\<close>
  where "Rel(f) \<equiv> \<forall>p\<in>f. \<exists>x. \<exists>y. p = <x,y>"

lemma RelE :
  assumes H1:\<open>Rel(f)\<close>
      and H2:\<open>p\<in>f\<close>
      and H3:\<open>\<And>x y. <x,y>\<in>f \<Longrightarrow> P(<x,y>)\<close>
    shows \<open>P(p)\<close>
proof -
  from H1 have H1:"\<forall>p\<in>f. \<exists>x. \<exists>y. p = <x,y>"
    by (unfold Rel_def)    
  from H1 and H2 have H1:"\<exists>x. \<exists>y. p = <x,y>"
    by (rule bspec)
  then obtain x where H1:"\<exists>y. p = <x,y>" by auto
  then obtain y where H1:"p = <x,y>" by auto
  from H1 and H2 have \<open>\<langle>x, y\<rangle> \<in> f\<close> by auto
  then have \<open>P(<x,y>)\<close> by (rule H3)
  from \<open>P(<x,y>)\<close> and H1 show \<open>P(p)\<close> by auto
qed

(* "At most one" quantifier *)
definition Only1 :: \<open>('a \<Rightarrow> o) \<Rightarrow> o\<close>  (binder \<open>!\<close> 10)
  where only1_def: \<open>!x. P(x) \<equiv> (\<forall>x.\<forall>y. P(x) \<and> P(y) \<longrightarrow> x = y)\<close>

(* Binary relation *)
definition Fun :: \<open>i \<Rightarrow> o\<close>
  where "Fun(f) \<equiv> \<forall>a. !w. <a,w> \<in> f"

(* Example: *)
definition EmpS :: \<open>i\<close>
  where "EmpS \<equiv> THE a. \<forall>q. q \<notin> a"

(* Intersection of class OLD *)
definition intersecOLD :: \<open>(i \<Rightarrow> o) \<Rightarrow> i\<close>
where "intersecOLD(K) == THE x. \<forall>m. K(m) \<longrightarrow> x \<subseteq> m"

(* Inhabited *)
definition inhab :: "i \<Rightarrow> o"
  where "inhab(s) \<equiv> \<exists>m. m\<in>s"

definition inhabC :: "(i \<Rightarrow> o) \<Rightarrow> o"
  where "inhabC(K) \<equiv> \<exists>m. K(m)"

(* Intersection of class NEW *)
definition
  myInterC :: "(i \<Rightarrow> o) \<Rightarrow> (i \<Rightarrow> o)"
  where "myInterC(K) == \<lambda>x. (\<forall>m. K(m) \<longrightarrow> x\<in>m)"

axiomatization
  myInter :: "(i \<Rightarrow> o) \<Rightarrow> i"
where
(*  myInter_iff: "A \<in> myInter(K) \<longleftrightarrow> 
((\<forall>m. K(m) \<longrightarrow> A\<in>m) \<and> (\<exists>B. K(B)))" *)
  myInter_iff: "A \<in> myInter(K) \<longleftrightarrow> 
    (myInterC(K)(A) \<and> inhabC(K))"

theorem redefrepl:
  assumes "funcon(A,P)"
  shows "intersecOLD(K) = myInter(K)"

(* One may prove that
intersecOLD(K) = myInter(K)
*)

(* My "The" binder *)
definition myThe :: \<open>(i \<Rightarrow> o) \<Rightarrow> i\<close>
  where "myThe(P) == myInter(\<lambda>x. P(x))"

(*
PrimReplace :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> i"
replacement : "(\<forall>x\<in>A. \<forall>y z. P(x,y) \<and> P(x,z) \<longrightarrow> y = z)
 \<Longrightarrow>  b \<in> PrimReplace(A,P) \<longleftrightarrow> (\<exists>x\<in>A. P(x,b))"
*)

definition imageC :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> (i\<Rightarrow>o)"
  where "imageC(A,P) == %b. \<exists>x\<in>A. P(x,b)"

definition supersets :: "(i\<Rightarrow>o) \<Rightarrow> (i\<Rightarrow>o)"
  where "supersets(K) == \<lambda>x. \<forall>k. K(x) \<longrightarrow> k\<in>x"

definition supimg :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> (i\<Rightarrow>o)"
  where "supimg(A,P) == supersets(imageC(A,P))"

definition funcon :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> o"
  where "funcon(A,P) == (\<forall>x\<in>A. !w. P(x,w))"

axiomatization
  where myreplacement:
    "funcon(A,P) \<Longrightarrow> inhabC(supimg(A,P))"

definition myPrimReplace :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> i"
  where "myPrimReplace(A,P) == myInter(supimg(A,P))"

theorem redefrepl:
  assumes "funcon(A,P)"
  shows "myPrimReplace(A,P) = PrimReplace(A,P)"
(*
proof
 1. myPrimReplace(A, P) \<subseteq> PrimReplace(A, P)
 2. PrimReplace(A, P) \<subseteq> myPrimReplace(A, P)
qed
*)
  sorry

end