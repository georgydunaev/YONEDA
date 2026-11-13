theory mylibrary imports ZF
begin

(*
  Foundational set-theoretic utilities and abstractions for category theory
  and the Yoneda lemma formalization.
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

lemma Only1I :
  assumes "\<And>x y. P(x) \<Longrightarrow> P(y) \<Longrightarrow> x = y"
  shows "!x. P(x)"
proof (unfold only1_def)
  show "\<forall>x y. P(x) \<and> P(y) \<longrightarrow> x = y"
  proof (intro allI impI)
    fix x y
    assume "P(x) \<and> P(y)"
    then have "P(x)" and "P(y)" by auto
    then show "x = y" by (rule assms)
  qed
qed

lemma Only1E :
  assumes "!x. P(x)" and "P(x)" and "P(y)"
  shows "x = y"
proof -
  from assms(1) have "\<forall>x y. P(x) \<and> P(y) \<longrightarrow> x = y"
    by (unfold only1_def)
  with assms(2,3) show "x = y" by auto
qed

(* Binary relation functionality *)
definition Fun :: \<open>i \<Rightarrow> o\<close>
  where "Fun(f) \<equiv> \<forall>a. !w. <a,w> \<in> f"

lemma FunI :
  assumes "\<And>a w1 w2. <a,w1> \<in> f \<Longrightarrow> <a,w2> \<in> f \<Longrightarrow> w1 = w2"
  shows "Fun(f)"
proof (unfold Fun_def)
  show "\<forall>a. !w. <a,w> \<in> f"
  proof (intro allI)
    fix a
    show "!w. <a,w> \<in> f"
    proof (rule Only1I)
      fix w1 w2
      assume "<a,w1> \<in> f" and "<a,w2> \<in> f"
      then show "w1 = w2" by (rule assms)
    qed
  qed
qed

(* Empty set description *)
definition EmpS :: \<open>i\<close>
  where "EmpS \<equiv> THE a. \<forall>q. q \<notin> a"

(* Intersection of class OLD *)
definition intersecOLD :: \<open>(i \<Rightarrow> o) \<Rightarrow> i\<close>
  where "intersecOLD(K) == THE x. \<forall>m. K(m) \<longrightarrow> x \<subseteq> m"

(* Inhabited predicates *)
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
  myInter_iff: "A \<in> myInter(K) \<longleftrightarrow> (myInterC(K)(A) \<and> inhabC(K))"

(* Definite description binder via class intersection *)
definition myThe :: \<open>(i \<Rightarrow> o) \<Rightarrow> i\<close>
  where "myThe(P) == myInter(\<lambda>x. P(x))"

definition imageC :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> (i\<Rightarrow>o)"
  where "imageC(A,P) == %b. \<exists>x\<in>A. P(x,b)"

definition supersets :: "(i\<Rightarrow>o) \<Rightarrow> (i\<Rightarrow>o)"
  where "supersets(K) == \<lambda>x. \<forall>k. K(k) \<longrightarrow> k \<subseteq> x"

definition supimg :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> (i\<Rightarrow>o)"
  where "supimg(A,P) == supersets(imageC(A,P))"

definition funcon :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> o"
  where "funcon(A,P) == (\<forall>x\<in>A. !w. P(x,w))"

axiomatization
  where myreplacement:
    "funcon(A,P) \<Longrightarrow> inhabC(supimg(A,P))"

definition myPrimReplace :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> i"
  where "myPrimReplace(A,P) == myInter(supimg(A,P))"

axiomatization
  where myPrimReplace_correct:
    "funcon(A,P) \<Longrightarrow> myPrimReplace(A,P) = PrimReplace(A,P)"

(* Shared Category Theory Utility Definitions *)

(* General isomorphism between objects in a category *)
definition is_iso :: "[i, i, i, i, i, i, i] \<Rightarrow> o"
  where "is_iso(C, Hom, compo, id, X, Y, f) \<equiv>
    f \<in> Hom ` <X,Y> \<and>
    (\<exists>g \<in> Hom ` <Y,X>.
       compo ` X ` Y ` X ` <f, g> = id ` X \<and>
       compo ` Y ` X ` Y ` <g, f> = id ` Y)"

(* Universal property abstraction: an initial or terminal object / universal element *)
definition has_universal_element :: "[i, i, (i \<Rightarrow> i), (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i), i, i] \<Rightarrow> o"
  where "has_universal_element(C, Hom, P_obj, P_mor, A, u) \<equiv>
    A \<in> C \<and> u \<in> P_obj(A) \<and>
    (\<forall>X\<in>C. \<forall>x\<in>P_obj(X). \<exists>!f. f \<in> Hom ` <X,A> \<and> P_mor(X,A,f) ` u = x)"

(* Representability of a presheaf by an object and universal element *)
definition is_represented_by :: "[i, i, (i \<Rightarrow> i), (i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i), i, i] \<Rightarrow> o"
  where "is_represented_by(C, Hom, P_obj, P_mor, A, u) \<equiv>
    has_universal_element(C, Hom, P_obj, P_mor, A, u)"

end
