theory mylibrary imports ZF
begin
(*
definition eqtype :: \<open>[i,i] \<Rightarrow> i\<close>
  where "eqtype(x,y) == {_\<in>{0}. x=y}"
*)
(* Binary relation *)
definition Rel :: \<open>i \<Rightarrow> o\<close>
  where "Rel(f) == \<forall>p\<in>f. \<exists>x. \<exists>y. p = <x,y>"

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
(*lemma q1 : "\<lbrakk>Rel(f); p\<in>f; \<And>x y. <x,y>\<in>f \<Longrightarrow> P(<x,y>)\<rbrakk>
 \<Longrightarrow> P(p)"*)

(*
  show "P(p)"
  proof(rule exE[OF H1])
    fix x
    assume H1:"\<exists>y. p = \<langle>x, y\<rangle>"
    show "P(p)"
    proof(rule exE[OF H1])
      fix y
      assume H1:"p = \<langle>x, y\<rangle>"
      have B:"P(<x,y>)"
      proof(rule H3[OF ])
        from H1 and H2 show \<open>\<langle>x, y\<rangle> \<in> f\<close>
          by auto
      qed
      from H1 and B show "P(p)" by auto
    qed
  qed
*)
qed

  have "0\<in>1"
    sorry



(unfold eqtype_def)

end