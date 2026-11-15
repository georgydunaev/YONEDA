# Manuscript and Proof Index: YONEDA

## 1. Repository Overview and Scope

`YONEDA` is a formal category theory and set-theoretic foundations repository combining an Isabelle/ZF mechanization (`mylibrary.thy`, `Yoneda.thy`) with a companion mathematical manuscript (`yoneda.tex`, using custom LaTeX macros in `gdmath.sty`; compiled snapshot preserved in `yoneda.pdf`). It develops class/set intersections, uniqueness and definite description binders, dependent sums ($\Sigma$) and dependent products ($\Pi$), transitive sets and von Neumann ordinals, locally small categories, opposite categories, contravariant/covariant Hom-functors (presheaves), natural transformations, the Yoneda Lemma, the Yoneda Embedding (full and faithful), universal elements and representable functors, categorical adjunctions (both Hom-set bijection and unit-counit formulations), and preservation of limits by right adjoints and representable functors.

---

## 2. Inventory of Source Manuscript and Proof Files

| File | Lines | Language / System | Role and Contents |
| :--- | :--- | :--- | :--- |
| `yoneda.tex` | 374 | LaTeX | Primary mathematical manuscript: *"Some Proofs of the Category Theory"* by Georgy Dunaev. Contains Section 1 (*Logic and Set Theory*: predicate calculus axiom schemata and inference rules, class/set intersections, uniqueness quantifier $!x$, unique existence $\exists!x$, dual $?x$, definite description $\iota / \mathrm{The}$, dependent sum $\Sigma R$ and product $\Pi R$, functional extensionality, transitive sets $\mathrm{Tr}(A)$ and ordinals $\mathrm{TOrd}(A)$) and Section 2 (*Category Theory*: locally small categories, duality $C^{\mathrm{op}}$, covariant functors, Hom-functor $\mathrm{Hom}_C(-, x)$, natural transformations induced by morphisms, Yoneda embedding faithfulness/fullness, and the contravariant Yoneda Lemma $\mathrm{Nat}(h_A, G) \simeq G(A)$). |
| `gdmath.sty` | 112 | LaTeX Package | Custom mathematical macro package defining set-theoretic and categorical notation (`\interclass`, `\inter`, `\propdef`, `\eqdef`, `\The`, `\apo`, `\dom`, `\Fun`, `\Rel`, `\Pow`, `\Set`, `\Cat`, `\Ob`, `\Hom`, `\HomMor`, `\FMor`, `\GMor`, `\Nat`, `\TOrd`, `\Tr`, `\mysucc`, `\myprf`, `\myqed`). |
| `mylibrary.thy` | 207 | Isabelle/ZF | Foundational set-theoretic and categorical prelude importing `ZF`. Defines relations (`Rel`, `RelE`), uniqueness quantifier (`Only1`, `Only1I`, `Only1E`), functional graphs (`Fun`, `FunI`), empty set (`EmpS`), inhabited sets (`inhab`, `inhabC`), intersections (`intersecOLD`, `myInterC`, `myInter`), definite description (`myThe`), image and function space (`imageC`, `supersets`, `supimg`, `funcon`, `myPrimReplace`), and set-theoretic categorical predicates (`is_iso`, `has_universal_element`, `is_represented_by`, `is_functor`, `is_nat_trans`, `is_adjunction`, `is_cone`, `is_limit`, `is_cocone`, `is_colimit`). |
| `Yoneda.thy` | 585 | Isabelle/ZF | Core formalization of transitive sets (`Tr`), local universe `U0`, typed set equality (`eqtype`, `eqtyperefl`), category locales (`catloc`, `category`), opposite category (`op_Hom`, `op_compo`), contravariant presheaves (`presheaf`), representable presheaf $h_A$ (`h_obj`, `h_mor`), natural transformations (`natural_transformation`), the Yoneda bijection maps (`yoneda_phi`, `yoneda_psi`), naturality and mutual inversion theorems, Yoneda embedding fullness and faithfulness, representability via universal elements, covariant functors (`covariant_functor`), adjunctions (`adjunction`), unit-counit triangle identities, transpose bijections, limits (`cone`, `limit`), colimits (`cocone`, `colimit`), right-adjoint limit preservation (`right_adjoint_preserves_limits`), and Yoneda limit preservation (`yoneda_preserves_limits`). |
| `yoneda.pdf` | Binary | PDF | Stored compiled artifact of `yoneda.tex` (strictly read-only/immutable). |
| `tests/test_yoneda.py` | 180 | Python | Structural and semantic verification suite checking the Yoneda Lemma, naturality squares, and presheaf laws on finite categories. |
| `tests/test_adjunctions.py` | 210 | Python | Verification test suite checking unit-counit triangle identities, Hom-set adjunction transposes,cones/limits, and right-adjoint limit preservation. |

---

## 3. Core Mathematical Results Established

### 3.1 Set-Theoretic Foundations (`yoneda.tex` Section 1, `mylibrary.thy`, `Yoneda.thy`)
1. **Uniqueness and Definite Description Binders**:
   - Uniqueness quantifier $!x.\,P(x) \iff \forall x_1\,\forall x_2.\,P(x_1) \land P(x_2) \implies x_1 = x_2$ (`Only1` in `mylibrary.thy`, proved with introduction `Only1I` and elimination `Only1E`).
   - Definite description $\mathrm{The}\,x.\,P(x) = \bigcap \{x : P(x) \land !w.\,P(w)\}$ (`myThe` in `mylibrary.thy`).
2. **Dependent Products and Sums (`yoneda.tex` Section 1.4, `mylibrary.thy`)**:
   - Dependent sum $\Sigma R = \{\langle x, y \rangle : y \in R(x)\}$ and dependent product $\Pi R = \{f \in \mathcal{P}(\Sigma R) : \mathrm{Fun}(f) \land \mathrm{dom}(R) \subseteq \mathrm{dom}(f)\}$, together with function space Pi-types (`funcon` in `mylibrary.thy`) and typed equality (`eqtype`, `eqtyperefl`, `q1`, `q2` in `Yoneda.thy`).
3. **Transitive Sets and Ordinals (`yoneda.tex` Section 1.6, `Yoneda.thy`)**:
   - Formal definition of transitive class/set $\mathrm{Tr}(A) \iff \forall a \in A.\,a \subseteq A$ (`Tr_def` in `Yoneda.thy`), closure under ordinal successor $\mathrm{Tr}(A) \implies \mathrm{Tr}(A \cup \{A\})$, and transitive ordinal preservation $\mathrm{TOrd}(A) \implies \mathrm{TOrd}(A \cup \{A\})$.

### 3.2 Yoneda Lemma and Yoneda Embedding (`yoneda.tex` Section 2, `Yoneda.thy`)
1. **Opposite Category and Representable Presheaf (`category`, `presheaf` locales in `Yoneda.thy`)**:
   - Given a locally small category $\mathcal{C}$ (`Ob`, `Hom`, `Id`, `compo`), the opposite Hom-set `op_Hom A B = Hom B A` and reversed composition `op_compo` satisfy all category axioms.
   - For each $A \in \mathrm{Ob}_{\mathcal{C}}$, the contravariant Hom-functor $h_A(X) = \mathrm{Hom}_{\mathcal{C}}(X, A)$ (`h_obj`) with action on morphisms $h_A(f) = (\lambda g \in \mathrm{Hom}_{\mathcal{C}}(Y, A).\,g \circ_{\mathcal{C}} f)$ (`h_mor`) satisfies the functoriality laws (`h_mor_eval`, `h_mor_type`, `h_mor_id`, `h_mor_comp`).
2. **Contravariant Yoneda Bijection (`yoneda_phi`, `yoneda_psi`)**:
   - Forward evaluation map $\Phi(\eta) = \eta_A(\mathrm{Id}_A) \in F(A)$ (`yoneda_phi`).
   - Backward canonical transformation $\Psi(u)_X(f) = F(f)(u)$ (`yoneda_psi`).
   - **Naturality (`Theorem yoneda_psi_naturality`)**: For every $u \in F(A)$ and morphism $f \in \mathrm{Hom}_{\mathcal{C}}(Y, X)$, $\Psi(u)$ commutes with $F(f)$ and $h_A(f)$.
   - **Bijection (`Theorem yoneda_left_inverse` and `Theorem yoneda_right_inverse`)**:
     - $\Phi(\Psi(u)) = u$ for all $u \in F(A)$ (`yoneda_left_inverse`).
     - $\Psi(\Phi(\eta))_X(f) = \eta_X(f)$ for every natural transformation $\eta : h_A \Rightarrow F$, object $X \in \mathrm{Ob}_{\mathcal{C}}$, and morphism $f \in \mathrm{Hom}_{\mathcal{C}}(X, A)$ (`yoneda_right_inverse`).
3. **Yoneda Embedding (`yoneda_embed_mor`, `yoneda_embedding_faithful`, `yoneda_embedding_full`)**:
   - Every morphism $k \in \mathrm{Hom}_{\mathcal{C}}(A, B)$ induces a natural transformation $h_k : h_A \Rightarrow h_B$ via post-composition (`yoneda_embed_mor`).
   - **Faithfulness (`Theorem yoneda_embedding_faithful`)**: If $h_{k_1} = h_{k_2}$ on $A$, then $k_1 = k_2$.
   - **Fullness (`Theorem yoneda_embedding_full`)**: Every natural transformation $\eta : h_A \Rightarrow h_B$ is induced by a unique morphism $k = \Phi(\eta) = \eta_A(\mathrm{Id}_A) \in \mathrm{Hom}_{\mathcal{C}}(A, B)$.
4. **Universal Elements and Representability (`Theorem representability_criterion`)**:
   - A presheaf $F$ is representable by $(A, u)$ with $u \in F(A)$ if and only if $\Psi(u)_X : \mathrm{Hom}_{\mathcal{C}}(X, A) \to F(X)$ is a bijection for every $X \in \mathrm{Ob}_{\mathcal{C}}$.

### 3.3 Adjunctions, Limits, and Limit Preservation (`Yoneda.thy` lines 310--585)
1. **Categorical Adjunctions (`locale adjunction`)**:
   - Formalizes covariant functors $L : \mathcal{C} \to \mathcal{D}$ and $R : \mathcal{D} \to \mathcal{C}$ equipped with unit $\eta$, counit $\varepsilon$, and Hom-set transposes $\varphi = \text{adj\_transpose\_lr}$ and $\psi = \text{adj\_transpose\_rl}$.
   - Proves the equivalence between the unit-counit triangle identities (`adjunction_triangle_1`, `adjunction_triangle_2`) and the mutual inversion of the Hom-set transposes (`adj_transpose_left_inv`, `adj_transpose_right_inv`, `adjunction_counit_from_unit`, `adjunction_unit_from_counit`).
2. **Cones, Limits, Colimits, and Preservation Theorems (`locale cone`, `locale limit`, `locale cocone`, `locale colimit`)**:
   - **Uniqueness of Mediating Morphisms (`limit_mediating_unique`, `colimit_mediating_unique`)**.
   - **Right Adjoints Preserve Limits (`Theorem right_adjoint_preserves_limits`)**: Any right adjoint functor $R$ maps a limit cone in $\mathcal{D}$ to a limit cone in $\mathcal{C}$.
   - **Representable Functors Preserve Limits (`Theorem yoneda_preserves_limits`)**: The Hom-presheaf $h_A$ maps universal cones to universal cones.

---

## 4. Open Questions and Unresolved Proof Obligations

1. **Elimination of Auxiliary Axiomatizations in `mylibrary.thy` and `Yoneda.thy`**:
   - `mylibrary.thy` uses three `axiomatization` declarations (`myInter` at line 96, `funcon` typing at line 117, and `myPrimReplace` at line 124), and `Yoneda.thy` declares `axiomatization U0 :: "i"` (line 13) for the ambient Grothendieck-style universe set. Replacing these axiomatizations with pure definitional constructions over Isabelle/ZF's native `Inter`, `Pi`, and `Replace` operators will make the theory 100% definitional.
2. **Completion of Functional Subset Proof in `yoneda.tex` (Section 1.5, line 144)**:
   - The prose proof of the theorem in Section 1.5 of `yoneda.tex` ($\forall x \in X.\,g_1(x) = g_2(x) \implies g_1 \subseteq g_2$ when $\mathrm{dom}(g_1) \subseteq \mathrm{dom}(g_2)$) currently ends with the note `... to be continued ...` and can be completed in the manuscript to match the mechanized function equality proofs in `Yoneda.thy`.
3. **Co-Yoneda Lemma (Density Formula) and Kan Extensions (Ticket 7406)**:
   - Extending the `limit` and `colimit` locales in `Yoneda.thy` to formalize the Co-Yoneda (Ninja Yoneda / density) theorem, showing that every presheaf $F : \mathcal{C}^{\mathrm{op}} \to \mathbf{Set}$ is canonically isomorphic to the colimit of representable presheaves indexed by its category of elements $\int F$, and generalizing to pointwise left and right Kan extensions.
