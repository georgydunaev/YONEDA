# Project Overview: Isabelle and LaTeX Formalization of the Yoneda Lemma (`YONEDA`)

## 1. Purpose and Scope
`YONEDA` (`/botworkspace/YONEDA`) provides an Isabelle formalization (`Yoneda.thy`, `mylibrary.thy`, `CoYonedaAndDefinitionalPrelude.thy`) and a typeset LaTeX mathematical exposition (`yoneda.tex`, `gdmath.sty`) of the Yoneda Lemma, representable functors, universal properties, and categorical duality. The compiled `yoneda.pdf` file is strictly immutable per Fact 11.

## 2. Key Files and Structure
- [Yoneda.thy](file:///botworkspace/YONEDA/Yoneda.thy) — Main Isabelle theory formalizing categories, hom-functors, natural transformations, and the Yoneda Lemma bijection.
- [mylibrary.thy](file:///botworkspace/YONEDA/mylibrary.thy) — Foundational Isabelle helper lemmas for set-theoretic functions, dependent products, and extensionality.
- [CoYonedaAndDefinitionalPrelude.thy](file:///botworkspace/YONEDA/CoYonedaAndDefinitionalPrelude.thy) — Contravariant/covariant Co-Yoneda density theorem and definitional prelude.
- [yoneda.tex](file:///botworkspace/YONEDA/yoneda.tex) and [gdmath.sty](file:///botworkspace/YONEDA/gdmath.sty) — LaTeX manuscript and macro package.
- [MANUSCRIPT_AND_PROOF_INDEX.md](file:///botworkspace/YONEDA/MANUSCRIPT_AND_PROOF_INDEX.md) and [PROOF_COMPLETIONS_AND_EXTENSIONS.md](file:///botworkspace/YONEDA/PROOF_COMPLETIONS_AND_EXTENSIONS.md) — Detailed theorem index and completion notes.
- `tests/` — Automated Python verification tests checking Isabelle theory structure and LaTeX definitions.

## 3. Verification
```bash
python3 -m unittest discover -s /botworkspace/YONEDA/tests -p "test_*.py"
```
