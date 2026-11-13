#!/usr/bin/env python3
"""Verification tests for YONEDA: theory syntax, category axioms, presheaves, Yoneda lemma, and embedding."""

import os
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class TestYoneda(unittest.TestCase):
    def test_isabelle_and_latex_files_exist(self):
        for rel in ("Yoneda.thy", "mylibrary.thy", "yoneda.tex", "yoneda.pdf", "gdmath.sty", "README.md"):
            path = os.path.join(ROOT, rel)
            self.assertTrue(os.path.isfile(path), f"Missing {path}")
            self.assertGreater(os.path.getsize(path), 0)

    def test_theory_syntax_and_import_integrity(self):
        yoneda_path = os.path.join(ROOT, "Yoneda.thy")
        mylib_path = os.path.join(ROOT, "mylibrary.thy")

        with open(yoneda_path, "r", encoding="utf-8") as f:
            yoneda_content = f.read()
        with open(mylib_path, "r", encoding="utf-8") as f:
            mylib_content = f.read()

        self.assertTrue(
            yoneda_content.strip().startswith("theory Yoneda imports mylibrary"),
            "Yoneda.thy must declare 'theory Yoneda imports mylibrary'",
        )
        self.assertTrue(
            yoneda_content.strip().endswith("end"),
            "Yoneda.thy must conclude with 'end'",
        )

        self.assertTrue(
            mylib_content.strip().startswith("theory mylibrary imports ZF"),
            "mylibrary.thy must declare 'theory mylibrary imports ZF'",
        )
        self.assertTrue(
            mylib_content.strip().endswith("end"),
            "mylibrary.thy must conclude with 'end'",
        )

    def test_absence_of_unproved_markers(self):
        unproved_markers = ["sorry", "oops", "admit"]
        for rel in ("Yoneda.thy", "mylibrary.thy"):
            path = os.path.join(ROOT, rel)
            with open(path, "r", encoding="utf-8") as f:
                content = f.read()
            for marker in unproved_markers:
                # Ensure no unproved markers as standalone tokens
                tokens = content.split()
                self.assertNotIn(
                    marker,
                    tokens,
                    f"Forbidden unproved marker '{marker}' found in {rel}",
                )

    def test_structural_validity_of_category_axioms(self):
        path = os.path.join(ROOT, "Yoneda.thy")
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        required_locales = ["catloc", "category", "presheaf", "natural_transformation"]
        for loc in required_locales:
            self.assertIn(f"locale {loc}", content, f"Missing locale {loc} in Yoneda.thy")

        required_axioms = ["comp_assoc", "comp_id_left", "comp_id_right"]
        for ax in required_axioms:
            self.assertIn(ax, content, f"Missing category axiom {ax} in Yoneda.thy")

    def test_presheaf_and_hom_functor_structure(self):
        path = os.path.join(ROOT, "Yoneda.thy")
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        required_presheaf_items = [
            "P_mor_type",
            "P_mor_id",
            "P_mor_comp",
            "h_obj",
            "h_mor",
            "h_mor_eval",
        ]
        for item in required_presheaf_items:
            self.assertIn(item, content, f"Missing presheaf/Hom item {item} in Yoneda.thy")

    def test_naturality_square_and_yoneda_bijection_statement(self):
        path = os.path.join(ROOT, "Yoneda.thy")
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        required_theorems = [
            "naturality_square",
            "yoneda_phi",
            "yoneda_psi",
            "yoneda_psi_naturality",
            "yoneda_left_inverse",
            "yoneda_right_inverse",
        ]
        for thm in required_theorems:
            self.assertIn(thm, content, f"Missing Yoneda bijection component {thm} in Yoneda.thy")

    def test_representability_and_yoneda_embedding(self):
        yoneda_path = os.path.join(ROOT, "Yoneda.thy")
        mylib_path = os.path.join(ROOT, "mylibrary.thy")

        with open(yoneda_path, "r", encoding="utf-8") as f:
            yoneda_content = f.read()
        with open(mylib_path, "r", encoding="utf-8") as f:
            mylib_content = f.read()

        self.assertIn("yoneda_embed_mor", yoneda_content)
        self.assertIn("yoneda_embedding_faithful", yoneda_content)
        self.assertIn("yoneda_embedding_full", yoneda_content)
        self.assertIn("representability_criterion", yoneda_content)

        self.assertIn("has_universal_element", mylib_content)
        self.assertIn("is_represented_by", mylib_content)

    def test_finite_category_yoneda_bijection_and_embedding(self):
        # Explicit computational model of a small category:
        # Poset category 0 <= 1 <= 2
        objects = [0, 1, 2]
        # Morphisms are pairs (X, Y) with X <= Y
        hom = {}
        for x in objects:
            for y in objects:
                if x <= y:
                    hom[(x, y)] = [(x, y)]
                else:
                    hom[(x, y)] = []

        # Category identity and composition
        def ident(x):
            return (x, x)

        def comp(m1, m2):
            # m1: X to Y, m2: Y to Z => result: X to Z
            assert m1[1] == m2[0]
            return (m1[0], m2[1])

        # Verify category axioms
        for x in objects:
            for y in objects:
                for f in hom[(x, y)]:
                    # Left identity
                    self.assertEqual(comp(ident(x), f), f)
                    # Right identity
                    self.assertEqual(comp(f, ident(y)), f)

        for x in objects:
            for y in objects:
                for z in objects:
                    for w in objects:
                        for f in hom[(x, y)]:
                            for g in hom[(y, z)]:
                                for h in hom[(z, w)]:
                                    self.assertEqual(comp(comp(f, g), h), comp(f, comp(g, h)))

        # Construct a Presheaf P : C^op to Set
        # P(0) = {'a0', 'b0'}, P(1) = {'a1'}, P(2) = {'a2'}
        P_obj = {0: ["a0", "b0"], 1: ["a1"], 2: ["a2"]}
        # P_mor((X, Y)) : P(Y) to P(X)
        P_mor = {
            (0, 0): {"a0": "a0", "b0": "b0"},
            (1, 1): {"a1": "a1"},
            (2, 2): {"a2": "a2"},
            (0, 1): {"a1": "a0"},
            (1, 2): {"a2": "a1"},
            (0, 2): {"a2": "a0"},
        }

        # Verify presheaf functoriality
        for x in objects:
            for u in P_obj[x]:
                self.assertEqual(P_mor[(x, x)][u], u)

        for x in objects:
            for y in objects:
                for z in objects:
                    if x <= y and y <= z:
                        f = (x, y)
                        g = (y, z)
                        gf = comp(f, g)
                        for u in P_obj[z]:
                            # Contravariant: P(g o f) = P(f) o P(g)
                            self.assertEqual(P_mor[gf][u], P_mor[f][P_mor[g][u]])

        # Test Yoneda bijection for each object A in C
        for A in objects:
            for u in P_obj[A]:
                # Extension Psi(u): for each X in C, Psi(u)_X(f) = P_mor(f)(u) for f in Hom(X, A)
                def psi_u(X, f):
                    return P_mor[f][u]

                # 1. Naturality square verification:
                # For any morphism m: X to Y and any g: Y to A:
                # Psi(u)_X(g o m) == P_mor(m)(Psi(u)_Y(g))
                for X in objects:
                    for Y in objects:
                        if X <= Y:
                            m = (X, Y)
                            for g in hom[(Y, A)]:
                                gm = comp(m, g)
                                lhs = psi_u(X, gm)
                                rhs = P_mor[m][psi_u(Y, g)]
                                self.assertEqual(
                                    lhs,
                                    rhs,
                                    f"Naturality square failed at A={A}, u={u}, m={m}, g={g}",
                                )

                # 2. Left inverse roundtrip: Phi(Psi(u)) = Psi(u)_A(id_A) = u
                phi_psi = psi_u(A, ident(A))
                self.assertEqual(phi_psi, u)

        # Test Yoneda Embedding: Hom(A, B) isomorphic to Nat(h_A, h_B)
        for A in objects:
            for B in objects:
                for f in hom[(A, B)]:
                    # Natural transformation induced by f: y(f)_X(g) = f o g for g in Hom(X, A)
                    def y_f(X, g):
                        return comp(g, f)

                    # Verify naturality of y(f):
                    for X in objects:
                        for Y in objects:
                            if X <= Y:
                                m = (X, Y)
                                for g in hom[(Y, A)]:
                                    # (h_B)_mor(m)(y(f)_Y(g)) == y(f)_X((h_A)_mor(m)(g))
                                    # (f o g) o m == f o (g o m)
                                    lhs = comp(m, y_f(Y, g))
                                    rhs = y_f(X, comp(m, g))
                                    self.assertEqual(lhs, rhs)

                    # Evaluation of y(f) at id_A recovers f:
                    recovered_f = y_f(A, ident(A))
                    self.assertEqual(recovered_f, f)


if __name__ == "__main__":
    unittest.main()
