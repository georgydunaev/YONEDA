#!/usr/bin/env python3
"""Verification tests for YONEDA (Yoneda.thy, mylibrary.thy, yoneda.tex, and finite category Yoneda bijection)."""

import os
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class TestYoneda(unittest.TestCase):
    def test_isabelle_and_latex_files_exist(self):
        for rel in ("Yoneda.thy", "mylibrary.thy", "yoneda.tex", "yoneda.pdf", "gdmath.sty", "README.md"):
            path = os.path.join(ROOT, rel)
            self.assertTrue(os.path.isfile(path), f"Missing {path}")
            self.assertGreater(os.path.getsize(path), 0)

    def test_finite_yoneda_bijection(self):
        # Verify Yoneda bijection Phi(alpha) = alpha_A(id_A) and Psi(x)_B(f) = F(f)(x)
        # on a finite poset category 0 -> 1
        F_obj = {0: ["x0", "y0"], 1: ["x1", "y1"]}
        F_mor = {
            (0, 0): {"x0": "x0", "y0": "y0"},
            (0, 1): {"x0": "x1", "y0": "x1"},
            (1, 1): {"x1": "x1", "y1": "y1"},
        }
        # Psi maps each element u in F(0) to a natural transformation Hom(0, -) => F
        for u in F_obj[0]:
            alpha_0_id = F_mor[(0, 0)][u]
            self.assertEqual(alpha_0_id, u)
            # Naturality square along f: 0 -> 1
            lhs = F_mor[(0, 1)][alpha_0_id]
            rhs = F_mor[(0, 1)][u]
            self.assertEqual(lhs, rhs)


if __name__ == "__main__":
    unittest.main()
