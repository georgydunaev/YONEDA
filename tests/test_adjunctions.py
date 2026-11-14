#!/usr/bin/env python3
"""Categorical algorithmic verification of adjunctions, triangle identities, limits, colimits, and Yoneda limit preservation."""

import os
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class TestAdjunctionsAndLimitsTheoryIntegrity(unittest.TestCase):
    """Verify presence and structure of newly formalized category theory items in Isabelle theories."""

    def test_mylibrary_adjunction_and_limit_definitions(self):
        path = os.path.join(ROOT, "mylibrary.thy")
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        expected_definitions = [
            "is_functor",
            "is_nat_trans",
            "is_adjunction",
            "is_cone",
            "is_limit",
            "is_cocone",
            "is_colimit",
        ]
        for item in expected_definitions:
            self.assertIn(
                item,
                content,
                f"Missing definition {item} in mylibrary.thy",
            )

    def test_yoneda_adjunction_and_limit_locales_and_theorems(self):
        path = os.path.join(ROOT, "Yoneda.thy")
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        expected_locales = [
            "locale covariant_functor",
            "locale adjunction",
            "locale diagram_cone",
            "locale diagram_limit",
        ]
        for loc in expected_locales:
            self.assertIn(
                loc,
                content,
                f"Missing {loc} in Yoneda.thy",
            )

        expected_theorems = [
            "adjunction_triangle_1",
            "adjunction_triangle_2",
            "adjunction_counit_from_unit",
            "adjunction_unit_from_counit",
            "limit_factorization_exists",
            "limit_factorization_unique",
            "yoneda_preserves_limits",
            "right_adjoint_preserves_limits_universal",
        ]
        for thm in expected_theorems:
            self.assertIn(
                thm,
                content,
                f"Missing theorem {thm} in Yoneda.thy",
            )


class TestFiniteCategoryAdjunctions(unittest.TestCase):
    """Algorithmic verification of adjunctions, triangle identities, and Hom-set bijections on finite categories."""

    def setUp(self):
        # Construct explicit finite categories C and D for Cartesian Closed Adjunction (- x A) -| (-)^A.
        # Let base objects be finite sets {0}, {0, 1}
        # A is fixed set {0, 1}
        self.A = (0, 1)

        # Objects of C and D are tuples representing finite sets
        self.objects = [(), (0,), (0, 1)]

        # Morphisms are set-theoretic functions represented as tuples of image values
        # For domain X = (x0, x1, ...) and codomain Y:
        # A function f : X -> Y is represented by tuple (f(x0), f(x1), ...)
        self.hom = {}
        for X in self.objects:
            for Y in self.objects:
                funcs = []
                if len(X) == 0:
                    funcs.append(())
                elif len(Y) == 0:
                    pass  # No functions from non-empty set to empty set
                else:
                    # Cartesian power Y^X
                    def make_funcs(x_idx, current):
                        if x_idx == len(X):
                            funcs.append(tuple(current))
                            return
                        for y in Y:
                            current.append(y)
                            make_funcs(x_idx + 1, current)
                            current.pop()

                    make_funcs(0, [])
                self.hom[(X, Y)] = funcs

        def id_mor(X):
            return tuple(X)

        def comp(f, g, X, Y, Z):
            # f : X -> Y, g : Y -> Z => g o f : X -> Z
            # f is tuple of len(X) with values in Y
            # g is tuple of len(Y) with values in Z
            y_to_idx = {y: idx for idx, y in enumerate(Y)}
            return tuple(g[y_to_idx[f_x]] for f_x in f)

        self.id_mor = id_mor
        self.comp = comp

        # Functor F(X) = X x A (cartesian product)
        # We encode product elements as indices into product pairs
        def F_obj(X):
            # Pairs (x, a)
            pairs = []
            for x in X:
                for a in self.A:
                    pairs.append((x, a))
            return tuple(pairs)

        def F_mor(f, X, Y):
            # f : X -> Y, F(f) : X x A -> Y x A
            # (x, a) |-> (f(x), a)
            x_to_idx = {x: idx for idx, x in enumerate(X)}
            res = []
            for x in X:
                fx = f[x_to_idx[x]]
                for a in self.A:
                    res.append((fx, a))
            return tuple(res)

        # Functor G(Y) = Y^A (exponential)
        # Since A = (0, 1), G(Y) = Y x Y (pairs of values for a=0 and a=1)
        def G_obj(Y):
            pairs = []
            for y0 in Y:
                for y1 in Y:
                    pairs.append((y0, y1))
            return tuple(pairs)

        def G_mor(g, Y, Z):
            # g : Y -> Z, G(g) : Y^A -> Z^A
            # (y0, y1) |-> (g(y0), g(y1))
            y_to_idx = {y: idx for idx, y in enumerate(Y)}
            res = []
            for y0 in Y:
                for y1 in Y:
                    gy0 = g[y_to_idx[y0]]
                    gy1 = g[y_to_idx[y1]]
                    res.append((gy0, gy1))
            return tuple(res)

        self.F_obj = F_obj
        self.F_mor = F_mor
        self.G_obj = G_obj
        self.G_mor = G_mor

    def test_triangle_identities_and_hom_bijection(self):
        # Unit eta_X : X -> (X x A)^A = G(F(X))
        # Maps x |-> ( (x, 0), (x, 1) )
        def eta(X):
            res = []
            for x in X:
                res.append(((x, 0), (x, 1)))
            return tuple(res)

        # Counit eps_Y : F(G(Y)) = Y^A x A -> Y
        # Maps ((y0, y1), a) |-> y0 if a==0 else y1
        def eps(Y):
            res = []
            for y0 in Y:
                for y1 in Y:
                    for a in self.A:
                        res.append(y0 if a == 0 else y1)
            return tuple(res)

        # 1. Verify Triangle Identity 1: eps_(F(X)) o F(eta_X) == id_(F(X))
        for X in self.objects:
            FX = self.F_obj(X)
            GFX = self.G_obj(FX)
            F_GFX = self.F_obj(GFX)

            eta_X = eta(X)
            # F(eta_X) : F(X) -> F(G(F(X)))
            x_to_idx = {x: idx for idx, x in enumerate(X)}
            F_eta_X = []
            for x in X:
                eta_x = eta_X[x_to_idx[x]]
                for a in self.A:
                    F_eta_X.append((eta_x, a))
            F_eta_X = tuple(F_eta_X)

            # eps_(FX) : F(G(FX)) -> FX
            eps_FX = eps(FX)

            # Composite: eps_FX o F(eta_X) : FX -> FX
            target_to_idx = {p: idx for idx, p in enumerate(F_GFX)}
            comp_1 = tuple(eps_FX[target_to_idx[val]] for val in F_eta_X)

            id_FX = tuple(FX)
            self.assertEqual(
                comp_1,
                id_FX,
                f"Triangle identity 1 failed for X={X}",
            )

        # 2. Verify Triangle Identity 2: G(eps_Y) o eta_(G(Y)) == id_(G(Y))
        for Y in [(), (0,), (0, 1)]:
            GY = self.G_obj(Y)
            FGY = self.F_obj(GY)
            GFGY = self.G_obj(FGY)

            # eta_(GY) : GY -> G(F(GY))
            eta_GY = eta(GY)

            # eps_Y : F(GY) -> Y
            eps_Y = eps(Y)

            # G(eps_Y) : G(F(GY)) -> G(Y)
            fgy_to_idx = {p: idx for idx, p in enumerate(FGY)}
            G_eps_Y = []
            for p0 in FGY:
                for p1 in FGY:
                    val0 = eps_Y[fgy_to_idx[p0]]
                    val1 = eps_Y[fgy_to_idx[p1]]
                    G_eps_Y.append((val0, val1))
            G_eps_Y = tuple(G_eps_Y)

            # Composite: G(eps_Y) o eta_(GY) : GY -> GY
            gfgy_to_idx = {q: idx for idx, q in enumerate(GFGY)}
            comp_2 = tuple(G_eps_Y[gfgy_to_idx[val]] for val in eta_GY)

            id_GY = tuple(GY)
            self.assertEqual(
                comp_2,
                id_GY,
                f"Triangle identity 2 failed for Y={Y}",
            )

        # 3. Verify Hom-set Natural Bijection:
        # Theta : Hom(F(X), Y) -> Hom(X, G(Y))
        # Theta(f) = G(f) o eta_X
        # Theta_inv(g) = eps_Y o F(g)
        for X in self.objects:
            for Y in self.objects:
                FX = self.F_obj(X)
                GY = self.G_obj(Y)

                # Construct Hom(F(X), Y)
                hom_FX_Y = []
                if len(FX) == 0:
                    hom_FX_Y.append(())
                elif len(Y) > 0:
                    def make_f(idx, cur):
                        if idx == len(FX):
                            hom_FX_Y.append(tuple(cur))
                            return
                        for y in Y:
                            cur.append(y)
                            make_f(idx + 1, cur)
                            cur.pop()
                    make_f(0, [])

                # Construct Hom(X, G(Y))
                hom_X_GY = []
                if len(X) == 0:
                    hom_X_GY.append(())
                elif len(GY) > 0:
                    def make_g(idx, cur):
                        if idx == len(X):
                            hom_X_GY.append(tuple(cur))
                            return
                        for gy in GY:
                            cur.append(gy)
                            make_g(idx + 1, cur)
                            cur.pop()
                    make_g(0, [])

                # Test bijection for each f in Hom(F(X), Y)
                fx_to_idx = {p: idx for idx, p in enumerate(FX)}
                for f in hom_FX_Y:
                    # Theta(f)(x) = (f(x, 0), f(x, 1)) in G(Y)
                    theta_f = tuple((f[fx_to_idx[(x, 0)]], f[fx_to_idx[(x, 1)]]) for x in X)
                    self.assertIn(theta_f, hom_X_GY)

                    # Roundtrip: Theta_inv(theta_f) should recover f
                    x_to_idx = {x: idx for idx, x in enumerate(X)}
                    recovered_f = tuple(
                        theta_f[x_to_idx[x]][0] if a == 0 else theta_f[x_to_idx[x]][1]
                        for (x, a) in FX
                    )
                    self.assertEqual(recovered_f, f)

    def test_right_adjoint_preserves_limits(self):
        # Let diagram in D be a binary product of Y1 = (0, 1) and Y2 = (0,)
        Y1 = (0, 1)
        Y2 = (0,)
        # Product L = Y1 x Y2: ((0, 0), (1, 0))
        L = ((0, 0), (1, 0))
        pi1 = (0, 1)  # to Y1
        pi2 = (0, 0)  # to Y2

        # Right adjoint G(Y) = Y^A where A = (0, 1)
        G_L = self.G_obj(L)
        G_Y1 = self.G_obj(Y1)
        G_Y2 = self.G_obj(Y2)

        # Projections under G: G(pi1) : G(L) -> G(Y1), G(pi2) : G(L) -> G(Y2)
        G_pi1 = self.G_mor(pi1, L, Y1)
        G_pi2 = self.G_mor(pi2, L, Y2)

        # Verify that (G_L, G_pi1, G_pi2) is a limit cone of (G_Y1, G_Y2) in C:
        # For any object W in C, and any cone (h1, h2) with h1 : W -> G(Y1) and h2 : W -> G(Y2),
        # there must exist a UNIQUE u : W -> G(L) such that G(pi1) o u == h1 and G(pi2) o u == h2.
        gl_to_idx = {gl: idx for idx, gl in enumerate(G_L)}
        for W in self.objects:
            hom_W_GY1 = []
            if len(W) == 0:
                hom_W_GY1.append(())
            else:
                def make_h1(idx, cur):
                    if idx == len(W):
                        hom_W_GY1.append(tuple(cur))
                        return
                    for y in G_Y1:
                        cur.append(y)
                        make_h1(idx + 1, cur)
                        cur.pop()
                make_h1(0, [])

            hom_W_GY2 = []
            if len(W) == 0:
                hom_W_GY2.append(())
            else:
                def make_h2(idx, cur):
                    if idx == len(W):
                        hom_W_GY2.append(tuple(cur))
                        return
                    for y in G_Y2:
                        cur.append(y)
                        make_h2(idx + 1, cur)
                        cur.pop()
                make_h2(0, [])

            hom_W_GL = []
            if len(W) == 0:
                hom_W_GL.append(())
            else:
                def make_u(idx, cur):
                    if idx == len(W):
                        hom_W_GL.append(tuple(cur))
                        return
                    for gl in G_L:
                        cur.append(gl)
                        make_u(idx + 1, cur)
                        cur.pop()
                make_u(0, [])

            cones = [(h1, h2) for h1 in hom_W_GY1 for h2 in hom_W_GY2]

            factorization_map = {}
            for u in hom_W_GL:
                comp1 = tuple(G_pi1[gl_to_idx[ux]] for ux in u)
                comp2 = tuple(G_pi2[gl_to_idx[ux]] for ux in u)
                cone = (comp1, comp2)
                self.assertNotIn(cone, factorization_map, "Limit factorization must be unique")
                factorization_map[cone] = u

            for cone in cones:
                self.assertIn(cone, factorization_map, f"Cone {cone} not factorized through G(L)")

            self.assertEqual(len(hom_W_GL), len(cones))


class TestFiniteCategoryLimitsAndYonedaPreservation(unittest.TestCase):
    """Algorithmic verification of categorical limits (products, equalizers, pullbacks) and Yoneda limit preservation."""

    def setUp(self):
        # Finite category of sets and functions over domains S0=(), S1=(0,), S2=(0,1), S3=(0,1,2)
        self.objects = [(), (0,), (0, 1), (0, 1, 2)]
        self.hom = {}
        for X in self.objects:
            for Y in self.objects:
                funcs = []
                if len(X) == 0:
                    funcs.append(())
                elif len(Y) == 0:
                    pass
                else:
                    def make_f(idx, cur):
                        if idx == len(X):
                            funcs.append(tuple(cur))
                            return
                        for y in Y:
                            cur.append(y)
                            make_f(idx + 1, cur)
                            cur.pop()
                    make_f(0, [])
                self.hom[(X, Y)] = funcs

    def comp(self, f, g, X, Y, Z):
        # f : X -> Y, g : Y -> Z
        y_to_idx = {y: idx for idx, y in enumerate(Y)}
        return tuple(g[y_to_idx[f_x]] for f_x in f)

    def test_binary_products_and_yoneda_preservation(self):
        # Test product of A = (0, 1) and B = (0,)
        A = (0, 1)
        B = (0,)
        # Product object P = A x B has elements (0, 0), (1, 0)
        P = ((0, 0), (1, 0))

        # Projections pi_A : P -> A, pi_B : P -> B
        pi_A = (0, 1)  # (0, 0) -> 0, (1, 0) -> 1
        pi_B = (0, 0)  # (0, 0) -> 0, (1, 0) -> 0

        # For any object X, verify: Hom(X, A x B) ~= Hom(X, A) x Hom(X, B)
        for X in self.objects:
            hom_X_P = []
            if len(X) == 0:
                hom_X_P.append(())
            else:
                def make_p(idx, cur):
                    if idx == len(X):
                        hom_X_P.append(tuple(cur))
                        return
                    for p in P:
                        cur.append(p)
                        make_p(idx + 1, cur)
                        cur.pop()
                make_p(0, [])

            hom_X_A = self.hom[(X, A)]
            hom_X_B = self.hom[(X, B)]

            # Total cones from X to diagram (A, B)
            cones = [(fA, fB) for fA in hom_X_A for fB in hom_X_B]

            # Yoneda mapping: u in Hom(X, P) |-> (pi_A o u, pi_B o u)
            p_to_idx = {p: idx for idx, p in enumerate(P)}
            yoneda_map = {}
            for u in hom_X_P:
                comp_A = tuple(pi_A[p_to_idx[ux]] for ux in u)
                comp_B = tuple(pi_B[p_to_idx[ux]] for ux in u)
                cone = (comp_A, comp_B)
                self.assertNotIn(cone, yoneda_map, "Yoneda mapping must be injective")
                yoneda_map[cone] = u

            # Check surjectivity: every cone corresponds to a unique u
            for cone in cones:
                self.assertIn(cone, yoneda_map, f"Cone {cone} not represented by any u in Hom(X, P)")

            self.assertEqual(len(hom_X_P), len(cones))

    def test_equalizers_and_yoneda_preservation(self):
        # Parallel arrows f, g : A -> B
        A = (0, 1, 2)
        B = (0, 1)
        # f : (0, 1, 2) -> (0, 1), e.g. (0, 1, 0)
        # g : (0, 1, 2) -> (0, 1), e.g. (0, 0, 0)
        # Equalizer is subset where f(x) == g(x): x in {0, 2}
        f = (0, 1, 0)
        g = (0, 0, 0)

        E = (0, 2)
        # Inclusion e : E -> A: 0 |-> 0, 2 |-> 2
        e = (0, 2)

        # Check f o e == g o e
        a_to_idx = {a: idx for idx, a in enumerate(A)}
        fe = tuple(f[a_to_idx[ex]] for ex in e)
        ge = tuple(g[a_to_idx[ex]] for ex in e)
        self.assertEqual(fe, ge)

        # For any object X, Hom(X, E) ~= {h in Hom(X, A) | f o h == g o h}
        for X in self.objects:
            hom_X_E = []
            if len(X) == 0:
                hom_X_E.append(())
            else:
                def make_e(idx, cur):
                    if idx == len(X):
                        hom_X_E.append(tuple(cur))
                        return
                    for elem in E:
                        cur.append(elem)
                        make_e(idx + 1, cur)
                        cur.pop()
                make_e(0, [])

            # Compatible arrows h in Hom(X, A) such that f o h == g o h
            compatible_h = []
            for h in self.hom[(X, A)]:
                fh = tuple(f[a_to_idx[hx]] for hx in h)
                gh = tuple(g[a_to_idx[hx]] for hx in h)
                if fh == gh:
                    compatible_h.append(h)

            # Yoneda mapping: u in Hom(X, E) |-> e o u in Hom(X, A)
            e_to_idx = {el: idx for idx, el in enumerate(E)}
            yoneda_map = {}
            for u in hom_X_E:
                eu = tuple(e[e_to_idx[ux]] for ux in u)
                self.assertNotIn(eu, yoneda_map)
                yoneda_map[eu] = u

            for h in compatible_h:
                self.assertIn(h, yoneda_map)

            self.assertEqual(len(hom_X_E), len(compatible_h))

    def test_pullbacks_and_yoneda_preservation(self):
        # Cospan: f : A -> C, g : B -> C
        A = (0, 1)
        B = (0, 1)
        C = (0, 1)
        f = (0, 1)  # identity
        g = (1, 0)  # swap

        # Pullback P = A x_C B: pairs (a, b) such that f(a) == g(b)
        # f(0)=0 == g(1)=0 => (0, 1)
        # f(1)=1 == g(0)=1 => (1, 0)
        P = ((0, 1), (1, 0))
        p1 = (0, 1)  # projection to A
        p2 = (1, 0)  # projection to B

        # Verify commutativity: f o p1 == g o p2
        c_to_idx = {c: idx for idx, c in enumerate(C)}
        a_to_idx = {a: idx for idx, a in enumerate(A)}
        b_to_idx = {b: idx for idx, b in enumerate(B)}
        fp1 = tuple(f[a_to_idx[p]] for p in p1)
        gp2 = tuple(g[b_to_idx[p]] for p in p2)
        self.assertEqual(fp1, gp2)

        # For any object X, Hom(X, P) ~= { (h1, h2) in Hom(X, A) x Hom(X, B) | f o h1 == g o h2 }
        for X in self.objects:
            hom_X_P = []
            if len(X) == 0:
                hom_X_P.append(())
            else:
                def make_p(idx, cur):
                    if idx == len(X):
                        hom_X_P.append(tuple(cur))
                        return
                    for elem in P:
                        cur.append(elem)
                        make_p(idx + 1, cur)
                        cur.pop()
                make_p(0, [])

            compatible_cones = []
            for h1 in self.hom[(X, A)]:
                for h2 in self.hom[(X, B)]:
                    fh1 = tuple(f[a_to_idx[hx]] for hx in h1)
                    gh2 = tuple(g[b_to_idx[hx]] for hx in h2)
                    if fh1 == gh2:
                        compatible_cones.append((h1, h2))

            # Yoneda mapping: u in Hom(X, P) |-> (p1 o u, p2 o u)
            p_to_idx = {p: idx for idx, p in enumerate(P)}
            yoneda_map = {}
            for u in hom_X_P:
                comp1 = tuple(p1[p_to_idx[ux]] for ux in u)
                comp2 = tuple(p2[p_to_idx[ux]] for ux in u)
                cone = (comp1, comp2)
                self.assertNotIn(cone, yoneda_map)
                yoneda_map[cone] = u

            for cone in compatible_cones:
                self.assertIn(cone, yoneda_map)

            self.assertEqual(len(hom_X_P), len(compatible_cones))


if __name__ == "__main__":
    unittest.main()
