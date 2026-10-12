"""Exact checks for "Random-cluster measures with 0 < q < 1 are not monotone in p".

    python checks.py

Needs Python 3.9+ and sympy (parts D and E). Every numerical inequality stated in the paper is checked here in
exact rational arithmetic; floating point is used only in part C, for the sanity checks of Theorem 1.2, and for
the printed decimals.

A  Lemma 2.1 (theta graphs): brute force over all edge sets against the closed form.
B  Table 1: the three witnesses, by the closed form and by a second route (path sums by enumeration, then a
   two-state recursion over the paths), with the comparison bounds p <= phi <= p/(p+q(1-p)).
C  Theorem 1.2: q_l, the derivative identity of Section 3 against finite differences, and float scans.
D  The arboreal gas on the ten-edge graph Theta(2,2,2,3): forest counts, the derivative numerator, beta*,
   P_20 > P_25, and the uniform-forest layers 5/14 > 6/17.
E  Theorem 1.3(c): the random-cluster measure on the ten-edge graph for 0 < q <= 1/40000 (and 1/32618), from a
   polynomial obtained by enumerating all 1024 edge sets.
F  Proposition 1.4 (cacti): the product structure, by brute force on a small cactus.
G  Section 6 (q -> 0 at fixed p): the limiting edge odds on theta graphs, brute force and monotonicity.
"""
from fractions import Fraction as F
from math import exp, log
import sys

FAILS = []


def check(cond, msg):
    if not cond:
        FAILS.append(msg)
        print("FAIL:", msg)


# ----------------------------------------------------------------------------------------------------------------
# graphs and brute force

def theta_graph(lengths):
    """Vertices 0 = u and 1 = v. Edge 0 is e = uv; then one u-v path of each given length (>= 2)."""
    edges = [(0, 1)]
    nv = 2
    for l in lengths:
        prev = 0
        for _ in range(l - 1):
            edges.append((prev, nv))
            prev = nv
            nv += 1
        edges.append((prev, 1))
    return nv, edges


def n_components(nv, edges, mask):
    par = list(range(nv))

    def find(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a

    k = nv
    for i, (a, b) in enumerate(edges):
        if mask >> i & 1:
            ra, rb = find(a), find(b)
            if ra != rb:
                par[ra] = rb
                k -= 1
    return k


def popcount(m):
    return bin(m).count("1")


def fk_brute(nv, edges, x, q):
    """(Z with edge 0 open, Z with edge 0 closed) for the weights x^|w| q^k(w)."""
    zo = zc = 0
    for mask in range(1 << len(edges)):
        w = x ** popcount(mask) * q ** n_components(nv, edges, mask)
        if mask & 1:
            zo += w
        else:
            zc += w
    return zo, zc


# ----------------------------------------------------------------------------------------------------------------
# Lemma 2.1 and the second route

def V_path(l, x, q):
    return q / ((1 + q / x) ** l - 1)


def theta_odds(lengths, x, q):
    R = 1
    for l in lengths:
        R *= 1 + V_path(l, x, q)
    return x * R / (R - 1 + q)


_PATH_CACHE = {}


def path_sums(l, x, q):
    """Enumerate the 2^l states of a u-v path of length l. Returns (sum over the full state, sum over the others) of
    x^(open edges) q^(components containing neither u nor v)."""
    key = (l, x, q)
    if key not in _PATH_CACHE:
        nv, edges = l + 1, [(i, i + 1) for i in range(l)]
        full = nonfull = 0
        for mask in range(1 << l):
            k = n_components(nv, edges, mask)
            if mask == (1 << l) - 1:
                full += x ** l
            else:
                nonfull += x ** popcount(mask) * q ** (k - 2)
        _PATH_CACHE[key] = (full, nonfull)
    return _PATH_CACHE[key]


def theta_odds_dp(lengths, x, q):
    conn, disc = 0, 1  # weight of the paths seen so far, split by whether a full path joins u and v
    for l in lengths:
        full, nonfull = path_sums(l, x, q)
        conn, disc = conn * (full + nonfull) + disc * full, disc * nonfull
    zo = x * q * (conn + disc)
    zc = q * conn + q * q * disc
    return zo / zc


def prob(odds):
    return odds / (1 + odds)


# ----------------------------------------------------------------------------------------------------------------
def part_A():
    cases = [(2,), (3,), (2, 2), (2, 3), (2, 2, 2), (3, 3), (2, 2, 2, 2), (2, 2, 2, 3), (4, 4), (2, 2, 2, 2, 2),
             (3, 3, 3), (5, 5), (2, 3, 4), (6, 6)]
    pts = [(F(1, 3), F(1, 2)), (F(2, 7), F(1, 10)), (F(5, 2), F(3, 4)), (F(1, 50), F(1, 1000)), (F(7, 3), F(9, 10)),
           (F(3, 2), F(5, 3))]
    n = 0
    for L in cases:
        nv, edges = theta_graph(L)
        for x, q in pts:
            zo, zc = fk_brute(nv, edges, x, q)
            check(zo / zc == theta_odds(L, x, q), "Lemma 2.1 closed form %s %s %s" % (L, x, q))
            check(zo / zc == theta_odds_dp(L, x, q), "second route %s %s %s" % (L, x, q))
            n += 1
    print("A  Lemma 2.1: brute force = closed form = second route on %d (graph, x, q) cases" % n)


WITNESSES = [  # q, l, m, p1, p2
    (F(1, 10), 4, 13, F(461, 3586), F(539, 3664)),
    (F(1, 4), 7, 27, F(5831, 18331), F(6419, 18919)),
    (F(1, 2), 10, 388, F(6461, 16461), F(6539, 16539)),
]


def q_l(l):
    return 1 - exp(1 - 1 / l) / l


def part_B():
    print("B  Table 1")
    for q, l, m, p1, p2 in WITNESSES:
        L = (l,) * m
        x1, x2 = p1 / (1 - p1), p2 / (1 - p2)
        o1, o2 = theta_odds(L, x1, q), theta_odds(L, x2, q)
        check(o1 == theta_odds_dp(L, x1, q) and o2 == theta_odds_dp(L, x2, q), "second route, witness q=%s" % q)
        f1, f2 = prob(o1), prob(o2)
        check(0 < p1 < p2 < 1, "p1 < p2 at q=%s" % q)
        check(f1 > f2, "drop at q=%s" % q)
        for p, f in ((p1, f1), (p2, f2)):
            check(p <= f <= p / (p + q * (1 - p)), "comparison bounds at q=%s" % q)
            check(p / (p + q * (1 - p)) - p >= F(17, 100), "comparison interval of length at least 0.17 at q=%s" % q)
        check(float(q) < q_l(l), "q < q_l at q=%s" % q)
        print("   q=%s  Theta(%d^%d)  edges=%d  vertices=%d  x1=%s x2=%s  p1=%.6f p2=%.6f  phi1=%.9f phi2=%.9f"
              "  drop=%.3e  q_l=%.4f" % (q, l, m, 1 + l * m, 2 + (l - 1) * m, x1, x2, float(p1), float(p2),
                                         float(f1), float(f2), float(f1 - f2), q_l(l)))


# ----------------------------------------------------------------------------------------------------------------
def dlogO_dlogx(l, m, x, q):
    """d log O / d log x on Theta(l^m), from the identity of Section 3."""
    t = q / x
    V = q / ((1 + t) ** l - 1)
    kappa = t * (1 + t) ** (l - 1) / ((1 + t) ** l - 1)
    R = exp(min(m * log(1 + V), 700.0))  # beyond e^700 the second term is below 1e-290
    rho = m * V / (1 + V) * l * kappa
    return 1 - rho * (1 - q) / (R - 1 + q)


def part_C():
    print("C  Theorem 1.2")
    print("   q_l:", ", ".join("q_%d=%.5f" % (l, q_l(l)) for l in (2, 3, 4, 5, 7, 10, 20, 100)))
    check(all(q_l(l) < q_l(l + 1) for l in range(2, 400)) and q_l(10 ** 6) > 0.99999, "q_l increases to 1")
    # the identity against a centred finite difference of log O computed from the closed form
    for l, m, x, q in ((2, 7, 0.3, 0.1), (4, 13, 0.16, 0.1), (3, 40, 0.05, 0.3), (10, 388, 0.65, 0.5)):
        h = 1e-6
        num = (log(float(theta_odds((l,) * m, x * exp(h), q))) - log(float(theta_odds((l,) * m, x * exp(-h), q))))
        num /= 2 * h
        check(abs(num - dlogO_dlogx(l, m, x, q)) < 1e-6, "derivative identity %s" % ((l, m, x, q),))
    # above q_l: no decrease for any m on a grid; below q_l: a decrease appears for some m
    xs = [10 ** (k / 40) for k in range(-400, 121)]
    ms = sorted(set([1, 2, 3, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000, 10 ** 5, 10 ** 6, 10 ** 7]))
    for l in (2, 3, 5, 10):
        qa = q_l(l) * (1 + 1e-3)
        neg = [(m, x) for m in ms for x in xs if dlogO_dlogx(l, m, x, qa) <= 0]
        check(not neg, "above q_%d no decrease (%d grid points fail)" % (l, len(neg)))
        qb = q_l(l) / 2  # m grows very fast as q approaches q_l (Section 3), so the scan stays well below it
        found = next((m for m in ms if any(dlogO_dlogx(l, m, x, qb) < 0 for x in xs)), None)
        check(found is not None, "below q_%d a decrease appears" % l)
        print("   l=%d: at q=1.001 q_l no decrease on the grid (m<=1e7); at q=q_l/2 a decrease for m=%s" % (l, found))


# ----------------------------------------------------------------------------------------------------------------
TEN = (2, 2, 2, 3)


def part_D():
    import sympy as sp
    print("D  arboreal gas on Theta(2,2,2,3)")
    nv, edges = theta_graph(TEN)
    check((nv, len(edges)) == (7, 10), "ten-edge graph has 7 vertices and 10 edges")
    D = [0] * nv
    N = [0] * nv
    for mask in range(1 << len(edges)):
        s = popcount(mask)
        if n_components(nv, edges, mask) == nv - s:  # a forest
            D[s] += 1
            if mask & 1:
                N[s] += 1
    print("   forests by size D_r =", D, " containing e N_r =", N)
    check(D == [1, 10, 45, 117, 185, 168, 68] and N == [0, 1, 9, 33, 62, 60, 24], "forest counts")
    check(F(N[5], D[5]) == F(5, 14) and F(N[6], D[6]) == F(6, 17) and F(5, 14) - F(6, 17) == F(1, 238),
          "uniform forest layers")
    b = sp.symbols("b", positive=True)
    Np = sum(c * b ** r for r, c in enumerate(N))
    Dp = sum(c * b ** r for r, c in enumerate(D))

    def c_l(l, y):
        return y ** l / ((1 + y) ** l - y ** l)

    g = b / (1 + sum(c_l(l, b) for l in TEN))
    check(sp.simplify(g / (1 + g) - Np / Dp) == 0, "arboreal closed form = forest count")
    num = sp.expand(sp.diff(Np, b) * Dp - Np * sp.diff(Dp, b))
    target = -(1 + 2 * b) ** 4 * (3 * b ** 6 - 34 * b ** 5 - 85 * b ** 4 - 82 * b ** 3 - 40 * b ** 2 - 10 * b - 1)
    check(sp.expand(num - target) == 0, "derivative numerator")
    sextic = sp.Poly(3 * b ** 6 - 34 * b ** 5 - 85 * b ** 4 - 82 * b ** 3 - 40 * b ** 2 - 10 * b - 1, b)
    pos = [r for r in sp.real_roots(sextic) if r > 0]
    check(len(pos) == 1, "one positive root")
    bstar = float(pos[0].evalf(30))
    check(sextic.eval(sp.Rational(1357, 100)) < 0 < sextic.eval(sp.Rational(1358, 100)), "beta* in (13.57,13.58)")
    print("   P(e) = N(b)/D(b); numerator of its derivative = %s" % sp.factor(num))
    print("   beta* = %.10f (unique positive root of the sextic)" % bstar)

    def P(y):
        return F(sum(c * y ** r for r, c in enumerate(N)), sum(c * y ** r for r, c in enumerate(D)))

    check(P(20) > P(25), "P_20 > P_25")
    check(P(13) < P(F(27, 2)) and P(14) > P(15), "increasing before beta*, decreasing after")
    print("   P_20 = %s = %.9f,  P_25 = %s = %.9f,  limit 6/17 = %.9f" % (P(20), float(P(20)), P(25), float(P(25)),
                                                                        6 / 17))


def part_E():
    import sympy as sp
    print("E  random-cluster measure on Theta(2,2,2,3) for small q")
    nv, edges = theta_graph(TEN)
    q = sp.symbols("q", positive=True)
    rows = [(popcount(mask), n_components(nv, edges, mask), mask & 1) for mask in range(1 << len(edges))]

    def Z(y):  # x = y q, weights x^|w| q^k = y^|w| q^(|w|+k)
        zo = sum(y ** s * q ** (s + k) for s, k, o in rows if o)
        zc = sum(y ** s * q ** (s + k) for s, k, o in rows if not o)
        return sp.expand(zo), sp.expand(zc)

    for y1, y2, q0 in ((sp.Integer(20), sp.Integer(25), sp.Rational(1, 40000)),
                       (sp.Rational(512, 25), sp.Rational(2049, 100), sp.Rational(1, 32618))):
        zo1, zc1 = Z(y1)
        zo2, zc2 = Z(y2)
        Dq = sp.Poly(sp.expand(zo1 * zc2 - zo2 * zc1), q)
        coeffs = Dq.all_coeffs()[::-1]  # constant first
        low = next(i for i, c in enumerate(coeffs) if c != 0)
        H = coeffs[low:]
        signs = "".join("+" if c > 0 else ("-" if c < 0 else "0") for c in H)
        ok_pattern = H[0] > 0 and all(c <= 0 for c in H[1:])
        val = sum(c * q0 ** i for i, c in enumerate(H))
        check(ok_pattern and val > 0, "H sign pattern and H(q0) > 0 for y=(%s,%s)" % (y1, y2))
        try:
            roots = [r for r in sp.Poly(sum(c * q ** i for i, c in enumerate(H)), q).nroots(n=30, maxsteps=200)
                     if r.is_real and r > 0]
        except Exception:  # the root is only printed; the claim rests on the sign pattern and H(q0)
            roots = []
        print("   y=(%s,%s): D(q) = q^%d H(q), deg H = %d, signs %s, H(%s) > 0; positive root of H = %s (1/%.3f)" % (
            y1, y2, low, len(H) - 1, signs, q0, sp.N(roots[0], 12) if roots else None,
            float(1 / roots[0]) if roots else float("nan")))
        # one point by the closed form as well
        qq = F(q0.p, q0.q)
        o1 = theta_odds(TEN, F(y1.p, y1.q) * qq, qq)
        o2 = theta_odds(TEN, F(y2.p, y2.q) * qq, qq)
        check(prob(o1) > prob(o2), "closed form agrees at q0")


# ----------------------------------------------------------------------------------------------------------------
def part_F():
    print("F  cactus")
    # triangle 0-1-2, square 2-3-4-5, bridge 5-6, triangle 6-7-8, bridge 0-9
    cycles = [[(0, 1), (1, 2), (2, 0)], [(2, 3), (3, 4), (4, 5), (5, 2)], [(6, 7), (7, 8), (8, 6)]]
    bridges = [(5, 6), (0, 9)]
    edges = [e for c in cycles for e in c] + bridges
    nv = 10
    for p, q in ((F(1, 3), F(1, 7)), (F(3, 5), F(1, 2)), (F(1, 10), F(3, 4))):
        x = p / (1 - p)
        w = x / q
        brute = {}
        prod = {}
        for mask in range(1 << len(edges)):
            s = popcount(mask)
            brute[mask] = x ** s * q ** n_components(nv, edges, mask)
            val = w ** s
            pos = 0
            for c in cycles:
                if all(mask >> (pos + j) & 1 for j in range(len(c))):
                    val *= q
                pos += len(c)
            prod[mask] = val
        zb, zp = sum(brute.values()), sum(prod.values())
        check(all(brute[mk] / zb == prod[mk] / zp for mk in brute), "cactus product form at p=%s q=%s" % (p, q))
        # bridges: probability w/(1+w) = p/(p+q(1-p))
        i = len(edges) - 1
        pb = sum(v for mk, v in brute.items() if mk >> i & 1) / zb
        check(pb == p / (p + q * (1 - p)), "bridge marginal")
    print("   measure = product over blocks, bridges Bernoulli(p/(p+q(1-p))), on 3 (p, q) points")


def part_G():
    print("G  q -> 0 at fixed p on theta graphs")
    # limiting measure: x^|w| on spanning connected subgraphs; odds of e = x R0/(R0-1), R0 = prod(1+x/l)
    for L in ((2, 2, 2, 3), (3, 3, 3), (2, 2, 2, 2, 2), (4, 4), (2, 5)):
        nv, edges = theta_graph(L)
        for x in (F(1, 3), F(2), F(7, 5)):
            zo = sum(x ** popcount(mk) for mk in range(1 << len(edges))
                     if n_components(nv, edges, mk) == 1 and mk & 1)
            zc = sum(x ** popcount(mk) for mk in range(1 << len(edges))
                     if n_components(nv, edges, mk) == 1 and not mk & 1)
            R0 = 1
            for l in L:
                R0 *= 1 + x / l
            check(zo / zc == x * R0 / (R0 - 1), "q=0 odds %s %s" % (L, x))
    grid = [F(k, 20) for k in range(1, 400)]
    for L in ((2,) * 50, (10,) * 300, (2, 2, 2, 3), (3, 7, 50, 50)):
        def odds0(x):
            R0 = 1
            for l in L:
                R0 *= 1 + x / l
            return x * R0 / (R0 - 1)
        vals = [odds0(x) for x in grid]
        check(all(a < b for a, b in zip(vals, vals[1:])), "q=0 odds increasing on %s" % (L[:4],))
    print("   limiting odds x R0/(R0-1) match brute force and increase on the grid")


if __name__ == "__main__":
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    part_G()
    print("ALL CHECKS PASS" if not FAILS else "%d FAILURES" % len(FAILS))
    sys.exit(1 if FAILS else 0)
