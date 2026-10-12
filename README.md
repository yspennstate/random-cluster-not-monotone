# Random-cluster measures with 0 < q < 1 are not monotone in p

Companion material for the paper of the same title (Y. Shmalo, October 2026). [Read the paper](paper/main.pdf).

For q ≥ 1 the random-cluster measure on a finite graph is stochastically increasing in the edge parameter p. The
paper shows that for every q in (0,1) there are a finite graph G, an edge e and p1 < p2 with
φ_{G,p1,q}(e open) > φ_{G,p2,q}(e open), so the measures (φ_{G,p,q}), 0 ≤ p ≤ 1, admit no monotone coupling. This
answers Question 13.2 of G. Pete, *Probability and Geometry on Groups*, in the negative for 0 < q < 1.

The graphs are theta graphs: an edge e = uv together with m internally disjoint paths from u to v. When all paths
have length l, the probability that e is open fails to be increasing in p for all large m exactly when
q < 1 − e^(1−1/l)/l. For the arboreal gas (the limit q → 0 with p/(1−p) = βq) the same computation gives a criterion
in terms of the path lengths; the smallest theta graph satisfying it has ten edges, and on it the probability of e
increases up to β* ≈ 13.574 and decreases after. If every edge of G lies in at most one cycle, a monotone coupling
exists for every q > 0.

## Contents

- `paper/` the LaTeX source and the compiled PDF.
- `code/checks.py` exact rational checks of the computations in the paper: the closed form of Lemma 2.1 against
  enumeration of all configurations, the three witnesses of Table 1 with their comparison bounds, the derivative
  formula of Lemma 3.1, the forest polynomials of Section 4, the product form of Section 5 and the limit q → 0 of
  Section 6. `code/checks.out` is its output.
- `lean/RandomCluster.lean` ten finite certificates closed by `decide +kernel`, so the Lean kernel itself evaluates
  the enumerations and the integer arithmetic. It uses the core library only (no Mathlib). `lean/RandomCluster.out`
  is the output, with the axioms each theorem depends on.

## Reproducing

    python code/checks.py

needs Python 3.9 or later and sympy, and takes a few seconds. For the Lean file, install the version
pinned in `lean/lean-toolchain` (Lean 4.33.1) and run

    cd lean
    lean RandomCluster.lean

which takes a few minutes. A successful run prints only the `#print axioms` lines at the end of the file.
