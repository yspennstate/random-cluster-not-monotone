/-
Finite certificates for "Random-cluster measures with 0 < q < 1 are not monotone in p".

Core Lean 4, no Mathlib. Every theorem is closed by `decide +kernel`: the kernel itself evaluates the enumeration
or the integer arithmetic, so nothing rests on compiled code.

Contents.
* The ten-edge graph Theta(2,2,2,3) (Section 4 of the paper), by enumeration of all 1024 edge sets:
  - `forest_counts`: the numbers of forests of each size, and of those containing e;
  - `uniform_forest_layers`: 60/168 > 24/68, i.e. 5/14 > 6/17;
  - `arboreal_drop`: P_20(e in F) > P_25(e in F) for the arboreal gas;
  - `arboreal_derivative`: the numerator of d/db (N/D) is -(1+2b)^4 S(b), and S changes sign on (13.57, 13.58);
  - `fk_small_q`: the polynomial H(q) of Theorem 1.3(c) has H_0 > 0, H_i <= 0 for i >= 1, and H(1/40000) > 0;
  - `fk_point`: the random-cluster inequality itself at q = 1/40000;
  - `closed_form_agrees`: Lemma 2.1 against the enumeration at one point of this graph.
* Table 1 (Section 1), from the closed form of Lemma 2.1 in integer form:
  - `table_q_tenth`, `table_q_quarter`, `table_q_half`.
-/

namespace RandomCluster

/-! ## The ten-edge graph -/

/-- Theta(2,2,2,3) on the vertices 0..6; edge 0 is e = {0,1}, then three paths of length 2 and one of length 3. -/
def tenEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (2, 1), (0, 3), (3, 1), (0, 4), (4, 1), (0, 5), (5, 6), (6, 1)]

def nV : Nat := 7
def nE : Nat := 10

def relabel (lab : List Nat) (old new : Nat) : List Nat :=
  lab.map fun l => if l == old then new else l

/-- Label propagation along the edges of `mask`; every class keeps the label of one of its vertices. -/
def labels (mask : Nat) : List Nat :=
  (tenEdges.foldl
    (fun (st : List Nat × Nat) (ab : Nat × Nat) =>
      let lab := st.1
      let la := lab.getD ab.1 0
      let lb := lab.getD ab.2 0
      (if mask.testBit st.2 && la != lb then relabel lab lb la else lab, st.2 + 1))
    (List.range nV, 0)).1

/-- Number of connected components of (V, omega), omega = the edges i with bit i of `mask` set. -/
def comps (mask : Nat) : Nat :=
  let lab := labels mask
  ((List.range nV).filter fun v => lab.getD v 0 == v).length

def size (mask : Nat) : Nat :=
  ((List.range nE).filter fun i => mask.testBit i).length

/-- Cycle rank |omega| - |V| + k(omega). -/
def cycleRank (mask : Nat) : Nat := size mask + comps mask - nV

def masks : List Nat := List.range (2 ^ nE)

def addAt : List Int → Nat → Int → List Int
  | [], _, _ => []
  | a :: as, 0, c => (a + c) :: as
  | a :: as, n + 1, c => a :: addAt as n c

def polyAdd : List Int → List Int → List Int
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: polyAdd p q

def polyNeg (p : List Int) : List Int := p.map fun a => -a

def polyMul : List Int → List Int → List Int
  | [], _ => []
  | a :: p, q => polyAdd (q.map fun b => a * b) (0 :: polyMul p q)

def polyDeriv (p : List Int) : List Int :=
  ((p.zip (List.range p.length)).map fun (c, i) => c * (i : Int)).drop 1

/-- `N ^ (length - 1)` times the value of the polynomial `p` at `a / N`. -/
def evalScaled (p : List Int) (a N : Int) : Int :=
  ((p.zip (List.range p.length)).map fun (c, i) => c * a ^ i * N ^ (p.length - 1 - i)).foldl (· + ·) 0

/-! ### The arboreal gas -/

/-- Number of forests of each size 0..6, all of them (`eOpen = false` and `true` added) or only those
with e open / e closed. -/
def forestCount (eOpen : Bool) : List Int :=
  masks.foldl (fun acc m =>
    if comps m + size m == nV && m.testBit 0 == eOpen then addAt acc (size m) 1 else acc)
    (List.replicate nV 0)

def forestAll : List Int := polyAdd (forestCount true) (forestCount false)

theorem forest_counts :
    forestAll = [1, 10, 45, 117, 185, 168, 68] ∧ forestCount true = [0, 1, 9, 33, 62, 60, 24] := by
  decide +kernel

/-- Uniform forests with 5 edges against uniform spanning trees (6 edges): 60/168 > 24/68. -/
theorem uniform_forest_layers :
    (forestCount true).getD 5 0 * forestAll.getD 6 0 > (forestCount true).getD 6 0 * forestAll.getD 5 0 := by
  decide +kernel

/-- Forest sums with e open / closed at an integer fugacity. -/
def forestZ (b : Int) (eOpen : Bool) : Int := evalScaled (forestCount eOpen) b 1

theorem arboreal_drop :
    forestZ 20 true * forestZ 25 false > forestZ 25 true * forestZ 20 false ∧
    forestZ 25 false > 0 ∧ forestZ 20 false > 0 := by
  decide +kernel

def sextic : List Int := [-1, -10, -40, -82, -85, -34, 3]

/-- (N'D - N D') = -(1+2b)^4 S(b) with N, D the forest polynomials, and S(13.57) < 0 < S(13.58). -/
theorem arboreal_derivative :
    (polyAdd
      (polyAdd (polyMul (polyDeriv (forestCount true)) forestAll)
        (polyNeg (polyMul (forestCount true) (polyDeriv forestAll))))
      (polyMul (polyMul (polyMul [1, 2] [1, 2]) (polyMul [1, 2] [1, 2])) sextic)).all (· == 0) ∧
    evalScaled sextic 1357 100 < 0 ∧ evalScaled sextic 1358 100 > 0 := by
  decide +kernel

/-! ### The random-cluster measure with x = y q

With p / (1 - p) = y q, the weight x^|omega| q^k(omega) equals q^|V| y^|omega| q^c(omega), c the cycle rank, so
phi_{p,q}(e open) = Zo / (Zo + Zc) with Zo, Zc the polynomials in q below. -/

def fkPoly (y : Int) (eOpen : Bool) : List Int :=
  masks.foldl (fun acc m =>
    if m.testBit 0 == eOpen then addAt acc (cycleRank m) (y ^ size m) else acc)
    (List.replicate 5 0)

/-- H(q) = Zo(20) Zc(25) - Zo(25) Zc(20): phi(p1) - phi(p2) has the sign of H(q). -/
def Hpoly : List Int :=
  polyAdd (polyMul (fkPoly 20 true) (fkPoly 25 false)) (polyNeg (polyMul (fkPoly 25 true) (fkPoly 20 false)))

theorem fk_small_q :
    Hpoly.length = 9 ∧ Hpoly.getD 0 0 > 0 ∧ (Hpoly.drop 1).all (· ≤ 0) ∧ evalScaled Hpoly 1 40000 > 0 := by
  decide +kernel

/-- Integer form of the partition functions at x = y/N, q = 1/N: the sum over edge sets with e open (closed) of
y^|omega| N^((|E| - |omega|) + (|V| - k(omega))), which is N^(|E|+|V|) times the sum of x^|omega| q^k(omega). -/
def fkZ (y N : Nat) (eOpen : Bool) : Nat :=
  masks.foldl (fun acc m =>
    if m.testBit 0 == eOpen then acc + y ^ size m * N ^ ((nE - size m) + (nV - comps m)) else acc) 0

theorem fk_point :
    fkZ 20 40000 true * fkZ 25 40000 false > fkZ 25 40000 true * fkZ 20 40000 false := by
  decide +kernel

/-! ## The closed form of Lemma 2.1 in integer form

For x = a/b and q = 1/N, a path of length l contributes A = x^l (all edges open) and
B = ((x+q)^l - x^l)/q (otherwise). With S = b^l N^(l-1): A S = a^l N^(l-1) and B S = (aN+b)^l - (aN)^l.
Multiplying Zo = x q prod(A+B) and Zc = q prod(A+B) - q(1-q) prod B by N^2 b prod S gives the two values below;
the common positive factor does not change Zo/Zc. -/

def Ap (a N l : Nat) : Int := (a : Int) ^ l * (N : Int) ^ (l - 1)
def Bp (a b N l : Nat) : Int := ((a * N + b : Nat) : Int) ^ l - ((a * N : Nat) : Int) ^ l

def zoCF (a b N : Nat) (ls : List Nat) : Int :=
  (N : Int) * a * (ls.map fun l => Ap a N l + Bp a b N l).foldl (· * ·) 1

def zcCF (a b N : Nat) (ls : List Nat) : Int :=
  (N : Int) * b * (ls.map fun l => Ap a N l + Bp a b N l).foldl (· * ·) 1
    - ((N : Int) - 1) * b * (ls.map fun l => Bp a b N l).foldl (· * ·) 1

theorem closed_form_agrees :
    (fkZ 20 40000 true : Int) * zcCF 20 40000 40000 [2, 2, 2, 3]
      = zoCF 20 40000 40000 [2, 2, 2, 3] * (fkZ 20 40000 false : Int) := by
  decide +kernel

/-- phi(x1) > phi(x2) with x1 < x2, written as Zo(x1) Zc(x2) > Zo(x2) Zc(x1) with all four values positive. -/
def drop (a1 a2 b N : Nat) (ls : List Nat) : Prop :=
  a1 < a2 ∧ zoCF a1 b N ls > 0 ∧ zcCF a1 b N ls > 0 ∧ zoCF a2 b N ls > 0 ∧ zcCF a2 b N ls > 0 ∧
    zoCF a1 b N ls * zcCF a2 b N ls > zoCF a2 b N ls * zcCF a1 b N ls

instance (a1 a2 b N : Nat) (ls : List Nat) : Decidable (drop a1 a2 b N ls) := by
  unfold drop; infer_instance

/-- q = 1/10, Theta(4^13): x1 = 461/3125, x2 = 539/3125. -/
theorem table_q_tenth : drop 461 539 3125 10 (List.replicate 13 4) := by decide +kernel

/-- q = 1/4, Theta(7^27): x1 = 5831/12500, x2 = 6419/12500. -/
theorem table_q_quarter : drop 5831 6419 12500 4 (List.replicate 27 7) := by decide +kernel

/-- q = 1/2, Theta(10^388): x1 = 6461/10000, x2 = 6539/10000. -/
theorem table_q_half : drop 6461 6539 10000 2 (List.replicate 388 10) := by decide +kernel

end RandomCluster

#print axioms RandomCluster.forest_counts
#print axioms RandomCluster.uniform_forest_layers
#print axioms RandomCluster.arboreal_drop
#print axioms RandomCluster.arboreal_derivative
#print axioms RandomCluster.fk_small_q
#print axioms RandomCluster.fk_point
#print axioms RandomCluster.closed_form_agrees
#print axioms RandomCluster.table_q_tenth
#print axioms RandomCluster.table_q_quarter
#print axioms RandomCluster.table_q_half
