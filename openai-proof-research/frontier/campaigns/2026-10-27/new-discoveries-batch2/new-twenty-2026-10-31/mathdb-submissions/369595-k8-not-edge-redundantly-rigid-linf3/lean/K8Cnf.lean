import RupCore

/-!
# The propositional instance for `K₈` in `ℓ∞³`, defined by clause provenance

Vertices are `0, …, 7`, coordinates (colours) are `0, 1, 2`.  The 28 edges
`(u, v)` with `u < v` are numbered `edgeIdx u v` in lexicographic order.

Variables (DIMACS numbering, literals encoded as in `RupCore`):
* `colVar u v c = 1 + 3 * edgeIdx u v + c` — "the edge `uv` has colour `c`",
  i.e. coordinate `c` is the unique coordinate of largest absolute value of
  `p v - p u`;
* `sgnVar u v = 85 + edgeIdx u v` — "`p u c < p v c` in the colour `c` of `uv`".

Every clause of the instance is described by a provenance record `Prov`; the
record determines the clause by the computable function `Prov.clause`, and the
decidable predicate `Prov.valid` says which records belong to the instance.
The instance is the set of clauses of valid records; `Base α` says that the
assignment `α` satisfies all of them.  The certificate modules use only finitely
many valid records; each is checked by kernel evaluation.
-/

namespace K8

open Rup

def edgeIdx (u v : Nat) : Nat := u * (15 - u) / 2 + (v - u - 1)

def colVar (u v c : Nat) : Nat := 1 + 3 * edgeIdx (min u v) (max u v) + c

def sgnVar (u v : Nat) : Nat := 85 + edgeIdx (min u v) (max u v)

def pos (x : Nat) : Nat := 2 * x

def neg (x : Nat) : Nat := 2 * x + 1

/-- The 28 pairs `(u, v)`, `u < v < 8`, in lexicographic order. -/
def pairs : List (Nat × Nat) :=
  (List.range 8).flatMap fun u => ((List.range 8).filter fun v => u < v).map fun v => (u, v)

/-- The six pairs of `K₄` in lexicographic order. -/
def e4 : List (Nat × Nat) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The six permutations of `{0, 1, 2}` as lists of images. -/
def perms3 : List (List Nat) :=
  [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

/-- The seven forbidden signed patterns on four points.  An entry `(i, c, s)`
says that the `i`-th pair `(a, b)` of `K₄` has colour `c`, and that
`q b c - q a c` is positive (`s = true`) or negative (`s = false`). -/
def reps : List (List (Nat × Nat × Bool)) :=
  [ [(0, 0, false), (1, 0, true), (3, 0, false)],
    [(0, 0, false), (1, 0, true), (3, 1, false)],
    [(0, 0, false), (1, 0, true), (4, 0, false), (5, 0, true)],
    [(0, 0, false), (1, 0, true), (4, 0, false), (5, 1, false)],
    [(0, 0, false), (1, 0, true), (4, 1, false), (5, 1, true)],
    [(0, 0, false), (1, 1, false), (4, 1, true), (5, 0, true)],
    [(0, 0, false), (1, 1, false), (2, 2, false), (3, 2, false), (4, 1, true), (5, 0, false)] ]

/-- The eleven anchor (symmetry-breaking) unit literals. -/
def anchors : List Nat :=
  [pos (colVar 0 1 0), pos (colVar 0 2 0), pos (colVar 0 3 0), pos (colVar 0 4 1),
   pos (colVar 0 5 1), pos (colVar 0 6 2), pos (colVar 0 7 2),
   pos (sgnVar 0 1), pos (sgnVar 0 2), pos (sgnVar 0 4), pos (sgnVar 0 6)]

/-- Clause provenance records. -/
inductive Prov where
  /-- the edge `uv` has some colour -/
  | alo (u v : Nat)
  /-- the edge `uv` does not have both colours `a` and `b` -/
  | amo (u v a b : Nat)
  /-- the cut `(S, V ∖ S)` (bit mask `S`) has a crossing edge of colour `k`
  other than `uv` -/
  | cut (S k u v : Nat)
  /-- the image of representative pattern `r` under the vertex map `f`, the
  coordinate permutation `perms3[t]` and the reflections in bit mask `eps` does
  not occur -/
  | pat (r : Nat) (f : List Nat) (t eps : Nat)
  /-- the `j`-th anchor literal -/
  | anchor (j : Nat)

/-- Two literals forbidding one entry of a transformed pattern. -/
def patEntry (f : List Nat) (τ : List Nat) (eps : Nat) (e : Nat × Nat × Bool) : List Nat :=
  let ab := e4.getD e.1 (0, 0)
  let x := f.getD ab.1 0
  let y := f.getD ab.2 0
  let c := τ.getD e.2.1 0
  -- `s'` true: the claim is `p y c - p x c > 0`.
  let s' := e.2.2 ^^ eps.testBit e.2.1
  -- value of the sign variable of the edge `{x, y}` under the claim
  let sv := s' ^^ decide (y < x)
  [neg (colVar x y c), if sv then neg (sgnVar x y) else pos (sgnVar x y)]

def Prov.clause : Prov → Clause
  | .alo u v => [pos (colVar u v 0), pos (colVar u v 1), pos (colVar u v 2)]
  | .amo u v a b => [neg (colVar u v a), neg (colVar u v b)]
  | .cut S k u v =>
    ((pairs.filter fun e => (S.testBit e.1 != S.testBit e.2) && !(e.1 == u && e.2 == v)).map
      fun e => pos (colVar e.1 e.2 k))
  | .pat r f t eps =>
    (reps.getD r []).flatMap (patEntry f (perms3.getD t []) eps)
  | .anchor j => [anchors.getD j 0]

def Prov.valid : Prov → Bool
  | .alo u v => decide (u < v) && decide (v < 8)
  | .amo u v a b => decide (u < v) && decide (v < 8) && decide (a < b) && decide (b < 3)
  | .cut S k u v => decide (0 < S) && decide (S < 255) && decide (k < 3) && decide (u < v) &&
      decide (v < 8)
  | .pat r f t eps => decide (r < 7) && decide (t < 6) && decide (eps < 8) && f.length == 4 &&
      f.all (fun x => decide (x < 8)) && decide f.Nodup
  | .anchor j => decide (j < 11)

/-- The assignment satisfies every clause of the instance. -/
def Base (α : Nat → Bool) : Prop := ∀ π : Prov, π.valid = true → Sat α π.clause

end K8
