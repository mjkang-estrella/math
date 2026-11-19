# Lean source appendix

Lean 4.34.1, Mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612 (see PINS.json).
Hand-written modules are listed in import order; each block is byte-exact (verified by
scripts/build_appendix.py --check).  The eight generated certificate modules
K8Cert00-K8Cert07 sit between K8Cnf and K8Comb in the import order; they are not
reproduced here.  Instead the last part gives the generator scripts (byte-exact), the
sha256 of the certificate inputs, and the sha256 of every generated module, so that
an independent replay can regenerate and rebuild them:

    python3 -I scripts/k8_cnf.py cert/k8                       # CNF + provenance
    <python with PySAT 1.9.dev23> scripts/k8_solve.py cert/k8.cnf cert/k8.drat
    drat-trim cert/k8.cnf cert/k8.drat -L cert/k8.lrat          # 2024 drat-trim
    python3 -I scripts/k8_lean_cert.py 2200                    # src/K8Cert00..07.lean

The pipeline is deterministic; the replay in this lane reproduced every hash below.
Only the Lean kernel check is trusted: the CNF, the proof and the generators are not.

## RupCore.lean

```lean
/-!
# A small reverse-unit-propagation (RUP) checker with a soundness proof

Literals are natural numbers: the literal `2 * v` is the positive literal of the
variable `v` and `2 * v + 1` is its negation.  A clause is a list of literals.
An assignment is a map `Nat → Bool` on variables.

`rupCheck C Hs` assumes the negation of every literal of `C` and then runs unit
propagation through the hint clauses `Hs`, in order.  Every hint must be either
unit (exactly one literal not yet falsified, and no literal already true) or
conflicting (all literals falsified).  The check succeeds when a conflict is
reached.  Soundness (`rupCheck_sound`): if an assignment satisfies every hint
clause, then it satisfies `C`.

The checker is an ordinary Lean function.  Certificates are checked by kernel
reduction (`decide +kernel`), which introduces no axioms.
-/

namespace Rup

abbrev Clause := List Nat

/-- Value of a literal under an assignment of the variables. -/
def litVal (α : Nat → Bool) (l : Nat) : Bool := α (l >>> 1) ^^ l.testBit 0

/-- A clause is satisfied when one of its literals is true. -/
def Sat (α : Nat → Bool) (C : Clause) : Prop := C.any (litVal α) = true

/-- All clauses of a list are satisfied.  An inductive predicate, so proofs are
built by explicit constructor applications. -/
inductive AllSat (α : Nat → Bool) : List Clause → Prop
  | nil : AllSat α []
  | cons {C : Clause} {Cs : List Clause} : Sat α C → AllSat α Cs → AllSat α (C :: Cs)

/-- Outcome of examining one hint clause against the current trail. -/
inductive Hint where
  | bad
  | conflict
  | unit (l : Nat)

/-- `classify t H pend`: `t` is the trail (bit `l` set means literal `l` is
assumed true).  `pend` is the unique unfalsified literal found so far. -/
def classify (t : Nat) : Clause → Option Nat → Hint
  | [], none => .conflict
  | [], some l => .unit l
  | l :: rest, pend =>
    if t.testBit l then .bad
    else if t.testBit (l ^^^ 1) then classify t rest pend
    else match pend with
      | none => classify t rest (some l)
      | some _ => .bad

/-- Unit propagation through the hints. -/
def runHints (t : Nat) : List Clause → Bool
  | [] => false
  | H :: Hs =>
    match classify t H none with
    | .bad => false
    | .conflict => true
    | .unit l => runHints (t ||| (1 <<< l)) Hs

/-- Initial trail: the negations of the literals of the clause. -/
def initTrail : Clause → Nat → Nat
  | [], t => t
  | l :: rest, t => initTrail rest (t ||| (1 <<< (l ^^^ 1)))

def rupCheck (C : Clause) (Hs : List Clause) : Bool := runHints (initTrail C 0) Hs

/-! ## Soundness -/

theorem testBit_setLit (t l m : Nat) :
    (t ||| (1 <<< l)).testBit m = (t.testBit m || decide (l = m)) := by
  rw [Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]

theorem shift_xor_one (l : Nat) : (l ^^^ 1) >>> 1 = l >>> 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_xor]
  have : (1 : Nat).testBit (1 + i) = false := by
    rw [Nat.add_comm, Nat.testBit_succ]; simp
  rw [this, Bool.xor_false]

theorem testBit0_xor_one (l : Nat) : (l ^^^ 1).testBit 0 = !l.testBit 0 := by
  rw [Nat.testBit_xor]
  have : (1 : Nat).testBit 0 = true := by decide
  rw [this, Bool.xor_true]

theorem litVal_neg (α : Nat → Bool) (l : Nat) : litVal α (l ^^^ 1) = !litVal α l := by
  unfold litVal
  rw [shift_xor_one, testBit0_xor_one]
  cases α (l >>> 1) <;> cases l.testBit 0 <;> rfl

/-- Trail invariant: every literal on the trail is true. -/
def Inv (α : Nat → Bool) (t : Nat) : Prop := ∀ m, t.testBit m = true → litVal α m = true

theorem Inv.set {α : Nat → Bool} {t l : Nat} (h : Inv α t) (hl : litVal α l = true) :
    Inv α (t ||| (1 <<< l)) := by
  intro m hm
  rw [testBit_setLit] at hm
  rcases Bool.or_eq_true_iff.mp hm with hm | hm
  · exact h m hm
  · have : l = m := of_decide_eq_true hm
    subst this; exact hl

theorem classify_sound {α : Nat → Bool} {t : Nat} (ht : Inv α t) :
    ∀ (H : Clause) (pend : Option Nat),
      (H.any (litVal α) = true ∨ ∃ p, pend = some p ∧ litVal α p = true) →
      match classify t H pend with
      | .bad => True
      | .conflict => False
      | .unit l => litVal α l = true
  | [], none, h => by
    rcases h with h | ⟨p, hp, _⟩
    · simp at h
    · cases hp
  | [], some l, h => by
    rcases h with h | ⟨p, hp, hpv⟩
    · simp at h
    · cases hp; exact hpv
  | l :: rest, pend, h => by
    unfold classify
    by_cases h1 : t.testBit l = true
    · simp [h1]
    · simp only [h1]
      by_cases h2 : t.testBit (l ^^^ 1) = true
      · simp only [h2, ite_true, Bool.false_eq_true, ite_false]
        apply classify_sound ht rest pend
        have hfalse : litVal α l = false := by
          have := ht _ h2
          rw [litVal_neg] at this
          simpa using this
        rcases h with h | h
        · left
          rw [List.any_cons, hfalse, Bool.false_or] at h
          exact h
        · right; exact h
      · simp only [h2, Bool.false_eq_true, ite_false]
        cases pend with
        | none =>
          apply classify_sound ht rest (some l)
          rcases h with h | ⟨p, hp, _⟩
          · rw [List.any_cons] at h
            rcases Bool.or_eq_true_iff.mp h with h | h
            · right; exact ⟨l, rfl, h⟩
            · left; exact h
          · cases hp
        | some _ => trivial

theorem runHints_sound {α : Nat → Bool} :
    ∀ (Hs : List Clause) (t : Nat), Inv α t → AllSat α Hs → runHints t Hs = true → False
  | [], _, _, _, h => by simp [runHints] at h
  | H :: Hs, t, ht, hall, h => by
    cases hall with
    | cons hH hHs =>
      have key := classify_sound ht H none (Or.inl hH)
      unfold runHints at h
      revert key h
      cases classify t H none with
      | bad => intro _ h; simp at h
      | conflict => intro key _; exact key
      | unit l =>
        intro key h
        exact runHints_sound Hs _ (ht.set key) hHs h

theorem initTrail_inv {α : Nat → Bool} :
    ∀ (C : Clause) (t : Nat), Inv α t → C.any (litVal α) = false → Inv α (initTrail C t)
  | [], _, ht, _ => ht
  | l :: rest, t, ht, hC => by
    rw [List.any_cons, Bool.or_eq_false_iff] at hC
    apply initTrail_inv rest _ _ hC.2
    apply ht.set
    rw [litVal_neg, hC.1]; rfl

theorem rupCheck_sound {α : Nat → Bool} {C : Clause} {Hs : List Clause}
    (hchk : rupCheck C Hs = true) (hs : AllSat α Hs) : Sat α C := by
  unfold Sat
  cases hC : C.any (litVal α) with
  | true => rfl
  | false =>
    exfalso
    have h0 : Inv α 0 := by
      intro m hm
      rw [Nat.zero_testBit] at hm
      cases hm
    exact runHints_sound Hs _ (initTrail_inv C 0 h0 hC) hs hchk

/-- The empty clause is never satisfied. -/
theorem not_sat_nil (α : Nat → Bool) : ¬ Sat α [] := by
  simp [Sat]

end Rup
```

## K8Cnf.lean

```lean
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
```

## K8Comb.lean

```lean
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Linarith

/-!
# The combinatorial shadow of an edge-redundantly rigid placement of `K₈` in `ℓ∞³`

`Dom x k`: coordinate `k` is the unique coordinate of largest absolute value of
`x`.  `Good p` collects the two consequences of edge-redundant rigidity that the
refutation uses (proved in `LinfBridge`):
* every pair of distinct points has a dominant coordinate;
* for every edge `uv`, every cut `(S, V ∖ S)` and every colour `k`, some edge
  other than `uv` crossing the cut has colour `k`.

`Anchored p` is the symmetry-normalised form used by the propositional instance.
-/

namespace K8

/-- Coordinate `k` strictly dominates every other coordinate in absolute value. -/
def Dom {d : ℕ} (x : Fin d → ℝ) (k : Fin d) : Prop := ∀ j, j ≠ k → |x j| < |x k|

structure Good (p : Fin 8 → Fin 3 → ℝ) : Prop where
  dom : ∀ u v : Fin 8, u ≠ v → ∃ k, Dom (p v - p u) k
  cut : ∀ u v : Fin 8, u ≠ v → ∀ (S : Finset (Fin 8)) (k : Fin 3), (∃ a, a ∈ S) → (∃ b, b ∉ S) →
    ∃ a ∈ S, ∃ b, b ∉ S ∧ ¬ (a = u ∧ b = v) ∧ ¬ (a = v ∧ b = u) ∧ Dom (p b - p a) k

structure Anchored (p : Fin 8 → Fin 3 → ℝ) : Prop where
  c1 : Dom (p 1 - p 0) 0
  c2 : Dom (p 2 - p 0) 0
  c3 : Dom (p 3 - p 0) 0
  c4 : Dom (p 4 - p 0) 1
  c5 : Dom (p 5 - p 0) 1
  c6 : Dom (p 6 - p 0) 2
  c7 : Dom (p 7 - p 0) 2
  s1 : p 0 0 < p 1 0
  s2 : p 0 0 < p 2 0
  s4 : p 0 1 < p 4 1
  s6 : p 0 2 < p 6 2

theorem Dom.neg {d : ℕ} {x : Fin d → ℝ} {k : Fin d} (h : Dom x k) : Dom (-x) k := by
  intro j hj
  simpa [abs_neg] using h j hj

theorem Dom.sub_comm {d : ℕ} {a b : Fin d → ℝ} {k : Fin d} (h : Dom (a - b) k) : Dom (b - a) k := by
  have := h.neg
  rwa [neg_sub] at this

theorem Dom.unique {d : ℕ} {x : Fin d → ℝ} {k l : Fin d} (hk : Dom x k) (hl : Dom x l) : k = l := by
  by_contra hne
  have h1 := hk l (Ne.symm hne)
  have h2 := hl k hne
  linarith

theorem Dom.pos {d : ℕ} {x : Fin d → ℝ} {k : Fin d} (h : Dom x k) (j : Fin d) (hj : j ≠ k) :
    0 < |x k| :=
  lt_of_le_of_lt (abs_nonneg _) (h j hj)

end K8
```

## K8Patterns.lean

```lean
import K8Cnf
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# The seven forbidden signed four-point patterns

For `Q : ℕ → ℕ → ℝ` (point `x`, coordinate `c`) the entry `(i, c, s)` of a
pattern says that for the `i`-th pair `(a, b)` of `K₄`,
`sgn(s) * (Q b c - Q a c) > |Q b j - Q a j|` for both coordinates `j ≠ c`.
Each representative pattern in `K8.reps` is infeasible over the reals: a
nonnegative combination of its strict inequalities is `0 < 0`.  `linarith`
finds the combination.
-/

set_option linter.unusedSimpArgs false

namespace K8

/-- `+1` or `-1`. -/
def sgnR (b : Bool) : ℝ := if b then 1 else -1

/-- The real inequalities expressed by one pattern entry. -/
def DomS (Q : ℕ → ℕ → ℝ) (e : ℕ × ℕ × Bool) : Prop :=
  ∀ j, j < 3 → j ≠ e.2.1 →
    |Q (e4.getD e.1 (0, 0)).2 j - Q (e4.getD e.1 (0, 0)).1 j| <
      sgnR e.2.2 * (Q (e4.getD e.1 (0, 0)).2 e.2.1 - Q (e4.getD e.1 (0, 0)).1 e.2.1)

theorem forall_lt_three {P : ℕ → Prop} : (∀ j, j < 3 → P j) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h; exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega)⟩
  · rintro ⟨h0, h1, h2⟩ j hj
    interval_cases j <;> assumption

theorem rep_infeasible (r : ℕ) (hr : r < 7) (Q : ℕ → ℕ → ℝ)
    (h : ∀ e ∈ reps.getD r [], DomS Q e) : False := by
  interval_cases r <;>
  · simp only [reps, List.getD_cons_succ, List.getD_cons_zero, List.forall_mem_cons,
      List.forall_mem_nil, DomS, forall_lt_three, e4, sgnR] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero, ne_eq, OfNat.ofNat_ne_zero,
      OfNat.zero_ne_ofNat, OfNat.ofNat_ne_one, OfNat.one_ne_ofNat, one_ne_zero, zero_ne_one,
      not_false_eq_true, not_true_eq_false, false_implies, true_implies, Bool.false_eq_true,
      ite_true, ite_false, abs_lt, one_mul, neg_mul, and_true, true_and] at h
    linarith

end K8
```

## K8Sound.lean

```lean
import K8Comb
import K8Patterns
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Soundness of the propositional instance

For a placement `p : Fin 8 → Fin 3 → ℝ` the assignment `assign p` gives the
colour variables and sign variables their geometric meaning.  If `p` is `Good`
and `Anchored` then `assign p` satisfies every clause of every valid provenance
record (`base_of_good`).
-/

set_option linter.unusedSimpArgs false

namespace K8

open Rup

/-- The placement extended by `0` to all natural-number indices. -/
noncomputable def P (p : Fin 8 → Fin 3 → ℝ) (x c : ℕ) : ℝ :=
  if h : x < 8 ∧ c < 3 then p ⟨x, h.1⟩ ⟨c, h.2⟩ else 0

/-- Dominance of colour `c` on the pair `(u, v)`, natural-number version. -/
def DomN (p : Fin 8 → Fin 3 → ℝ) (u v c : ℕ) : Prop :=
  ∀ j, j < 3 → j ≠ c → |P p v j - P p u j| < |P p v c - P p u c|

open Classical in
/-- The assignment induced by a placement. -/
noncomputable def assign (p : Fin 8 → Fin 3 → ℝ) (x : ℕ) : Bool :=
  if 1 ≤ x ∧ x ≤ 84 then
    decide (DomN p (pairs.getD ((x - 1) / 3) (0, 0)).1 (pairs.getD ((x - 1) / 3) (0, 0)).2
      ((x - 1) % 3))
  else if 85 ≤ x ∧ x ≤ 112 then
    decide (∃ c, c < 3 ∧ DomN p (pairs.getD (x - 85) (0, 0)).1 (pairs.getD (x - 85) (0, 0)).2 c ∧
      P p (pairs.getD (x - 85) (0, 0)).1 c < P p (pairs.getD (x - 85) (0, 0)).2 c)
  else false

/-! ### Finite facts about the numbering, checked by kernel evaluation -/

theorem pairs_edgeIdx_fin : ∀ u v : Fin 8, u < v →
    pairs.getD (edgeIdx u v) (0, 0) = (u.val, v.val) ∧ edgeIdx u v < 28 := by
  decide +kernel

theorem pairs_edgeIdx_aux {u v : ℕ} (hu : u < 8) (hv : v < 8) (huv : u < v) :
    pairs.getD (edgeIdx u v) (0, 0) = (u, v) ∧ edgeIdx u v < 28 :=
  pairs_edgeIdx_fin ⟨u, hu⟩ ⟨v, hv⟩ huv

theorem mem_pairs_fin : ∀ u v : Fin 8, u < v → (u.val, v.val) ∈ pairs := by
  decide +kernel

theorem testBit_some_fin : ∀ S : Fin 256, 0 < S.val → ∃ a : Fin 8, S.val.testBit a = true := by
  decide +kernel

theorem testBit_none_fin : ∀ S : Fin 255, ∃ a : Fin 8, S.val.testBit a = false := by
  decide +kernel

theorem perms3_fin : ∀ (t : Fin 6) (c c' : Fin 3),
    (perms3.getD t []).getD c 0 < 3 ∧
      ((perms3.getD t []).getD c 0 = (perms3.getD t []).getD c' 0 → c = c') := by
  decide +kernel

theorem perms3_aux {t c c' : ℕ} (ht : t < 6) (hc : c < 3) (hc' : c' < 3) :
    (perms3.getD t []).getD c 0 < 3 ∧
      ((perms3.getD t []).getD c 0 = (perms3.getD t []).getD c' 0 → c = c') := by
  have := perms3_fin ⟨t, ht⟩ ⟨c, hc⟩ ⟨c', hc'⟩
  simpa [Fin.ext_iff] using this

theorem reps_fin : ∀ r : Fin 7, ∀ e ∈ reps.getD r [], e.1 < 6 ∧ e.2.1 < 3 := by
  decide +kernel

theorem e4_fin : ∀ i : Fin 6, (e4.getD i (0, 0)).1 < 4 ∧ (e4.getD i (0, 0)).2 < 4 ∧
    (e4.getD i (0, 0)).1 ≠ (e4.getD i (0, 0)).2 := by
  decide +kernel

/-! ### Literals -/

theorem litVal_pos (α : ℕ → Bool) (x : ℕ) : litVal α (pos x) = α x := by
  unfold litVal pos
  have h1 : (2 * x) >>> 1 = x := by rw [Nat.shiftRight_one]; omega
  have h2 : (2 * x).testBit 0 = false := by rw [Nat.testBit_zero]; simp
  rw [h1, h2, Bool.xor_false]

theorem litVal_neg' (α : ℕ → Bool) (x : ℕ) : litVal α (neg x) = !α x := by
  unfold litVal neg
  have h1 : (2 * x + 1) >>> 1 = x := by rw [Nat.shiftRight_one]; omega
  have h2 : (2 * x + 1).testBit 0 = true := by rw [Nat.testBit_zero]; simp
  rw [h1, h2, Bool.xor_true]

theorem sat_of_mem {α : ℕ → Bool} {C : Clause} {l : ℕ} (hl : l ∈ C) (hv : litVal α l = true) :
    Sat α C := List.any_eq_true.mpr ⟨l, hl, hv⟩

theorem colVar_comm (u v c : ℕ) : colVar u v c = colVar v u c := by
  unfold colVar; rw [min_comm, max_comm]

theorem sgnVar_comm (u v : ℕ) : sgnVar u v = sgnVar v u := by
  unfold sgnVar; rw [min_comm, max_comm]

theorem colVar_minmax (a b c : ℕ) : colVar (min a b) (max a b) c = colVar a b c := by
  rcases le_total a b with h | h
  · rw [Nat.min_eq_left h, Nat.max_eq_right h]
  · rw [Nat.min_eq_right h, Nat.max_eq_left h, colVar_comm]

/-! ### The induced assignment on colour and sign variables -/

variable {p : Fin 8 → Fin 3 → ℝ}

theorem DomN.symm {u v c : ℕ} (h : DomN p u v c) : DomN p v u c := by
  intro j hj hjc
  rw [abs_sub_comm (P p u j), abs_sub_comm (P p u c)]
  exact h j hj hjc

theorem DomN.unique {u v c c' : ℕ} (h : DomN p u v c) (h' : DomN p u v c') (hc : c < 3)
    (hc' : c' < 3) : c = c' := by
  by_contra hne
  have h1 := h c' hc' (Ne.symm hne)
  have h2 := h' c hc hne
  linarith

theorem DomN.ne {u v c : ℕ} (h : DomN p u v c) : P p v c - P p u c ≠ 0 := by
  intro h0
  have := h (if c = 0 then 1 else 0) (by split <;> omega) (by split <;> omega)
  rw [h0, abs_zero] at this
  exact absurd this (not_lt.mpr (abs_nonneg _))

theorem assign_col {u v c : ℕ} (huv : u < v) (hv : v < 8) (hc : c < 3) :
    assign p (colVar u v c) = true ↔ DomN p u v c := by
  obtain ⟨hp, hlt⟩ := pairs_edgeIdx_aux (by omega) hv huv
  have hmin : min u v = u := by omega
  have hmax : max u v = v := by omega
  unfold assign colVar
  rw [hmin, hmax]
  have h1 : 1 ≤ 1 + 3 * edgeIdx u v + c ∧ 1 + 3 * edgeIdx u v + c ≤ 84 := by omega
  have h2 : (1 + 3 * edgeIdx u v + c - 1) / 3 = edgeIdx u v := by omega
  have h3 : (1 + 3 * edgeIdx u v + c - 1) % 3 = c := by omega
  rw [ite_eq_left h1, h2, h3, hp]
  simp only [decide_eq_true_eq]

theorem assign_col' {u v c : ℕ} (huv : u ≠ v) (hu : u < 8) (hv : v < 8) (hc : c < 3) :
    assign p (colVar u v c) = true ↔ DomN p u v c := by
  rcases Nat.lt_or_gt_of_ne huv with h | h
  · exact assign_col h hv hc
  · rw [colVar_comm, assign_col h hu hc]
    exact ⟨DomN.symm, DomN.symm⟩

theorem assign_sgn {u v : ℕ} (huv : u < v) (hv : v < 8) :
    assign p (sgnVar u v) = true ↔ ∃ c, c < 3 ∧ DomN p u v c ∧ P p u c < P p v c := by
  obtain ⟨hp, hlt⟩ := pairs_edgeIdx_aux (by omega) hv huv
  have hmin : min u v = u := by omega
  have hmax : max u v = v := by omega
  unfold assign sgnVar
  rw [hmin, hmax]
  have h0 : ¬ (1 ≤ 85 + edgeIdx u v ∧ 85 + edgeIdx u v ≤ 84) := by omega
  have h1 : 85 ≤ 85 + edgeIdx u v ∧ 85 + edgeIdx u v ≤ 112 := by omega
  have h2 : 85 + edgeIdx u v - 85 = edgeIdx u v := by omega
  rw [ite_eq_right h0, ite_eq_left h1, h2, hp]
  simp only [decide_eq_true_eq]

/-- Positive orientation of the edge `{u, v}` (`u < v`) in colour `c`. -/
theorem assign_sgn_col {u v c : ℕ} (huv : u < v) (hv : v < 8) (hc : c < 3) (hd : DomN p u v c) :
    assign p (sgnVar u v) = true ↔ 0 < P p v c - P p u c := by
  rw [assign_sgn huv hv]
  constructor
  · rintro ⟨c', hc', hd', hlt⟩
    rw [DomN.unique hd hd' hc hc']; linarith
  · intro hpos; exact ⟨c, hc, hd, by linarith⟩

theorem sgnR_true : sgnR true = 1 := rfl
theorem sgnR_false : sgnR false = -1 := rfl

/-- If the sign variable of `{x, y}` has the value `s xor (y < x)` then
`sgnR s * (P y c - P x c) > 0`. -/
theorem sgn_meaning {x y c : ℕ} (hxy : x ≠ y) (hx : x < 8) (hy : y < 8) (hc : c < 3)
    (hd : DomN p x y c) (s : Bool) (hs : assign p (sgnVar x y) = (s ^^ decide (y < x))) :
    0 < sgnR s * (P p y c - P p x c) := by
  have hne := DomN.ne hd
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · have hn : decide (y < x) = false := decide_eq_false (by omega)
    rw [hn, Bool.xor_false] at hs
    have key := assign_sgn_col h hy hc hd
    cases s
    · rw [sgnR_false]
      have : ¬ 0 < P p y c - P p x c := fun hp => by rw [← key, hs] at hp; cases hp
      rcases lt_or_eq_of_le (not_lt.mp this) with h' | h'
      · linarith
      · exact absurd h' hne
    · rw [sgnR_true, one_mul]; exact key.mp hs
  · have hn : decide (y < x) = true := decide_eq_true h
    rw [hn, Bool.xor_true, sgnVar_comm] at hs
    have key := assign_sgn_col h hx hc hd.symm
    cases s
    · rw [sgnR_false]
      have := key.mp hs
      linarith
    · rw [sgnR_true, one_mul]
      have : ¬ 0 < P p x c - P p y c := fun hp => by rw [← key, hs] at hp; cases hp
      rcases lt_or_eq_of_le (not_lt.mp this) with h' | h'
      · linarith
      · exact absurd (by linarith) hne

/-! ### From `Fin` dominance to the natural-number version -/

theorem P_fin (u : Fin 8) (c : Fin 3) : P p u c = p u c := by
  unfold P; rw [dite_eq_left ⟨u.isLt, c.isLt⟩]

theorem domN_of_dom {u v : Fin 8} {k : Fin 3} (h : Dom (p v - p u) k) : DomN p u v k := by
  intro j hj hjk
  have := h ⟨j, hj⟩ (fun e => hjk (by rw [← e]))
  simp only [Pi.sub_apply] at this
  rw [show P p v j = p v ⟨j, hj⟩ from P_fin v ⟨j, hj⟩, show P p u j = p u ⟨j, hj⟩ from P_fin u ⟨j, hj⟩,
    P_fin, P_fin]
  exact this

/-! ### Soundness of each clause family -/

theorem sound_alo (hg : Good p) {u v : ℕ} (huv : u < v) (hv : v < 8) :
    Sat (assign p) (Prov.alo u v).clause := by
  obtain ⟨k, hk⟩ := hg.dom ⟨u, by omega⟩ ⟨v, hv⟩ (fun e => by simp [Fin.ext_iff] at e; omega)
  have hd := domN_of_dom hk
  apply sat_of_mem (l := pos (colVar u v k))
  · simp only [Prov.clause]
    fin_cases k <;> simp
  · rw [litVal_pos, assign_col huv hv k.isLt]; exact hd

theorem sound_amo {u v a b : ℕ} (huv : u < v) (hv : v < 8) (hab : a < b) (hb : b < 3) :
    Sat (assign p) (Prov.amo u v a b).clause := by
  simp only [Prov.clause]
  by_cases ha' : DomN p u v a
  · apply sat_of_mem (l := neg (colVar u v b)) (by simp)
    rw [litVal_neg', Bool.not_eq_true', ← Bool.not_eq_true, assign_col huv hv hb]
    intro hb'
    exact absurd (DomN.unique ha' hb' (by omega) hb) (by omega)
  · apply sat_of_mem (l := neg (colVar u v a)) (by simp)
    rw [litVal_neg', Bool.not_eq_true', ← Bool.not_eq_true, assign_col huv hv (by omega)]
    exact ha'

theorem sound_cut (hg : Good p) {S k u v : ℕ} (hS0 : 0 < S) (hS : S < 255) (hk : k < 3)
    (huv : u < v) (hv : v < 8) : Sat (assign p) (Prov.cut S k u v).clause := by
  obtain ⟨⟨a0, ha0⟩, hSa⟩ := testBit_some_fin ⟨S, by omega⟩ hS0
  obtain ⟨⟨b0, hb0⟩, hSb⟩ := testBit_none_fin ⟨S, hS⟩
  let T : Finset (Fin 8) := Finset.univ.filter fun a => S.testBit a.val = true
  obtain ⟨a, haT, b, hbT, hn1, hn2, hd⟩ := hg.cut ⟨u, by omega⟩ ⟨v, hv⟩
    (fun e => by simp [Fin.ext_iff] at e; omega) T ⟨k, hk⟩
    ⟨⟨a0, ha0⟩, by simpa [T] using hSa⟩ ⟨⟨b0, hb0⟩, by simpa [T] using hSb⟩
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at haT hbT
  have hab : a.val ≠ b.val := fun e => by rw [Fin.ext e] at haT; rw [haT] at hbT; cases hbT
  have hdN : DomN p a b k := domN_of_dom hd
  simp only [Fin.ext_iff] at hn1 hn2
  apply sat_of_mem (l := pos (colVar (min a.val b.val) (max a.val b.val) k))
  · simp only [Prov.clause, List.mem_map, List.mem_filter]
    refine ⟨(min a.val b.val, max a.val b.val), ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.lt_or_gt_of_ne hab with h | h
      · rw [Nat.min_eq_left h.le, Nat.max_eq_right h.le]; exact mem_pairs_fin a b h
      · rw [Nat.min_eq_right h.le, Nat.max_eq_left h.le]; exact mem_pairs_fin b a h
    · rcases Nat.lt_or_gt_of_ne hab with h | h
      · rw [Nat.min_eq_left h.le, Nat.max_eq_right h.le]
        simp [haT, hbT]; omega
      · rw [Nat.min_eq_right h.le, Nat.max_eq_left h.le]
        simp [haT, hbT]; omega
  · rw [litVal_pos, colVar_minmax, assign_col' hab a.isLt b.isLt hk]
    exact hdN

theorem sound_anchor (ha : Anchored p) {j : ℕ} (hj : j < 11) :
    Sat (assign p) (Prov.anchor j).clause := by
  have col : ∀ (c : Fin 8) (k : Fin 3), 0 < c.val → Dom (p c - p 0) k →
      litVal (assign p) (pos (colVar 0 c k)) = true := by
    intro c k hlt hd
    rw [litVal_pos, assign_col hlt c.isLt k.isLt]
    exact domN_of_dom hd
  have sg : ∀ (c : Fin 8) (k : Fin 3), 0 < c.val → Dom (p c - p 0) k → p 0 k < p c k →
      litVal (assign p) (pos (sgnVar 0 c)) = true := by
    intro c k hc hd hlt
    rw [litVal_pos, assign_sgn hc c.isLt]
    refine ⟨k, k.isLt, domN_of_dom hd, ?_⟩
    rw [show P p 0 k = p 0 k from P_fin 0 k, P_fin]; exact hlt
  simp only [Prov.clause]
  interval_cases j
  · exact sat_of_mem (List.mem_singleton_self _) (col 1 0 (by decide) ha.c1)
  · exact sat_of_mem (List.mem_singleton_self _) (col 2 0 (by decide) ha.c2)
  · exact sat_of_mem (List.mem_singleton_self _) (col 3 0 (by decide) ha.c3)
  · exact sat_of_mem (List.mem_singleton_self _) (col 4 1 (by decide) ha.c4)
  · exact sat_of_mem (List.mem_singleton_self _) (col 5 1 (by decide) ha.c5)
  · exact sat_of_mem (List.mem_singleton_self _) (col 6 2 (by decide) ha.c6)
  · exact sat_of_mem (List.mem_singleton_self _) (col 7 2 (by decide) ha.c7)
  · exact sat_of_mem (List.mem_singleton_self _) (sg 1 0 (by decide) ha.c1 ha.s1)
  · exact sat_of_mem (List.mem_singleton_self _) (sg 2 0 (by decide) ha.c2 ha.s2)
  · exact sat_of_mem (List.mem_singleton_self _) (sg 4 1 (by decide) ha.c4 ha.s4)
  · exact sat_of_mem (List.mem_singleton_self _) (sg 6 2 (by decide) ha.c6 ha.s6)

/-! ### Patterns -/

theorem sgnR_mul (s b : Bool) : sgnR s * sgnR (!b) = sgnR (s ^^ b) := by
  cases s <;> cases b <;> simp [sgnR]

theorem abs_sgnR (b : Bool) : |sgnR b| = 1 := by
  cases b <;> simp [sgnR]

theorem getD_ne_of_nodup {f : List ℕ} (hl : f.length = 4) (hn : f.Nodup) {a b : ℕ} (ha : a < 4)
    (hb : b < 4) (hab : a ≠ b) : f.getD a 0 ≠ f.getD b 0 := by
  rw [← List.getElem_eq_getD (l := f) (i := a) (h := by omega) 0,
    ← List.getElem_eq_getD (l := f) (i := b) (h := by omega) 0]
  intro e
  exact hab ((List.Nodup.getElem_inj hn).mp e)

theorem getD_lt {f : List ℕ} (hl : f.length = 4) (hall : f.all (fun x => decide (x < 8)) = true)
    {a : ℕ} (ha : a < 4) : f.getD a 0 < 8 := by
  rw [← List.getElem_eq_getD (l := f) (i := a) (h := by omega) 0]
  have := List.all_eq_true.mp hall _ (List.getElem_mem (show a < f.length by omega))
  simpa using this

theorem sound_pat {r : ℕ} {f : List ℕ} {t eps : ℕ} (hr : r < 7) (ht : t < 6)
    (hl : f.length = 4) (hall : f.all (fun x => decide (x < 8)) = true) (hn : f.Nodup) :
    Sat (assign p) (Prov.pat r f t eps).clause := by
  unfold Sat
  by_contra hno
  rw [Bool.not_eq_true, List.any_eq_false] at hno
  let τ := perms3.getD t []
  let Q : ℕ → ℕ → ℝ := fun x c => sgnR (!eps.testBit c) * P p (f.getD x 0) (τ.getD c 0)
  apply rep_infeasible r hr Q
  intro e he
  obtain ⟨hi, hc⟩ := reps_fin ⟨r, hr⟩ e he
  obtain ⟨ha4, hb4, hab⟩ := e4_fin ⟨e.1, hi⟩
  simp only [Fin.val_mk] at ha4 hb4 hab
  set a := (e4.getD e.1 (0, 0)).1 with hA
  set b := (e4.getD e.1 (0, 0)).2 with hB
  set x := f.getD a 0 with hX
  set y := f.getD b 0 with hY
  set c' := τ.getD e.2.1 0 with hC
  set s' := e.2.2 ^^ eps.testBit e.2.1 with hS
  have hpe : patEntry f τ eps e = [neg (colVar x y c'),
      if (s' ^^ decide (y < x)) then neg (sgnVar x y) else pos (sgnVar x y)] := rfl
  have hmem : ∀ l ∈ patEntry f τ eps e, l ∈ (Prov.pat r f t eps).clause := by
    intro l hl'
    simp only [Prov.clause, List.mem_flatMap]
    exact ⟨e, he, hl'⟩
  have hcol := hno (neg (colVar x y c')) (hmem _ (by rw [hpe]; exact List.mem_cons_self))
  have hsgn := hno _ (hmem _ (by rw [hpe]; exact List.mem_cons_of_mem _ List.mem_cons_self))
  have hxy : x ≠ y := getD_ne_of_nodup hl hn ha4 hb4 hab
  have hx8 : x < 8 := getD_lt hl hall ha4
  have hy8 : y < 8 := getD_lt hl hall hb4
  have hc'3 : c' < 3 := (perms3_aux ht hc (c' := 0) (by omega)).1
  rw [litVal_neg', Bool.not_eq_true', Bool.not_eq_false, assign_col' hxy hx8 hy8 hc'3] at hcol
  have hd : DomN p x y c' := hcol
  have hsv : assign p (sgnVar x y) = (s' ^^ decide (y < x)) := by
    revert hsgn
    cases hsv' : (s' ^^ decide (y < x))
    · simp [litVal_pos]
    · simp [litVal_neg']
  have hpos := sgn_meaning hxy hx8 hy8 hc'3 hd _ hsv
  have habs : |P p y c' - P p x c'| = sgnR s' * (P p y c' - P p x c') := by
    have h2 : |sgnR s' * (P p y c' - P p x c')| = |P p y c' - P p x c'| := by
      rw [abs_mul, abs_sgnR, one_mul]
    rw [← h2, abs_of_pos hpos]
  -- now the entry's inequalities
  intro j hj hjc
  have hτj : τ.getD j 0 < 3 ∧ τ.getD j 0 ≠ c' := by
    refine ⟨(perms3_aux ht hj (c' := 0) (by omega)).1, fun h => hjc ?_⟩
    exact (perms3_aux ht hj hc).2 h
  have hdj := hd _ hτj.1 hτj.2
  show |Q b j - Q a j| < sgnR e.2.2 * (Q b e.2.1 - Q a e.2.1)
  have hQj : Q b j - Q a j = sgnR (!eps.testBit j) * (P p y (τ.getD j 0) - P p x (τ.getD j 0)) := by
    simp only [Q]; ring
  have hQc : sgnR e.2.2 * (Q b e.2.1 - Q a e.2.1) = sgnR s' * (P p y c' - P p x c') := by
    simp only [Q]; rw [hS, ← sgnR_mul]; ring
  rw [hQj, hQc, abs_mul, abs_sgnR, one_mul, ← habs]
  exact hdj

/-- Every clause of the instance holds under the induced assignment. -/
theorem base_of_good (hg : Good p) (ha : Anchored p) : Base (assign p) := by
  intro π hv
  cases π with
  | alo u v =>
    simp only [Prov.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact sound_alo hg hv.1 hv.2
  | amo u v a b =>
    simp only [Prov.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact sound_amo hv.1.1.1 hv.1.1.2 hv.1.2 hv.2
  | cut S k u v =>
    simp only [Prov.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact sound_cut hg hv.1.1.1.1 hv.1.1.1.2 hv.1.1.2 hv.1.2 hv.2
  | pat r f t eps =>
    simp only [Prov.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
    exact sound_pat hv.1.1.1.1.1 hv.1.1.1.1.2 hv.1.1.2 hv.1.2 hv.2
  | anchor j =>
    simp only [Prov.valid, decide_eq_true_eq] at hv
    exact sound_anchor ha hv

end K8
```

## K8Wlog.lean

```lean
import K8Comb
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Symmetry breaking

The isometries of `ℓ∞³` used here are coordinate permutations and coordinate
reflections; together with a relabelling of the vertices they preserve `Good`
(`good_transform`).  Every good placement can be transformed into an anchored
one (`exists_anchored`):

* the singleton cut `{0}` forces at least two edges of each colour at vertex `0`;
  since `0` has seven edges, some colour has at least three;
* permute coordinates so that this colour is coordinate `0`;
* among three neighbours of colour `0`, two have the same orientation; reflect
  coordinate `0` if necessary so that they lie above vertex `0`;
* reflect coordinates `1` and `2` so that one neighbour of each lies above `0`;
* relabel the vertices.
-/

namespace K8

open Classical

variable {p : Fin 8 → Fin 3 → ℝ}

/-- The transformed placement: relabel vertices by `σ`, permute coordinates by
`τ`, multiply coordinate `c` by `ε c`. -/
def transform (p : Fin 8 → Fin 3 → ℝ) (σ : Equiv.Perm (Fin 8)) (τ : Equiv.Perm (Fin 3))
    (ε : Fin 3 → ℝ) : Fin 8 → Fin 3 → ℝ :=
  fun v c => ε c * p (σ v) (τ c)

theorem dom_transform {σ : Equiv.Perm (Fin 8)} {τ : Equiv.Perm (Fin 3)} {ε : Fin 3 → ℝ}
    (hε : ∀ c, |ε c| = 1) {a b : Fin 8} {k : Fin 3} (h : Dom (p (σ b) - p (σ a)) (τ k)) :
    Dom (transform p σ τ ε b - transform p σ τ ε a) k := by
  intro j hj
  have hj' : τ j ≠ τ k := fun e => hj (τ.injective e)
  have := h (τ j) hj'
  simp only [Pi.sub_apply, transform]
  rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, hε, hε, one_mul, one_mul]
  simpa using this

theorem good_transform (hg : Good p) (σ : Equiv.Perm (Fin 8)) (τ : Equiv.Perm (Fin 3))
    (ε : Fin 3 → ℝ) (hε : ∀ c, |ε c| = 1) : Good (transform p σ τ ε) where
  dom u v huv := by
    obtain ⟨k, hk⟩ := hg.dom (σ u) (σ v) (fun e => huv (σ.injective e))
    refine ⟨τ.symm k, dom_transform hε ?_⟩
    simpa using hk
  cut u v huv S k hS hS' := by
    obtain ⟨a0, ha0⟩ := hS
    obtain ⟨b0, hb0⟩ := hS'
    obtain ⟨a, ha, b, hb, h1, h2, hd⟩ := hg.cut (σ u) (σ v) (fun e => huv (σ.injective e))
      (S.map σ.toEmbedding) (τ k) ⟨σ a0, by simpa [Finset.mem_map_equiv] using ha0⟩
      ⟨σ b0, by simpa [Finset.mem_map_equiv] using hb0⟩
    rw [Finset.mem_map_equiv] at ha hb
    refine ⟨σ.symm a, ha, σ.symm b, hb, ?_, ?_, dom_transform hε ?_⟩
    · rintro ⟨rfl, rfl⟩; exact h1 ⟨by simp, by simp⟩
    · rintro ⟨rfl, rfl⟩; exact h2 ⟨by simp, by simp⟩
    · simpa using hd

theorem Dom.ne_zero3 {x : Fin 3 → ℝ} {k : Fin 3} (h : Dom x k) : x k ≠ 0 := by
  have : 0 < |x k| := by
    fin_cases k
    · exact h.pos 1 (by decide)
    · exact h.pos 0 (by decide)
    · exact h.pos 0 (by decide)
  exact abs_pos.mp this

/-- Two distinct neighbours of each colour at vertex `0`. -/
theorem two_of_colour (hg : Good p) (k : Fin 3) :
    ∃ b₁ b₂ : Fin 8, b₁ ≠ 0 ∧ b₂ ≠ 0 ∧ b₁ ≠ b₂ ∧ Dom (p b₁ - p 0) k ∧ Dom (p b₂ - p 0) k := by
  obtain ⟨a, ha, b, hb, -, -, hd⟩ := hg.cut 0 1 (by decide) {0} k ⟨0, by simp⟩ ⟨1, by simp⟩
  rw [Finset.mem_singleton] at ha hb
  subst ha
  obtain ⟨a', ha', b', hb', h1, -, hd'⟩ := hg.cut 0 b (Ne.symm hb) {0} k ⟨0, by simp⟩ ⟨b, by simpa⟩
  rw [Finset.mem_singleton] at ha' hb'
  subst ha'
  exact ⟨b, b', hb, hb', fun e => h1 ⟨rfl, e.symm⟩, hd, hd'⟩

/-- Some colour has three distinct neighbours at vertex `0`. -/
theorem three_of_some_colour (hg : Good p) :
    ∃ k : Fin 3, ∃ a₁ a₂ a₃ : Fin 8, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ a₃ ≠ 0 ∧ a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ ∧
      Dom (p a₁ - p 0) k ∧ Dom (p a₂ - p 0) k ∧ Dom (p a₃ - p 0) k := by
  let N : Fin 3 → Finset (Fin 8) := fun k => Finset.univ.filter fun w => w ≠ 0 ∧ Dom (p w - p 0) k
  have hsub : Finset.univ.erase 0 ⊆ N 0 ∪ N 1 ∪ N 2 := by
    intro w hw
    rw [Finset.mem_erase] at hw
    obtain ⟨k, hk⟩ := hg.dom 0 w (Ne.symm hw.1)
    simp only [N, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases k
    · exact Or.inl (Or.inl ⟨hw.1, hk⟩)
    · exact Or.inl (Or.inr ⟨hw.1, hk⟩)
    · exact Or.inr ⟨hw.1, hk⟩
  have h7 : (Finset.univ.erase (0 : Fin 8)).card = 7 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
  have hle := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (N 0 ∪ N 1) (N 2)
  have hu2 := Finset.card_union_le (N 0) (N 1)
  have : ∃ k, 2 < (N k).card := by
    by_contra hno
    push Not at hno
    have := hno 0; have := hno 1; have := hno 2
    omega
  obtain ⟨k, hk⟩ := this
  obtain ⟨a₁, h₁, a₂, h₂, a₃, h₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hk
  simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂ h₃
  exact ⟨k, a₁, a₂, a₃, h₁.1, h₂.1, h₃.1, h12, h13, h23, h₁.2, h₂.2, h₃.2⟩

/-- The reflection sign making `w` lie above `z` in one coordinate. -/
noncomputable def upSign (z w : ℝ) : ℝ := if z < w then 1 else -1

theorem upSign_abs (z w : ℝ) : |upSign z w| = 1 := by
  unfold upSign; split <;> simp

theorem upSign_up {z w : ℝ} (h : w ≠ z) : upSign z w * z < upSign z w * w := by
  unfold upSign
  split
  · linarith
  · rcases lt_or_gt_of_ne h with h' | h'
    · linarith
    · contradiction

theorem upSign_up' {z w w' : ℝ} (h : w' ≠ z) (hiff : z < w ↔ z < w') :
    upSign z w * z < upSign z w * w' := by
  unfold upSign
  split
  · rename_i hw; have := hiff.mp hw; linarith
  · rename_i hw
    have : ¬ z < w' := fun h' => hw (hiff.mpr h')
    rcases lt_or_gt_of_ne h with h' | h'
    · linarith
    · contradiction

theorem exists_anchored (hg : Good p) : ∃ q, Good q ∧ Anchored q := by
  obtain ⟨k₀, a₁, a₂, a₃, h1, h2, h3, h12, h13, h23, d1, d2, d3⟩ := three_of_some_colour hg
  -- two of the three have the same orientation in coordinate `k₀`
  have hpig : ∃ x y z : Fin 8, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      Dom (p x - p 0) k₀ ∧ Dom (p y - p 0) k₀ ∧ Dom (p z - p 0) k₀ ∧
      (p 0 k₀ < p x k₀ ↔ p 0 k₀ < p y k₀) := by
    by_cases e12 : (p 0 k₀ < p a₁ k₀ ↔ p 0 k₀ < p a₂ k₀)
    · exact ⟨a₁, a₂, a₃, h1, h2, h3, h12, h13, h23, d1, d2, d3, e12⟩
    by_cases e13 : (p 0 k₀ < p a₁ k₀ ↔ p 0 k₀ < p a₃ k₀)
    · exact ⟨a₁, a₃, a₂, h1, h3, h2, h13, h12, Ne.symm h23, d1, d3, d2, e13⟩
    · refine ⟨a₂, a₃, a₁, h2, h3, h1, h23, Ne.symm h12, Ne.symm h13, d2, d3, d1, ?_⟩
      tauto
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, dx, dy, dz, hiff⟩ := hpig
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 k₀
  have hτ0 : τ 0 = k₀ := Equiv.swap_apply_left 0 k₀
  have hτ1 : τ 1 ≠ k₀ := fun e => by
    have : τ 1 = τ 0 := by rw [e, hτ0]
    exact absurd (τ.injective this) (by decide)
  have hτ2 : τ 2 ≠ k₀ := fun e => by
    have : τ 2 = τ 0 := by rw [e, hτ0]
    exact absurd (τ.injective this) (by decide)
  have hτ12 : τ 1 ≠ τ 2 := fun e => absurd (τ.injective e) (by decide)
  obtain ⟨b₁, b₂, hb1, hb2, hb12, db1, db2⟩ := two_of_colour hg (τ 1)
  obtain ⟨c₁, c₂, hc1, hc2, hc12, dc1, dc2⟩ := two_of_colour hg (τ 2)
  -- distinctness across colours
  have dne : ∀ {u w : Fin 8} {k l : Fin 3}, Dom (p u - p 0) k → Dom (p w - p 0) l → k ≠ l →
      u ≠ w := by
    intro u w k l hu hw hkl e
    subst e
    exact hkl (hu.unique hw)
  let L : List (Fin 8) := [0, x, y, z, b₁, b₂, c₁, c₂]
  have hL : L.Nodup := by
    simp only [L, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    refine ⟨⟨Ne.symm hx, Ne.symm hy, Ne.symm hz, Ne.symm hb1, Ne.symm hb2, Ne.symm hc1,
      Ne.symm hc2⟩, ⟨hxy, hxz, dne dx db1 (Ne.symm hτ1), dne dx db2 (Ne.symm hτ1),
      dne dx dc1 (Ne.symm hτ2), dne dx dc2 (Ne.symm hτ2)⟩,
      ⟨hyz, dne dy db1 (Ne.symm hτ1), dne dy db2 (Ne.symm hτ1), dne dy dc1 (Ne.symm hτ2),
      dne dy dc2 (Ne.symm hτ2)⟩,
      ⟨dne dz db1 (Ne.symm hτ1), dne dz db2 (Ne.symm hτ1), dne dz dc1 (Ne.symm hτ2),
      dne dz dc2 (Ne.symm hτ2)⟩,
      ⟨hb12, dne db1 dc1 hτ12, dne db1 dc2 hτ12⟩, ⟨dne db2 dc1 hτ12, dne db2 dc2 hτ12⟩, hc12, not_false⟩
  let f : Fin 8 → Fin 8 := ![0, x, y, z, b₁, b₂, c₁, c₂]
  have hf : Function.Injective f := by
    intro i j hij
    have hget : ∀ i : Fin 8, f i = L.get ⟨i, by simp [L]⟩ := by
      intro i; fin_cases i <;> rfl
    rw [hget, hget] at hij
    have := (List.Nodup.get_inj_iff hL).mp hij
    simpa using this
  let σ : Equiv.Perm (Fin 8) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hσ : ∀ i, σ i = f i := fun _ => rfl
  let ε : Fin 3 → ℝ := ![upSign (p 0 k₀) (p x k₀), upSign (p 0 (τ 1)) (p b₁ (τ 1)),
    upSign (p 0 (τ 2)) (p c₁ (τ 2))]
  have hε : ∀ c, |ε c| = 1 := by
    intro c; fin_cases c <;> exact upSign_abs _ _
  refine ⟨transform p σ τ ε, good_transform hg σ τ ε hε, ?_⟩
  have hd : ∀ (i : Fin 8) (k : Fin 3), Dom (p (f i) - p 0) (τ k) →
      Dom (transform p σ τ ε i - transform p σ τ ε 0) k := by
    intro i k h
    apply dom_transform hε
    rw [hσ, hσ]; exact h
  have ne0 : ∀ {w : Fin 8} {k : Fin 3}, Dom (p w - p 0) k → p w k ≠ p 0 k := by
    intro w k h e
    exact h.ne_zero3 (by simp [e])
  constructor
  · exact hd 1 0 (by rw [hτ0]; exact dx)
  · exact hd 2 0 (by rw [hτ0]; exact dy)
  · exact hd 3 0 (by rw [hτ0]; exact dz)
  · exact hd 4 1 db1
  · exact hd 5 1 db2
  · exact hd 6 2 dc1
  · exact hd 7 2 dc2
  · show ε 0 * p (σ 0) (τ 0) < ε 0 * p (σ 1) (τ 0)
    rw [hσ, hσ, hτ0]
    exact upSign_up (ne0 dx)
  · show ε 0 * p (σ 0) (τ 0) < ε 0 * p (σ 2) (τ 0)
    rw [hσ, hσ, hτ0]
    exact upSign_up' (ne0 dy) hiff
  · show ε 1 * p (σ 0) (τ 1) < ε 1 * p (σ 4) (τ 1)
    rw [hσ, hσ]
    exact upSign_up (ne0 db1)
  · show ε 2 * p (σ 0) (τ 2) < ε 2 * p (σ 6) (τ 2)
    rw [hσ, hσ]
    exact upSign_up (ne0 dc1)

end K8
```

## CdkDefs.lean

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Definitions of Cruickshank, Dewar and Kitson, *Algebraic connectivity in normed spaces*

arXiv:2508.00134v1, §2.2 (support functionals, smoothness, rigid motions),
§2.3 (frameworks, trivial infinitesimal flexes, rigidity matrix, infinitesimal
rigidity) and §5 (edge-redundant rigidity, Conjecture 5.4).

The definitions are stated for an arbitrary real normed space `E` with a family
of vectors `b : Fin d → E` playing the role of the standard basis
`b₁, …, b_d` of `ℝ^d` (the columns of the rigidity matrix are indexed by
`V × [d]`, and a kernel vector `u ∈ ℝ^{V × [d]}` is identified with the
displacement `v ↦ ∑ᵢ u (v, i) • bᵢ`).  The space `ℓ∞^d` is `Fin d → ℝ` with
Mathlib's sup norm `‖x‖ = maxᵢ |xᵢ|`, and `bᵢ = Pi.single i 1`.
-/

namespace CDK

open Matrix

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The dual norm of a linear functional, `‖φ‖* = sup_{‖x‖ = 1} |φ x|` (§2.2). -/
noncomputable def dualNorm (φ : E →ₗ[ℝ] ℝ) : ℝ :=
  sSup ((fun x => |φ x|) '' Metric.sphere (0 : E) 1)

/-- `φ` is a support functional for `x₀`: `φ x₀ = 1` and `‖φ‖* = 1` (§2.2). -/
def IsSupportFunctional (x₀ : E) (φ : E →ₗ[ℝ] ℝ) : Prop :=
  φ x₀ = 1 ∧ dualNorm φ = 1

/-- The norm is smooth at `x₀` if `x₀` has exactly one support functional (§2.2). -/
def IsSmoothAt (x₀ : E) : Prop :=
  ∃! φ : E →ₗ[ℝ] ℝ, IsSupportFunctional x₀ φ

open Classical in
/-- The unique support functional `φ_{x₀}` at a smooth point (any support
functional if there are several, `0` if there is none; only used at smooth
points). -/
noncomputable def supportFunctional (x₀ : E) : E →ₗ[ℝ] ℝ :=
  if h : ∃ φ, IsSupportFunctional x₀ φ then h.choose else 0

/-- A rigid motion of `E` (§2.2): continuous paths `αₓ : (-1, 1) → E` with
`αₓ(0) = x`, differentiable at `0`, and `‖αₓ(t) - α_y(t)‖ = ‖x - y‖` for all
`t ∈ (-1, 1)`.  Values outside `(-1, 1)` are irrelevant. -/
structure RigidMotion (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  α : E → ℝ → E
  continuousOn : ∀ x, ContinuousOn (α x) (Set.Ioo (-1) 1)
  zero : ∀ x, α x 0 = x
  differentiableAt : ∀ x, DifferentiableAt ℝ (α x) 0
  isometric : ∀ x y, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖α x t - α y t‖ = ‖x - y‖

/-- `η` is an infinitesimal rigid motion: `η x = αₓ'(0)` for a rigid motion `α`. -/
def IsInfRigidMotion (η : E → E) : Prop :=
  ∃ m : RigidMotion E, ∀ x, η x = deriv (m.α x) 0

variable {V : Type*}

/-- The normalised vector `(p v - p w) / ‖p v - p w‖`. -/
noncomputable def normalised (p : V → E) (v w : V) : E :=
  ‖p v - p w‖⁻¹ • (p v - p w)

/-- `(G, p)` is a framework in `E` (§2.3): for each edge `vw`, `p v ≠ p w` and the
norm is smooth at the normalised vector. -/
def IsFramework (G : SimpleGraph V) (p : V → E) : Prop :=
  ∀ v w, G.Adj v w → p v ≠ p w ∧ IsSmoothAt (normalised p v w)

/-- Well-positioned placements: the set `W(G, E)` of `p` for which `(G, p)` is a
framework. -/
def W (G : SimpleGraph V) : Set (V → E) := {p | IsFramework G p}

/-- `u` is a trivial infinitesimal flex of `(G, p)`: `u v = η (p v)` for an
infinitesimal rigid motion `η` (§2.3). -/
def IsTrivialFlex (p : V → E) (u : V → E) : Prop :=
  ∃ η, IsInfRigidMotion η ∧ ∀ v, u v = η (p v)

open Classical in
/-- The rigidity matrix `R(G, p)` (§2.3): rows indexed by edges, columns by
`V × [d]`; the `(e, (v, i))` entry is `φ_{v,w}(bᵢ)` if `e = vw`, else `0`, where
`φ_{v,w}` is the support functional at the normalised vector of `p v - p w`. -/
noncomputable def rigidityMatrix {d : ℕ} (b : Fin d → E) (G : SimpleGraph V) (p : V → E) :
    Matrix G.edgeSet (V × Fin d) ℝ :=
  fun e vi =>
    if h : vi.1 ∈ (e : Sym2 V) then supportFunctional (normalised p vi.1 (Sym2.Mem.other h)) (b vi.2)
    else 0

/-- The displacement field of a vector `u ∈ ℝ^{V × [d]}`. -/
def displacement {d : ℕ} (b : Fin d → E) (u : V × Fin d → ℝ) : V → E :=
  fun v => ∑ i, u (v, i) • b i

variable [Fintype V]

/-- Infinitesimal rigidity (§2.3): `(G, p)` is a framework and the kernel of the
rigidity matrix consists of trivial infinitesimal flexes only. -/
def IsInfRigid {d : ℕ} (b : Fin d → E) (G : SimpleGraph V) (p : V → E) : Prop :=
  IsFramework G p ∧
    ∀ u : V × Fin d → ℝ, rigidityMatrix b G p *ᵥ u = 0 → IsTrivialFlex p (displacement b u)

/-- An edge-redundantly rigid framework (§5): infinitesimally rigid, and the
framework obtained by deleting any single edge is infinitesimally rigid. -/
def IsEdgeRedundantlyRigidFramework {d : ℕ} (b : Fin d → E) (G : SimpleGraph V) (p : V → E) :
    Prop :=
  IsInfRigid b G p ∧ ∀ e ∈ G.edgeSet, IsInfRigid b (G.deleteEdges {e}) p

/-- `G` is edge-redundantly rigid in `E` (§5): some framework `(G, p)` in `E` is
edge-redundantly rigid. -/
def EdgeRedundantlyRigidIn {d : ℕ} (b : Fin d → E) (G : SimpleGraph V) : Prop :=
  ∃ p : V → E, IsEdgeRedundantlyRigidFramework b G p

end General

/-- The standard basis of `ℝ^d`. -/
noncomputable def stdBasis (d : ℕ) : Fin d → (Fin d → ℝ) := fun i => Pi.single i 1

/-- `G` is edge-redundantly rigid in `ℓ∞^d = (ℝ^d, ‖·‖∞)`. -/
def EdgeRedundantlyRigid {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  EdgeRedundantlyRigidIn (E := Fin d → ℝ) (stdBasis d) G

/-- The complete graph `Kₙ`. -/
def completeGraph (n : ℕ) : SimpleGraph (Fin n) := ⊤

/-- Conjecture 5.4 of Cruickshank–Dewar–Kitson: for every `d ≥ 2` and every
`n ≥ 2d + 2`, the complete graph `Kₙ` is edge-redundantly rigid in `ℓ∞^d`. -/
def Conjecture : Prop :=
  ∀ d n : ℕ, 2 ≤ d → 2 * d + 2 ≤ n → EdgeRedundantlyRigid (completeGraph n) d

end CDK
```

## LinfBridge.lean

```lean
import CdkDefs
import K8Comb
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# From edge-redundant rigidity in `ℓ∞^d` to the cut condition

For `ℓ∞^d = (Fin d → ℝ, sup norm)`:

* `dom_of_smooth`: if the norm is smooth at a unit vector `x₀`, then `x₀` has a
  unique coordinate of largest absolute value (`Dom x₀ k`);
* `supportFunctional_eq`: at such a point the support functional is
  `y ↦ x₀ k * y k`;
* `infRigidMotion_const`: every infinitesimal rigid motion of `ℓ∞^d` is constant
  (a translation);
* `good_of_edgeRedundant`: if `(Kₙ, p)` is an edge-redundantly rigid framework in
  `ℓ∞^d`, then every pair has a dominant coordinate, and for every edge `uv`,
  cut and coordinate `k` some edge other than `uv` crossing the cut has colour `k`.
-/

set_option linter.unusedSimpArgs false

namespace CDK

open K8 Filter Topology Matrix

variable {d : ℕ}

/-! ### Norm facts in `ℓ∞^d` -/

theorem norm_eq_of_dom {x : Fin d → ℝ} {k : Fin d} (h : Dom x k) : ‖x‖ = |x k| := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    by_cases hj : j = k
    · rw [hj]
    · exact (h j hj).le
  · have := norm_le_pi_norm x k
    rwa [Real.norm_eq_abs] at this

theorem abs_le_norm (x : Fin d → ℝ) (j : Fin d) : |x j| ≤ ‖x‖ := by
  have := norm_le_pi_norm x j
  rwa [Real.norm_eq_abs] at this

theorem exists_max_coord {x : Fin d → ℝ} (hx : ‖x‖ = 1) :
    ∃ k, ‖x‖ = |x k| ∧ ∀ j, |x j| ≤ |x k| := by
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · exfalso
    have : x = 0 := Subsingleton.elim _ _
    rw [this, norm_zero] at hx
    exact zero_ne_one hx
  · obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|) Finset.univ_nonempty
    refine ⟨k, le_antisymm ?_ (abs_le_norm x k), fun j => hk j (Finset.mem_univ _)⟩
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    exact hk j (Finset.mem_univ _)

theorem single_apply_self (k : Fin d) : (Pi.single k (1 : ℝ) : Fin d → ℝ) k = 1 := by
  simp

theorem single_apply_ne {k j : Fin d} (h : j ≠ k) : (Pi.single k (1 : ℝ) : Fin d → ℝ) j = 0 := by
  simp [Pi.single_apply, h]

theorem norm_single_one (k : Fin d) : ‖(Pi.single k (1 : ℝ) : Fin d → ℝ)‖ = 1 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    by_cases h : j = k
    · rw [h, single_apply_self]; simp
    · rw [single_apply_ne h]; simp
  · have := abs_le_norm (Pi.single k (1 : ℝ) : Fin d → ℝ) k
    rwa [single_apply_self, abs_one] at this

/-- The functional `y ↦ a * y k`. -/
def coordFun (a : ℝ) (k : Fin d) : (Fin d → ℝ) →ₗ[ℝ] ℝ := a • LinearMap.proj k

@[simp] theorem coordFun_apply (a : ℝ) (k : Fin d) (y : Fin d → ℝ) : coordFun a k y = a * y k := by
  simp [coordFun]

theorem dualNorm_coordFun {a : ℝ} (ha : |a| = 1) (k : Fin d) : dualNorm (coordFun a k) = 1 := by
  unfold dualNorm
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨_, Pi.single k 1, by simp [norm_single_one], rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hy
    simp only [coordFun_apply, abs_mul, ha, one_mul]
    rw [← hy]; exact abs_le_norm y k
  · intro w hw
    refine ⟨_, ⟨Pi.single k 1, by simp [norm_single_one], rfl⟩, ?_⟩
    simp only [coordFun_apply, single_apply_self, mul_one, ha]
    exact hw

theorem isSupport_coordFun {x₀ : Fin d → ℝ} {k : Fin d} (hk : |x₀ k| = 1) :
    IsSupportFunctional x₀ (coordFun (x₀ k) k) := by
  refine ⟨?_, dualNorm_coordFun hk k⟩
  rw [coordFun_apply, ← abs_mul_abs_self, hk, one_mul]

/-- In `ℓ∞^d`, smoothness at a unit vector forces a unique dominant coordinate. -/
theorem dom_of_smooth {x₀ : Fin d → ℝ} (hx : ‖x₀‖ = 1) (hs : IsSmoothAt x₀) : ∃ k, Dom x₀ k := by
  obtain ⟨k, hk, hmax⟩ := exists_max_coord hx
  refine ⟨k, fun j hj => ?_⟩
  by_contra hle
  have hjk : |x₀ j| = |x₀ k| := le_antisymm (hmax j) (not_lt.mp hle)
  have h1 : |x₀ k| = 1 := by rw [← hk, hx]
  have hsk := isSupport_coordFun (x₀ := x₀) h1
  have hsj := isSupport_coordFun (x₀ := x₀) (k := j) (by rw [hjk, h1])
  have heq := hs.unique hsk hsj
  have := LinearMap.congr_fun heq (Pi.single k 1)
  rw [coordFun_apply, coordFun_apply, single_apply_self, single_apply_ne hj, mul_one,
    mul_zero] at this
  rw [this, abs_zero] at h1
  exact zero_ne_one h1

theorem sum_single (y : Fin d → ℝ) : ∑ i, y i • (Pi.single i (1 : ℝ) : Fin d → ℝ) = y := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem linear_apply_eq (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ) (y : Fin d → ℝ) :
    φ y = ∑ i, y i * φ (Pi.single i 1) := by
  conv_lhs => rw [← sum_single y]
  rw [map_sum]
  simp [map_smul, smul_eq_mul]

/-- In `ℓ∞^d`, the support functionals at a unit vector with dominant coordinate
`k` are exactly `y ↦ x₀ k * y k`. -/
theorem support_formula {x₀ : Fin d → ℝ} {k : Fin d} (hx : ‖x₀‖ = 1) (hk : Dom x₀ k)
    {φ : (Fin d → ℝ) →ₗ[ℝ] ℝ} (hφ : IsSupportFunctional x₀ φ) (y : Fin d → ℝ) :
    φ y = x₀ k * y k := by
  have h1 : |x₀ k| = 1 := by rw [← norm_eq_of_dom hk, hx]
  have hbdd : BddAbove ((fun x => |φ x|) '' Metric.sphere (0 : Fin d → ℝ) 1) := by
    by_contra hb
    have := Real.sSup_of_not_bddAbove hb
    have h2 := hφ.2
    unfold dualNorm at h2
    rw [this] at h2
    exact zero_ne_one h2
  have hbound : ∀ y : Fin d → ℝ, ‖y‖ = 1 → |φ y| ≤ 1 := by
    intro y hy
    have := le_csSup hbdd ⟨y, by simpa using hy, rfl⟩
    have h2 := hφ.2
    unfold dualNorm at h2
    rwa [h2] at this
  -- `φ` vanishes on the other basis vectors
  have hzero : ∀ j, j ≠ k → φ (Pi.single j 1) = 0 := by
    intro j hj
    have hδ : 0 < 1 - |x₀ j| := by have := hk j hj; linarith
    have hnorm : ∀ s : ℝ, |s| = 1 → ‖x₀ + (s * (1 - |x₀ j|)) • Pi.single j 1‖ = 1 := by
      intro s hs
      apply le_antisymm
      · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
        rw [Real.norm_eq_abs]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        by_cases hi : i = j
        · subst hi
          rw [single_apply_self, mul_one]
          calc |x₀ i + s * (1 - |x₀ i|)| ≤ |x₀ i| + |s * (1 - |x₀ i|)| := abs_add_le _ _
            _ = 1 := by rw [abs_mul, hs, one_mul, abs_of_pos hδ]; ring
        · rw [single_apply_ne hi, mul_zero, add_zero, ← h1]
          by_cases hik : i = k
          · rw [hik]
          · exact (hk i hik).le
      · have := abs_le_norm (x₀ + (s * (1 - |x₀ j|)) • Pi.single j 1) k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, single_apply_ne (Ne.symm hj),
          mul_zero, add_zero, h1] at this
        exact this
    have hp := hbound _ (hnorm 1 (by simp))
    have hm := hbound _ (hnorm (-1) (by simp))
    rw [map_add, map_smul, hφ.1, smul_eq_mul] at hp hm
    have hp' := (abs_le.mp hp).2
    have hm' := (abs_le.mp hm).2
    have : (1 - |x₀ j|) * φ (Pi.single j 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  have hsum : ∀ y : Fin d → ℝ, φ y = y k * φ (Pi.single k 1) := by
    intro y
    rw [linear_apply_eq φ y, Finset.sum_eq_single k]
    · intro j _ hj; rw [hzero j hj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hk1 : φ (Pi.single k 1) = x₀ k := by
    have h0 := hφ.1
    rw [hsum x₀] at h0
    have hsq : x₀ k * x₀ k = 1 := by rw [← abs_mul_abs_self, h1, one_mul]
    calc φ (Pi.single k 1) = (x₀ k * x₀ k) * φ (Pi.single k 1) := by rw [hsq, one_mul]
      _ = x₀ k * (x₀ k * φ (Pi.single k 1)) := by ring
      _ = x₀ k := by rw [h0, mul_one]
  rw [hsum y, hk1, mul_comm]

theorem supportFunctional_eq {x₀ : Fin d → ℝ} {k : Fin d} (hx : ‖x₀‖ = 1) (hk : Dom x₀ k)
    (y : Fin d → ℝ) : supportFunctional x₀ y = x₀ k * y k := by
  have h1 : |x₀ k| = 1 := by rw [← norm_eq_of_dom hk, hx]
  have hex : ∃ φ, IsSupportFunctional x₀ φ := ⟨_, isSupport_coordFun h1⟩
  unfold supportFunctional
  rw [dite_eq_left hex]
  exact support_formula hx hk hex.choose_spec y

/-! ### Normalised vectors -/

theorem norm_normalised {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Type*}
    {p : V → E} {v w : V} (h : p v ≠ p w) : ‖normalised p v w‖ = 1 := by
  unfold normalised
  have h0 : ‖p v - p w‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ h0]

theorem normalised_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Type*}
    (p : V → E) (v w : V) : normalised p w v = -normalised p v w := by
  unfold normalised
  rw [norm_sub_rev, ← smul_neg, neg_sub]

theorem dom_smul_iff {x : Fin d → ℝ} {c : ℝ} (hc : 0 < c) {k : Fin d} :
    Dom (c • x) k ↔ Dom x k := by
  unfold Dom
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc]
  constructor
  · intro h j hj; exact lt_of_mul_lt_mul_left (h j hj) hc.le
  · intro h j hj; exact mul_lt_mul_of_pos_left (h j hj) hc

theorem dom_normalised_iff {V : Type*} {p : V → Fin d → ℝ} {v w : V} (h : p v ≠ p w) {k : Fin d} :
    Dom (normalised p v w) k ↔ Dom (p v - p w) k := by
  unfold normalised
  exact dom_smul_iff (inv_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr h)))

/-- For an edge of a framework in `ℓ∞^d`: a dominant coordinate `c` of `p v - p w`
and a sign `s` such that the support functionals of the two orientations are
`y ↦ s * y c` and `y ↦ -s * y c`. -/
theorem edge_functionals {V : Type*} {p : V → Fin d → ℝ} {v w : V} (hne : p v ≠ p w)
    (hs : IsSmoothAt (normalised p v w)) :
    ∃ c s, Dom (p v - p w) c ∧ (∀ y, supportFunctional (normalised p v w) y = s * y c) ∧
      (∀ y, supportFunctional (normalised p w v) y = -s * y c) := by
  have hn := norm_normalised hne
  obtain ⟨c, hc⟩ := dom_of_smooth hn hs
  refine ⟨c, normalised p v w c, (dom_normalised_iff hne).mp hc,
    fun y => supportFunctional_eq hn hc y, fun y => ?_⟩
  have hn' : ‖normalised p w v‖ = 1 := norm_normalised (Ne.symm hne)
  have hc' : Dom (normalised p w v) c := by rw [normalised_swap]; exact hc.neg
  rw [supportFunctional_eq hn' hc' y, normalised_swap]
  simp

/-! ### Infinitesimal rigid motions of `ℓ∞^d` are translations -/

theorem coord_deriv_zero {g : ℝ → Fin d → ℝ} {k : Fin d} (hdom : Dom (g 0) k) (hk : g 0 k ≠ 0)
    (hdiff : DifferentiableAt ℝ g 0) (hnorm : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖g t‖ = ‖g 0‖) :
    deriv g 0 k = 0 := by
  have hc : ContinuousAt g 0 := hdiff.continuousAt
  have hci : ∀ i, ContinuousAt (fun t => g t i) 0 := fun i =>
    (continuous_apply i).continuousAt.comp hc
  have hev1 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, j ≠ k → |g t j| < |g t k| := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = k
    · exact Filter.Eventually.of_forall fun _ h => absurd hj h
    · exact ((hci j).abs.eventually_lt (hci k).abs (hdom j hj)).mono fun _ h _ => h
  have hpos : 0 < |g 0 k| := abs_pos.mpr hk
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℝ), |g t k - g 0 k| < |g 0 k| := by
    have : ContinuousAt (fun t => |g t k - g 0 k|) 0 :=
      ((hci k).sub continuousAt_const).abs
    exact this.eventually_lt continuousAt_const (by simpa using hpos)
  have hev3 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Set.Ioo (-1 : ℝ) 1 :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hconst : (fun t => g t k) =ᶠ[𝓝 0] fun _ => g 0 k := by
    filter_upwards [hev1, hev2, hev3] with t h1 h2 h3
    have e1 : ‖g t‖ = |g t k| := norm_eq_of_dom h1
    have e0 : ‖g 0‖ = |g 0 k| := norm_eq_of_dom hdom
    have habs : |g t k| = |g 0 k| := by rw [← e1, ← e0, hnorm t h3]
    rcases abs_eq_abs.mp habs with h | h
    · exact h
    · exfalso
      rw [h] at h2
      have : |-g 0 k - g 0 k| = 2 * |g 0 k| := by
        rw [show -g 0 k - g 0 k = -(2 * g 0 k) by ring, abs_neg, abs_mul]; norm_num
      linarith
  have hd : HasDerivAt (fun t => g t k) (deriv g 0 k) 0 :=
    (hasDerivAt_pi.mp hdiff.hasDerivAt) k
  have hd' : HasDerivAt (fun _ : ℝ => g 0 k) (deriv g 0 k) 0 :=
    hd.congr_of_eventuallyEq hconst.symm
  exact hd'.unique (hasDerivAt_const 0 _)

theorem infRigidMotion_coord {η : (Fin d → ℝ) → Fin d → ℝ} (h : IsInfRigidMotion η)
    {x z : Fin d → ℝ} {k : Fin d} (hdom : Dom (z - x) k) (hk : (z - x) k ≠ 0) : η z k = η x k := by
  obtain ⟨m, hm⟩ := h
  let g : ℝ → Fin d → ℝ := fun t => m.α z t - m.α x t
  have hg0 : g 0 = z - x := by simp [g, m.zero]
  have hdiff : DifferentiableAt ℝ g 0 := (m.differentiableAt z).sub (m.differentiableAt x)
  have hnorm : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖g t‖ = ‖g 0‖ := by
    intro t ht
    rw [hg0]
    exact m.isometric z x t ht
  have := coord_deriv_zero (g := g) (by rw [hg0]; exact hdom) (by rw [hg0]; exact hk) hdiff hnorm
  have hder : deriv g 0 = deriv (m.α z) 0 - deriv (m.α x) 0 :=
    deriv_sub (m.differentiableAt z) (m.differentiableAt x)
  rw [hder, Pi.sub_apply, sub_eq_zero] at this
  rw [hm z, hm x]; exact this

/-- Every infinitesimal rigid motion of `ℓ∞^d` is constant. -/
theorem infRigidMotion_const {η : (Fin d → ℝ) → Fin d → ℝ} (h : IsInfRigidMotion η)
    (x y : Fin d → ℝ) : η x = η y := by
  funext k
  set M : ℝ := 2 * ‖x - y‖ + 1 with hM
  have hMpos : 0 < M := by have := norm_nonneg (x - y); linarith
  let z : Fin d → ℝ := x + M • Pi.single k 1
  have hzx : z - x = M • Pi.single k 1 := by simp [z]
  have hzy : ∀ i, (z - y) i = (x - y) i + M * (Pi.single k (1 : ℝ) : Fin d → ℝ) i := by
    intro i; simp [z]; ring
  have h1 : η z k = η x k := by
    apply infRigidMotion_coord h
    · intro j hj
      rw [hzx]
      simp [Pi.smul_apply, single_apply_ne hj, single_apply_self, abs_of_pos hMpos, hMpos]
    · rw [hzx]; simp [hMpos.ne']
  have hyk : (z - y) k = (x - y) k + M := by rw [hzy, single_apply_self, mul_one]
  have hbig : ‖x - y‖ < (z - y) k := by
    rw [hyk]
    have := abs_le_norm (x - y) k
    have := neg_abs_le ((x - y) k)
    linarith
  have h2 : η z k = η y k := by
    apply infRigidMotion_coord h
    · intro j hj
      rw [hzy, single_apply_ne hj, mul_zero, add_zero, abs_of_pos
        (lt_of_le_of_lt (norm_nonneg _) hbig)]
      exact lt_of_le_of_lt (abs_le_norm _ j) hbig
    · exact ne_of_gt (lt_of_le_of_lt (norm_nonneg _) hbig)
  rw [← h1, h2]

/-! ### The cut condition -/

theorem displacement_std {V : Type*} (u : V × Fin d → ℝ) (v : V) :
    displacement (stdBasis d) u v = fun i => u (v, i) := by
  unfold displacement stdBasis
  exact sum_single _

theorem other_left {V : Type*} {v w : V} (h : v ∈ s(v, w)) : Sym2.Mem.other h = w :=
  Sym2.congr_right.mp (Sym2.other_spec h)

theorem other_right {V : Type*} {v w : V} (h : w ∈ s(v, w)) : Sym2.Mem.other h = v := by
  exact Sym2.congr_right.mp ((Sym2.other_spec h).trans Sym2.eq_swap)

/-- The row of the rigidity matrix at an edge `vw` of a framework in `ℓ∞^d`:
`(R(G, p) u)_{vw} = s * (u (v, c) - u (w, c))`, where `c` is the dominant
coordinate of `p v - p w` and `s = ±1`. -/
theorem mulVec_edge {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    {p : V → Fin d → ℝ} (hfw : IsFramework H p) {v w : V} (hadj : H.Adj v w) :
    ∃ c s, Dom (p v - p w) c ∧ s ≠ 0 ∧ ∀ u : V × Fin d → ℝ,
      (rigidityMatrix (stdBasis d) H p *ᵥ u) ⟨s(v, w), hadj⟩ = s * (u (v, c) - u (w, c)) := by
  obtain ⟨hne, hs⟩ := hfw v w hadj
  obtain ⟨c, s, hdom, hφ, hφ'⟩ := edge_functionals hne hs
  have hs0 : s ≠ 0 := by
    have hn := norm_normalised hne
    have hc : Dom (normalised p v w) c := (dom_normalised_iff hne).mpr hdom
    have h1 : |normalised p v w c| = 1 := by rw [← norm_eq_of_dom hc, hn]
    intro h0
    have := (hφ (Pi.single c 1))
    rw [h0, zero_mul, supportFunctional_eq hn hc, single_apply_self, mul_one] at this
    rw [this, abs_zero] at h1
    exact zero_ne_one h1
  refine ⟨c, s, hdom, hs0, fun u => ?_⟩
  set e : H.edgeSet := ⟨s(v, w), hadj⟩
  have hvw' : (e : Sym2 V) = s(v, w) := rfl
  have hvw_ne : v ≠ w := hadj.ne
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  have hrow : ∀ x : V, ∑ i, rigidityMatrix (stdBasis d) H p e (x, i) * u (x, i) =
      if x = v then s * u (v, c) else if x = w then -s * u (w, c) else 0 := by
    intro x
    have hcoef : ∀ (z : Fin d → ℝ) (a : ℝ), (∀ y, supportFunctional z y = a * y c) →
        ∑ i, supportFunctional z (stdBasis d i) * u (x, i) = a * u (x, c) := by
      intro z a hz
      simp only [hz, stdBasis]
      rw [Finset.sum_eq_single c]
      · rw [single_apply_self, mul_one]
      · intro j _ hj; rw [single_apply_ne (Ne.symm hj)]; ring
      · intro h; exact absurd (Finset.mem_univ c) h
    by_cases hxv : x = v
    · subst hxv
      rw [ite_eq_left rfl]
      have hmem : x ∈ (e : Sym2 V) := Sym2.mem_mk_left _ _
      have : ∀ i, rigidityMatrix (stdBasis d) H p e (x, i) =
          supportFunctional (normalised p x w) (stdBasis d i) := by
        intro i
        unfold rigidityMatrix
        rw [dite_eq_left hmem]
        rw [other_left hmem]
      simp only [this]
      exact hcoef _ _ hφ
    · rw [ite_eq_right hxv]
      by_cases hxw : x = w
      · subst hxw
        rw [ite_eq_left rfl]
        have hmem : x ∈ (e : Sym2 V) := Sym2.mem_mk_right _ _
        have : ∀ i, rigidityMatrix (stdBasis d) H p e (x, i) =
            supportFunctional (normalised p x v) (stdBasis d i) := by
          intro i
          unfold rigidityMatrix
          rw [dite_eq_left hmem]
          rw [other_right hmem]
        simp only [this]
        exact hcoef _ _ hφ'
      · rw [ite_eq_right hxw]
        have hnm : x ∉ (e : Sym2 V) := by
          rw [hvw', Sym2.mem_iff]; exact fun h => h.elim hxv hxw
        apply Finset.sum_eq_zero
        intro i _
        unfold rigidityMatrix
        rw [dite_eq_right hnm, zero_mul]
  rw [Finset.sum_congr rfl fun x _ => hrow x]
  rw [Fintype.sum_eq_add v w hvw_ne]
  · rw [ite_eq_left rfl, ite_eq_right (Ne.symm hvw_ne), ite_eq_left rfl]; ring
  · intro x hx
    rw [ite_eq_right hx.1, ite_eq_right hx.2]

/-- An indicator flex: if no edge of `H` with colour `k` crosses the cut `S`,
then the vector equal to `1` in coordinate `k` on `S` and `0` elsewhere lies in
the kernel of the rigidity matrix. -/
theorem indicator_in_kernel {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    {p : V → Fin d → ℝ} (hfw : IsFramework H p) (S : Finset V) (k : Fin d)
    (hno : ∀ a ∈ S, ∀ b, b ∉ S → H.Adj a b → ¬ Dom (p b - p a) k) :
    rigidityMatrix (stdBasis d) H p *ᵥ (fun xi => if xi.2 = k ∧ xi.1 ∈ S then 1 else 0) = 0 := by
  funext e
  obtain ⟨⟨v, w⟩, hvw⟩ := Quot.exists_rep (e : Sym2 V)
  have hadj : H.Adj v w := by
    have := e.2
    rw [← hvw] at this
    exact this
  have he : e = ⟨s(v, w), hadj⟩ := Subtype.ext hvw.symm
  obtain ⟨c, s, hdom, -, hrow⟩ := mulVec_edge hfw hadj
  rw [he, hrow, Pi.zero_apply]
  by_cases hck : c = k
  · subst hck
    by_cases hv : v ∈ S <;> by_cases hw : w ∈ S
    · simp [hv, hw]
    · exact absurd hdom.sub_comm (hno v hv w hw hadj)
    · exact absurd hdom (hno w hw v hv hadj.symm)
    · simp [hv, hw]
  · simp [hck]

/-- Consequences of edge-redundant rigidity of `(Kₙ, p)` in `ℓ∞^d`. -/
theorem good_of_edgeRedundant {n : ℕ} {p : Fin n → Fin d → ℝ}
    (h : IsEdgeRedundantlyRigidFramework (stdBasis d) (completeGraph n) p) :
    (∀ u v : Fin n, u ≠ v → ∃ k, Dom (p v - p u) k) ∧
    (∀ u v : Fin n, u ≠ v → ∀ (S : Finset (Fin n)) (k : Fin d), (∃ a, a ∈ S) → (∃ b, b ∉ S) →
      ∃ a ∈ S, ∃ b, b ∉ S ∧ ¬ (a = u ∧ b = v) ∧ ¬ (a = v ∧ b = u) ∧ Dom (p b - p a) k) := by
  obtain ⟨⟨hfw, -⟩, hdel⟩ := h
  constructor
  · intro u v huv
    have hadj : (completeGraph n).Adj v u := Ne.symm huv
    obtain ⟨hne, hs⟩ := hfw v u hadj
    obtain ⟨k, hk⟩ := dom_of_smooth (norm_normalised hne) hs
    exact ⟨k, (dom_normalised_iff hne).mp hk⟩
  · intro u v huv S k ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩
    by_contra hno
    push Not at hno
    have hmem : s(u, v) ∈ (completeGraph n).edgeSet := by
      rw [SimpleGraph.mem_edgeSet]; exact huv
    obtain ⟨hfw', hker⟩ := hdel _ hmem
    have hno' : ∀ a ∈ S, ∀ b, b ∉ S → ((completeGraph n).deleteEdges {s(u, v)}).Adj a b →
        ¬ Dom (p b - p a) k := by
      intro a ha b hb hab
      rw [SimpleGraph.deleteEdges_adj] at hab
      apply hno a ha b hb
      · intro h1 h2; apply hab.2; rw [h1, h2]; exact Set.mem_singleton _
      · intro h1 h2; apply hab.2; rw [h1, h2, Sym2.eq_swap]; exact Set.mem_singleton _
    obtain ⟨η, hη, hu⟩ := hker _ (indicator_in_kernel hfw' S k hno')
    have ha := hu a₀
    have hb := hu b₀
    rw [displacement_std] at ha hb
    have := congr_fun (ha.trans ((infRigidMotion_const hη (p a₀) (p b₀)).trans hb.symm)) k
    simp [ha₀, hb₀] at this

end CDK
```

## K8Main.lean

```lean
import LinfBridge
import K8Sound
import K8Wlog
import K8Cert07

/-!
# Main theorem: `K₈` is not edge-redundantly rigid in `ℓ∞³`

Hence Conjecture 5.4 of Cruickshank, Dewar and Kitson fails at `d = 3`, `n = 8`.

Chain of the proof:
1. `CDK.good_of_edgeRedundant` (`LinfBridge`): an edge-redundantly rigid framework
   `(K₈, p)` in `ℓ∞³` is `K8.Good`.
2. `K8.exists_anchored` (`K8Wlog`): a good placement can be normalised by an
   isometry of `ℓ∞³` and a relabelling to an anchored good placement.
3. `K8.base_of_good` (`K8Sound`): the induced assignment satisfies every clause
   of the propositional instance `K8.Base`.
4. `K8.Cert.cert_unsat` (`K8Cert00`–`K8Cert07`): no assignment satisfies
   `K8.Base` (kernel-checked RUP certificate).
-/

namespace CDK

/-- No placement of eight points in `ℝ³` satisfies the combinatorial
consequences of edge-redundant rigidity. -/
theorem k8_no_good : ¬ ∃ p : Fin 8 → Fin 3 → ℝ, K8.Good p := by
  rintro ⟨p, hp⟩
  obtain ⟨q, hq, ha⟩ := K8.exists_anchored hp
  exact K8.Cert.cert_unsat _ (K8.base_of_good hq ha)

/-- **Main theorem.** The complete graph `K₈` is not edge-redundantly rigid in `ℓ∞³`. -/
theorem not_edgeRedundantlyRigid_K8 : ¬ EdgeRedundantlyRigid (completeGraph 8) 3 := by
  rintro ⟨p, hp⟩
  obtain ⟨h1, h2⟩ := good_of_edgeRedundant hp
  exact k8_no_good ⟨p, ⟨h1, h2⟩⟩

/-- Conjecture 5.4 of Cruickshank–Dewar–Kitson is false. -/
theorem not_conjecture : ¬ Conjecture := fun h =>
  not_edgeRedundantlyRigid_K8 (h 3 8 (by norm_num) (by norm_num))

end CDK
```

## Review369595.lean

```lean
import K8Main

/-!
# The reviewer's endpoint

The definitions in the namespace `Review369595` are copied verbatim from
REVIEW-369595.md, §6 (the coordinate-specialised form of the source
definitions: flexes are vectors whose `i`-th coordinates agree across each edge
of colour `i`, trivial flexes are translations).  Both `K8Endpoint` and
`RefutationEndpoint` are proved, through the same combinatorial core
`CDK.k8_no_good`.
-/

namespace Review369595

abbrev Placement (n d : ℕ) := Fin n → Fin d → ℝ
abbrev EdgeRel (n : ℕ) := Fin n → Fin n → Prop

def complete (n : ℕ) : EdgeRel n := fun v w => v ≠ w

def removeEdge {n : ℕ} (E : EdgeRel n) (v w : Fin n) : EdgeRel n :=
  fun a b => E a b ∧ ¬ ((a = v ∧ b = w) ∨ (a = w ∧ b = v))

def Dominates {n d : ℕ} (p : Placement n d) (v w : Fin n) (i : Fin d) : Prop :=
  0 < |p v i - p w i| ∧
    ∀ j : Fin d, j ≠ i → |p v j - p w j| < |p v i - p w i|

def WellPositioned {n d : ℕ} (E : EdgeRel n) (p : Placement n d) : Prop :=
  ∀ v w : Fin n, E v w → ∃ i : Fin d, Dominates p v w i

def Flex {n d : ℕ} (E : EdgeRel n) (p u : Placement n d) : Prop :=
  ∀ (v w : Fin n) (i : Fin d), E v w → Dominates p v w i → u v i = u w i

def InfRigid {n d : ℕ} (E : EdgeRel n) (p : Placement n d) : Prop :=
  WellPositioned E p ∧
    ∀ u : Placement n d, Flex E p u → ∃ t : Fin d → ℝ, ∀ v, u v = t

def Redundant {n d : ℕ} (E : EdgeRel n) (p : Placement n d) : Prop :=
  InfRigid E p ∧ ∀ v w : Fin n, E v w → InfRigid (removeEdge E v w) p

def ERConjecture : Prop :=
  ∀ d n : ℕ, 2 ≤ d → 2 * d + 2 ≤ n →
    ∃ p : Placement n d, Redundant (complete n) p

def K8Endpoint : Prop := ¬ ∃ p : Placement 8 3, Redundant (complete 8) p
def RefutationEndpoint : Prop := ¬ ERConjecture

open K8 in
theorem good_of_redundant {p : Placement 8 3} (h : Redundant (complete 8) p) : Good p := by
  obtain ⟨⟨hwp, -⟩, hdel⟩ := h
  constructor
  · intro u v huv
    obtain ⟨i, -, hi⟩ := hwp v u (Ne.symm huv)
    exact ⟨i, fun j hj => by simpa using hi j hj⟩
  · intro u v huv S k ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩
    by_contra hno
    push Not at hno
    obtain ⟨-, hflex⟩ := hdel u v huv
    let U : Placement 8 3 := fun x i => if i = k ∧ x ∈ S then 1 else 0
    have hU : Flex (removeEdge (complete 8) u v) p U := by
      intro a b i hab hdom
      by_cases hik : i = k
      · subst hik
        have hd : Dom (p a - p b) i := fun j hj => by simpa using hdom.2 j hj
        by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
        · simp [U, ha, hb]
        · exfalso
          refine hno a ha b hb ?_ ?_ hd.sub_comm
          · intro h1 h2; exact hab.2 (Or.inl ⟨h1, h2⟩)
          · intro h1 h2; exact hab.2 (Or.inr ⟨h1, h2⟩)
        · exfalso
          refine hno b hb a ha ?_ ?_ hd
          · intro h1 h2; exact hab.2 (Or.inr ⟨h2, h1⟩)
          · intro h1 h2; exact hab.2 (Or.inl ⟨h2, h1⟩)
        · simp [U, ha, hb]
      · simp [U, hik]
    obtain ⟨t, ht⟩ := hflex U hU
    have := congr_fun ((ht a₀).trans (ht b₀).symm) k
    simp [U, ha₀, hb₀] at this

theorem k8_counterexample : K8Endpoint := by
  rintro ⟨p, hp⟩
  exact CDK.k8_no_good ⟨p, good_of_redundant hp⟩

theorem cdk_source_refuted : RefutationEndpoint := fun candidate =>
  k8_counterexample (candidate 3 8 (by decide) (by decide))

end Review369595
```

## K9Positive.lean

```lean
import LinfBridge
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.FinRange

/-!
# `K₉` is edge-redundantly rigid in `ℓ∞³`

An explicit integer placement (found by the author's exact LP search, checked
independently by the reviewer) is an edge-redundantly rigid framework in the
sense of the source definitions.  This shows that the definitions of
`CdkDefs` are not vacuous, and that `n = 2d + 2 = 8` is the only failure of
Conjecture 5.4 at `d = 3` up to `n = 9` (the extension to all `n ≥ 9` is proved
on paper only).

* every pair of points has a unique dominant coordinate, given by `colT`
  (`domZ_colT`, kernel evaluation over the integers);
* every colour class stays connected after deleting any single edge
  (`conn_check`, kernel evaluation of a reachability iteration);
* translations are infinitesimal rigid motions.
-/

namespace CDK.K9

open K8

/-- The placement, integer coordinates. -/
def P9 : Fin 9 → Fin 3 → ℤ :=
  ![![13, 5, 10], ![15, -3, 16], ![-2, -8, 7], ![19, -9, 12], ![-1, -11, 8], ![7, 3, -2],
    ![9, -17, 0], ![0, 0, -5], ![-2, -4, -3]]

noncomputable def p9 : Fin 9 → Fin 3 → ℝ := fun v i => (P9 v i : ℝ)

/-- The colour (dominant coordinate) of each pair. -/
def colT : Fin 9 → Fin 9 → Fin 3 :=
  ![![0, 1, 0, 1, 1, 2, 1, 2, 0], ![1, 0, 0, 1, 0, 2, 2, 2, 2], ![0, 0, 0, 0, 1, 1, 0, 2, 2],
    ![1, 1, 0, 0, 0, 2, 2, 0, 0], ![1, 0, 1, 0, 0, 1, 0, 2, 2], ![2, 2, 1, 2, 1, 0, 1, 0, 0],
    ![1, 2, 0, 2, 0, 1, 0, 1, 1], ![2, 2, 2, 0, 2, 0, 1, 0, 1], ![0, 2, 2, 0, 2, 0, 1, 1, 0]]

def domZ (v w : Fin 9) (k : Fin 3) : Prop :=
  ∀ j, j ≠ k → |P9 v j - P9 w j| < |P9 v k - P9 w k|

theorem domZ_colT : ∀ v w : Fin 9, v ≠ w → domZ v w (colT v w) := by
  unfold domZ; decide +kernel

theorem dom_of_domZ {v w : Fin 9} {k : Fin 3} (h : domZ v w k) : Dom (p9 v - p9 w) k := by
  intro j hj
  have := h j hj
  simp only [Pi.sub_apply, p9]
  rw [← Int.cast_sub, ← Int.cast_sub, ← Int.cast_abs, ← Int.cast_abs]
  exact_mod_cast this

/-- Smoothness at a unit vector with a dominant coordinate. -/
theorem smooth_of_dom {x₀ : Fin 3 → ℝ} {k : Fin 3} (hx : ‖x₀‖ = 1) (hk : Dom x₀ k) :
    IsSmoothAt x₀ := by
  have h1 : |x₀ k| = 1 := by rw [← norm_eq_of_dom hk, hx]
  refine ⟨coordFun (x₀ k) k, isSupport_coordFun h1, fun φ hφ => ?_⟩
  exact LinearMap.ext fun y => by rw [support_formula hx hk hφ y, coordFun_apply]

theorem not_dom_zero (k : Fin 3) : ¬ Dom (0 : Fin 3 → ℝ) k := by
  intro h
  fin_cases k
  · simpa using h 1 (by decide)
  · simpa using h 0 (by decide)
  · simpa using h 0 (by decide)

theorem framework (H : SimpleGraph (Fin 9)) : IsFramework H p9 := by
  intro v w hvw
  have hd := dom_of_domZ (domZ_colT v w hvw.ne)
  have hne : p9 v ≠ p9 w := by
    intro e
    rw [e, sub_self] at hd
    exact not_dom_zero _ hd
  exact ⟨hne, smooth_of_dom (norm_normalised hne) ((dom_normalised_iff hne).mpr hd)⟩

/-- Translations are infinitesimal rigid motions. -/
theorem isInfRigidMotion_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) :
    IsInfRigidMotion (fun _ : E => c) := by
  have hd : ∀ x : E, HasDerivAt (fun t : ℝ => x + t • c) c 0 := by
    intro x
    have := ((hasDerivAt_id (0 : ℝ)).smul_const c).const_add x
    simpa using this
  refine ⟨⟨fun x t => x + t • c, fun x => ?_, fun x => by simp, fun x => (hd x).differentiableAt,
    fun x y t _ => by simp⟩, fun x => (hd x).deriv.symm⟩
  exact (continuous_const.add (continuous_id.smul continuous_const)).continuousOn

/-! ### Connectivity of the colour classes after deleting one edge -/

/-- Edges of colour `c` other than `{a, b}`. -/
def adjB (a b : Fin 9) (c : Fin 3) (v w : Fin 9) : Bool :=
  decide (v ≠ w) && decide (colT v w = c) && !((v == a && w == b) || (v == b && w == a))

def stepL (E : Fin 9 → Fin 9 → Bool) (R : List Bool) : List Bool :=
  (List.finRange 9).map fun (w : Fin 9) =>
    R.getD w.val false || (List.finRange 9).any fun (v : Fin 9) => R.getD v.val false && E v w

/-- Vertices reachable from `0` in at most `n` steps. -/
def reachL (E : Fin 9 → Fin 9 → Bool) : ℕ → List Bool
  | 0 => (List.finRange 9).map fun w => decide (w = 0)
  | n + 1 => stepL E (reachL E n)

set_option maxRecDepth 100000 in
theorem conn_check_0 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 0 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_1 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 1 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_2 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 2 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_3 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 3 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_4 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 4 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_5 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 5 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_6 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 6 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_7 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 7 b c) 8).getD w false = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conn_check_8 : ∀ (b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB 8 b c) 8).getD w false = true := by
  decide +kernel

/-- Every colour class minus any single edge `{a, b}` is connected (for `a = b`
nothing is deleted). -/
theorem conn_check : ∀ (a b : Fin 9) (c : Fin 3) (w : Fin 9),
    (reachL (adjB a b c) 8).getD w false = true := by
  intro a
  fin_cases a
  exacts [conn_check_0, conn_check_1, conn_check_2, conn_check_3, conn_check_4, conn_check_5,
    conn_check_6, conn_check_7, conn_check_8]

theorem getD_map_finRange {β : Type*} (g : Fin 9 → β) (d : β) (w : Fin 9) :
    ((List.finRange 9).map g).getD w.val d = g w := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simp)]
  simp

theorem reach_const (E : Fin 9 → Fin 9 → Bool) (f : Fin 9 → ℝ)
    (hE : ∀ v w, E v w = true → f v = f w) :
    ∀ n (w : Fin 9), (reachL E n).getD w false = true → f w = f 0 := by
  intro n
  induction n with
  | zero =>
    intro w h
    simp only [reachL, getD_map_finRange, decide_eq_true_eq] at h
    rw [h]
  | succ n ih =>
    intro w h
    simp only [reachL, stepL, getD_map_finRange, Bool.or_eq_true, List.any_eq_true,
      Bool.and_eq_true] at h
    rcases h with h | ⟨v, -, hv, hvw⟩
    · exact ih w h
    · rw [← hE v w hvw]; exact ih v hv

theorem infRigid_of (H : SimpleGraph (Fin 9)) (a b : Fin 9)
    (hH : ∀ v w, adjB a b (colT v w) v w = true → H.Adj v w) : IsInfRigid (stdBasis 3) H p9 := by
  refine ⟨framework H, fun u hu => ?_⟩
  have hedge : ∀ c v w, adjB a b c v w = true → u (v, c) = u (w, c) := by
    intro c v w h
    have hc : colT v w = c := by
      simp only [adjB, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.2
    have hadj : H.Adj v w := hH v w (by rw [hc]; exact h)
    obtain ⟨c', s, hd, hs, hrow⟩ := mulVec_edge (framework H) hadj
    have hc' : c' = c := by
      rw [← hc]; exact hd.unique (dom_of_domZ (domZ_colT v w hadj.ne))
    have := hrow u
    rw [hu, Pi.zero_apply] at this
    rcases mul_eq_zero.mp this.symm with h0 | h0
    · exact absurd h0 hs
    · rw [← hc']; linarith
  have hconst : ∀ v i, u (v, i) = u (0, i) := fun v i =>
    reach_const _ (fun x => u (x, i)) (hedge i) 8 v (conn_check a b i v)
  refine ⟨fun _ => displacement (stdBasis 3) u 0, isInfRigidMotion_const _, fun v => ?_⟩
  rw [displacement_std, displacement_std]
  funext i
  exact hconst v i

/-- **`K₉` is edge-redundantly rigid in `ℓ∞³`.** -/
theorem k9_edgeRedundantlyRigid : EdgeRedundantlyRigid (completeGraph 9) 3 := by
  refine ⟨p9, infRigid_of _ 0 0 fun v w h => ?_, fun e he => ?_⟩
  · simp only [adjB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  · obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep e
    refine infRigid_of _ a b fun v w h => ?_
    simp only [adjB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_false_iff,
      Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨h.1.1, fun hmem => ?_⟩
    rw [Set.mem_singleton_iff, ← hab] at hmem
    have := Sym2.eq_iff.mp hmem
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases h.2.1 with h' | h' <;> contradiction
    · rcases h.2.2 with h' | h' <;> contradiction

end CDK.K9
```

## Audit.lean

```lean
import Review369595
import K9Positive

/-! Endpoint statements and their axioms. -/

#check @CDK.not_edgeRedundantlyRigid_K8
#check @CDK.not_conjecture
#check @CDK.k8_no_good
#check @Review369595.k8_counterexample
#check @Review369595.cdk_source_refuted
#check @K8.Cert.cert_unsat
#check @CDK.K9.k9_edgeRedundantlyRigid
#print CDK.Conjecture
#print CDK.EdgeRedundantlyRigid
#print CDK.EdgeRedundantlyRigidIn
#print CDK.IsEdgeRedundantlyRigidFramework
#print CDK.IsInfRigid
#print CDK.IsFramework
#print CDK.IsSmoothAt
#print CDK.IsSupportFunctional
#print CDK.dualNorm
#print CDK.IsTrivialFlex
#print CDK.IsInfRigidMotion
#print CDK.RigidMotion
#print CDK.rigidityMatrix
#print CDK.displacement
#print CDK.stdBasis
#print CDK.completeGraph
#print axioms CDK.not_edgeRedundantlyRigid_K8
#print axioms CDK.not_conjecture
#print axioms CDK.k8_no_good
#print axioms Review369595.k8_counterexample
#print axioms Review369595.cdk_source_refuted
#print axioms K8.Cert.cert_unsat
#print axioms CDK.K9.k9_edgeRedundantlyRigid
```

# Generated certificate modules

## Hashes of certificate inputs and generated modules

| File | sha256 |
|---|---|
| cert/k8.cnf | 4190b555c48292f7c68c2c1cd45a5724b172a78f17e272292dadaaa03eb000fa |
| cert/k8.prov.json | 1c79e9b442e0ab597b10452fec40a38d39cc4a246c96099e6920ebc369ec17ec |
| cert/k8.drat | 85341bf30973c3bd365b16531c967714e77fa968418dc9f99e66092eb0e4b778 |
| cert/k8.lrat | 3465515a06b33f67e2795759156a9be3708cf78cb6282b8fe752ebca7c35329e |
| src/K8Cert00.lean | b70ab28a8a22b4854f512797760cd5c8de96aca0b4ed9e438226d6bc5f80c61a |
| src/K8Cert01.lean | d534fd1cdd2136cdff8b49a2f3c86c3b617d2e895f3cd6ef0f7f0887fde407ee |
| src/K8Cert02.lean | 0b519555263b6281cdb1b093969e88fa2f21ba77310c1679554fd34e69d4f716 |
| src/K8Cert03.lean | 077c6c9abca13ca9a3102d4431344944541b05cdb316ef2744f38507131e6332 |
| src/K8Cert04.lean | e991b96e134747dbe5a663530a0179c31998bcd30b232e216c00c0d74513f2c4 |
| src/K8Cert05.lean | aa18e3ad57764137d982e2da448133b32f615fee4f1a0a155d6a434f86293cd5 |
| src/K8Cert06.lean | 87754c12cba3f359c1d11f8828d3c752db55f9bbf01614e42403b9ef955b1fcf |
| src/K8Cert07.lean | 1a8c9cd9e482f494a0d0d8e799a452bfb230138225d6adf14dbf001af4405a94 |

## scripts/k8_cnf.py

```python
#!/usr/bin/env python3
"""Generate the K8 / l_inf^3 CNF from clause provenance records.

This mirrors src/K8Cnf.lean exactly: every clause is produced from a provenance
record by the same rule as `K8.Prov.clause`, with literals in the same order.
The Lean side re-derives each clause it uses from its record by kernel
evaluation, so this script is not trusted; it only has to be deterministic.

Output: <out>.cnf (DIMACS) and <out>.prov.json (one record per clause, in order).
"""
import json, sys
from itertools import permutations

def edge_idx(u, v): return u * (15 - u) // 2 + (v - u - 1)
def col_var(u, v, c): return 1 + 3 * edge_idx(min(u, v), max(u, v)) + c
def sgn_var(u, v): return 85 + edge_idx(min(u, v), max(u, v))
def pos(x): return 2 * x
def neg(x): return 2 * x + 1
PAIRS = [(u, v) for u in range(8) for v in range(8) if u < v]
E4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
PERMS3 = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]
F, T = False, True
REPS = [
    [(0, 0, F), (1, 0, T), (3, 0, F)],
    [(0, 0, F), (1, 0, T), (3, 1, F)],
    [(0, 0, F), (1, 0, T), (4, 0, F), (5, 0, T)],
    [(0, 0, F), (1, 0, T), (4, 0, F), (5, 1, F)],
    [(0, 0, F), (1, 0, T), (4, 1, F), (5, 1, T)],
    [(0, 0, F), (1, 1, F), (4, 1, T), (5, 0, T)],
    [(0, 0, F), (1, 1, F), (2, 2, F), (3, 2, F), (4, 1, T), (5, 0, F)],
]
ANCHORS = [pos(col_var(0, 1, 0)), pos(col_var(0, 2, 0)), pos(col_var(0, 3, 0)), pos(col_var(0, 4, 1)),
           pos(col_var(0, 5, 1)), pos(col_var(0, 6, 2)), pos(col_var(0, 7, 2)),
           pos(sgn_var(0, 1)), pos(sgn_var(0, 2)), pos(sgn_var(0, 4)), pos(sgn_var(0, 6))]

def bit(S, i): return (S >> i) & 1 == 1

def pat_entry(f, tau, eps, e):
    i, c0, s = e
    a, b = E4[i]
    x, y = f[a], f[b]
    c = tau[c0]
    s2 = s ^ bit(eps, c0)
    sv = s2 ^ (y < x)
    return [neg(col_var(x, y, c)), neg(sgn_var(x, y)) if sv else pos(sgn_var(x, y))]

def clause(rec):
    kind = rec[0]
    if kind == 'alo':
        _, u, v = rec; return [pos(col_var(u, v, c)) for c in range(3)]
    if kind == 'amo':
        _, u, v, a, b = rec; return [neg(col_var(u, v, a)), neg(col_var(u, v, b))]
    if kind == 'cut':
        _, S, k, u, v = rec
        return [pos(col_var(x, y, k)) for (x, y) in PAIRS if bit(S, x) != bit(S, y) and not (x == u and y == v)]
    if kind == 'pat':
        _, r, f, t, eps = rec
        out = []
        for e in REPS[r]: out += pat_entry(f, PERMS3[t], eps, e)
        return out
    if kind == 'anchor':
        return [ANCHORS[rec[1]]]
    raise ValueError(kind)

def valid(rec):
    kind = rec[0]
    if kind == 'alo': return rec[1] < rec[2] < 8
    if kind == 'amo': return rec[1] < rec[2] < 8 and rec[3] < rec[4] < 3
    if kind == 'cut': return 0 < rec[1] < 255 and rec[2] < 3 and rec[3] < rec[4] < 8
    if kind == 'pat':
        _, r, f, t, eps = rec
        return r < 7 and t < 6 and eps < 8 and len(f) == 4 and all(x < 8 for x in f) and len(set(f)) == 4
    if kind == 'anchor': return rec[1] < 11
    return False

def records():
    for u, v in PAIRS: yield ('alo', u, v)
    for u, v in PAIRS:
        for a in range(3):
            for b in range(a + 1, 3): yield ('amo', u, v, a, b)
    for S in range(1, 128):
        for k in range(3):
            for u, v in PAIRS:
                if bit(S, u) != bit(S, v): yield ('cut', S, k, u, v)
    for r in range(7):
        for f in permutations(range(8), 4):
            for t in range(6):
                for eps in range(8): yield ('pat', r, list(f), t, eps)
    for j in range(11): yield ('anchor', j)

def dimacs(l): return l // 2 if l % 2 == 0 else -(l // 2)

def main():
    out = sys.argv[1]
    seen = set(); clauses = []; provs = []
    for rec in records():
        assert valid(rec)
        c = clause(rec)
        key = frozenset(c)
        assert len(key) == len(c)
        if key in seen: continue
        seen.add(key); clauses.append(c); provs.append(rec)
    with open(out + '.cnf', 'w') as fh:
        fh.write(f'p cnf 112 {len(clauses)}\n')
        for c in clauses: fh.write(' '.join(str(dimacs(l)) for l in c) + ' 0\n')
    with open(out + '.prov.json', 'w') as fh:
        for rec in provs: fh.write(json.dumps(rec) + '\n')
    kinds = {}
    for r in provs: kinds[r[0]] = kinds.get(r[0], 0) + 1
    print(len(clauses), 'clauses', kinds)

if __name__ == '__main__':
    main()
```

## scripts/k8_solve.py

```python
#!/usr/bin/env python3
"""Solve cert/k8.cnf with CaDiCaL 1.9.5 (PySAT) and write a DRAT proof.
Usage: k8_solve.py <cnf> <drat-out>
The proof is untrusted; it is converted to LRAT by drat-trim and then checked in Lean."""
import sys, time
from pysat.formula import CNF
from pysat.solvers import Solver
cnf = CNF(from_file=sys.argv[1])
t = time.monotonic()
with Solver(name='cadical195', bootstrap_with=cnf.clauses, with_proof=True) as s:
    res = s.solve()
    assert res is False, res
    proof = s.get_proof()
open(sys.argv[2], 'w').write('\n'.join(proof) + '\n')
print('UNSAT', len(proof), 'proof lines', f'{time.monotonic()-t:.2f}s')
```

## scripts/k8_lean_cert.py

```python
#!/usr/bin/env python3
"""Generate the Lean certificate modules src/K8CertNN.lean from
cert/k8.cnf, cert/k8.prov.json and cert/k8.lrat (deterministic).

Design: every input clause used by the LRAT proof becomes a constant `iN` with a
theorem `si N : ∀ α, Base α → Sat α iN`, proved from its provenance record by
kernel evaluation of `Prov.valid` and `Prov.clause`.  Every LRAT addition becomes
a constant `dN` with a theorem `sdN`, proved by `Rup.rupCheck_sound` applied to
the explicit list of hint clauses (checked by `decide +kernel`) and the
theorems of the hint clauses.  The last module proves `K8.cert_unsat`.

Usage: k8_lean_cert.py <steps-per-module>
"""
import hashlib, json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CNF, PROV, LRAT = ROOT / 'cert/k8.cnf', ROOT / 'cert/k8.prov.json', ROOT / 'cert/k8.lrat'
PER = int(sys.argv[1]) if len(sys.argv) > 1 else 2200
INPUT_PER = 1100

def enc(x): return 2 * x if x > 0 else 2 * (-x) + 1

def lean_prov(rec):
    k = rec[0]
    if k == 'pat':
        return f"(.pat {rec[1]} [{', '.join(map(str, rec[2]))}] {rec[3]} {rec[4]})"
    return f"(.{k} {' '.join(map(str, rec[1:]))})"

def lst(xs): return '[' + ', '.join(map(str, xs)) + ']'

HEADER = """import {imp}

/-! Generated by scripts/k8_lean_cert.py from cert/k8.cnf, cert/k8.prov.json and
cert/k8.lrat.  Do not edit. -/

set_option Elab.async false
set_option maxRecDepth 100000

namespace K8.Cert
open Rup K8
"""

def main():
    inputs = {}
    with CNF.open() as fh:
        rows = fh.read().splitlines()[1:]
    provs = [json.loads(l) for l in PROV.read_text().splitlines()]
    assert len(rows) == len(provs)
    for i, (row, rec) in enumerate(zip(rows, provs), 1):
        inputs[i] = ([enc(int(t)) for t in row.split()[:-1]], rec)
    steps = []
    for row in LRAT.read_text().splitlines():
        t = row.split()
        if t[1] == 'd':
            continue
        nums = list(map(int, t[1:])); k = nums.index(0)
        steps.append((int(t[0]), [enc(x) for x in nums[:k]], nums[k + 1:-1]))
    assert steps[-1][1] == []
    derived = {s[0] for s in steps}
    used = sorted({h for _, _, hs in steps for h in hs if h in inputs})
    for _, _, hs in steps:
        assert all(h in inputs or h in derived for h in hs)
    modules = []
    # input modules
    for m in range(0, len(used), INPUT_PER):
        body = []
        for i in used[m:m + INPUT_PER]:
            cl, rec = inputs[i]
            body.append(f"def i{i} : Clause := {lst(cl)}")
            body.append(f"theorem si{i} (α : Nat → Bool) (h : Base α) : Sat α i{i} := by\n"
                        f"  have e : Prov.valid {lean_prov(rec)} = true ∧ Prov.clause {lean_prov(rec)} = i{i} := by\n"
                        f"    decide +kernel\n"
                        f"  exact e.2 ▸ h _ e.1")
        modules.append(body)
    n_input_modules = len(modules)
    defined_at = {}
    for idx, (sid, cl, hs) in enumerate(steps):
        if idx % PER == 0:
            modules.append([])
        name = lambda h: f"i{h}" if h in inputs else f"d{h}"
        sname = lambda h: f"si{h}" if h in inputs else f"sd{h}"
        pf = ".nil"
        for h in reversed(hs):
            pf = f"(.cons ({sname(h)} α h) {pf})"
        modules[-1].append(f"def d{sid} : Clause := {lst(cl)}")
        modules[-1].append(f"theorem sd{sid} (α : Nat → Bool) (h : Base α) : Sat α d{sid} :=\n"
                           f"  rupCheck_sound (Hs := [{', '.join(name(h) for h in hs)}]) (by decide +kernel)\n"
                           f"    {pf}")
    last = steps[-1][0]
    modules[-1].append(f"/-- The propositional instance is unsatisfiable. -/\n"
                       f"theorem cert_unsat (α : Nat → Bool) (h : Base α) : False :=\n"
                       f"  not_sat_nil α (sd{last} α h)")
    manifest = {'cnf_sha256': hashlib.sha256(CNF.read_bytes()).hexdigest(),
                'prov_sha256': hashlib.sha256(PROV.read_bytes()).hexdigest(),
                'lrat_sha256': hashlib.sha256(LRAT.read_bytes()).hexdigest(),
                'input_clauses_used': len(used), 'additions': len(steps),
                'hints': sum(len(h) for _, _, h in steps), 'steps_per_module': PER,
                'input_clauses_per_module': INPUT_PER, 'modules': []}
    for old in (ROOT / 'src').glob('K8Cert[0-9]*.lean'):
        old.unlink()
    prev = 'K8Cnf'
    for n, body in enumerate(modules):
        mod = f"K8Cert{n:02d}"
        text = HEADER.format(imp=prev) + '\n' + '\n\n'.join(body) + '\n\nend K8.Cert\n'
        path = ROOT / 'src' / f'{mod}.lean'
        path.write_text(text)
        manifest['modules'].append({'module': mod, 'kind': 'input' if n < n_input_modules else 'rup',
                                    'sha256': hashlib.sha256(text.encode()).hexdigest(),
                                    'lines': text.count('\n'), 'bytes': len(text.encode())})
        prev = mod
    (ROOT / 'cert' / 'manifest.json').write_text(json.dumps(manifest, indent=1) + '\n')
    print(json.dumps({k: v for k, v in manifest.items() if k != 'modules'}))
    for m in manifest['modules']:
        print(m['module'], m['kind'], m['lines'], m['bytes'])

if __name__ == '__main__':
    main()
```

