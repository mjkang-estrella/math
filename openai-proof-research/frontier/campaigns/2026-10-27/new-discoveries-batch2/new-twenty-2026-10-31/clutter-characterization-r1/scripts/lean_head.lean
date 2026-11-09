import Mathlib

/-!
# A counterexample to Király's conjecture on orientations of nonideal clutters

MathDB 388087 ("Orientation of nonideal clutters", Egres Open; Király's conjecture as stated in
J. Pap, EGRES TR-2010-09, Conjecture 1.2, and Pap's PhD thesis, Conjecture 3.4.5):

  Let `C` be a clutter on a finite ground set `V` and `B` its blocker. Then `C` is nonideal
  if and only if there exist `p : C → V`, `q : B → V` with `p X ∈ X`, `q Y ∈ Y`, and
  `p X = q Y → |X ∩ Y| > 1`.

We exhibit an 11-element clutter (the eleven 3-sets of a cubic `(11,3,4)` Lehman matrix) which is
nonideal (`(1/3,…,1/3)` is a non-integral extreme point of its covering polyhedron) and admits no
such pair `(p, q)`.  Hence the conjecture (its "only if"/nonideal ⇒ orientation direction) is false.

Definitions follow the sources: a clutter is a family of pairwise incomparable sets; the blocker is
the family of inclusion-minimal transversals; the covering polyhedron is
`P(C) = {x ∈ ℝ^V : x ≥ 0, x(X) ≥ 1 ∀ X ∈ C}` and `C` is ideal iff `P(C)` is integral, i.e. every
extreme point (vertex) of `P(C)` is an integer vector.
-/

namespace KiralyClutter

open Finset

section Definitions

variable {V : Type} [DecidableEq V]

/-- A clutter: no member contains another. -/
def IsClutter (C : Finset (Finset V)) : Prop :=
  ∀ X ∈ C, ∀ Y ∈ C, X ⊆ Y → X = Y

/-- `T` meets every member of `C`. -/
def IsTransversal (C : Finset (Finset V)) (T : Finset V) : Prop :=
  ∀ X ∈ C, (X ∩ T).Nonempty

/-- The blocker `b(C)`: the inclusion-minimal transversals of `C`. -/
def blocker (C : Finset (Finset V)) : Set (Finset V) :=
  {T | IsTransversal C T ∧ ∀ T' : Finset V, T' ⊂ T → ¬ IsTransversal C T'}

/-- The covering polyhedron `P(C) = {x ≥ 0 : x(X) ≥ 1 for all X ∈ C}`. -/
def coveringPolyhedron (C : Finset (Finset V)) : Set (V → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ ∀ X ∈ C, (1 : ℝ) ≤ ∑ v ∈ X, x v}

/-- `C` is ideal: its covering polyhedron is integral (every vertex is an integer vector). -/
def IsIdeal (C : Finset (Finset V)) : Prop :=
  ∀ x ∈ Set.extremePoints ℝ (coveringPolyhedron C), ∀ v, ∃ z : ℤ, x v = z

/-- Existence of Király's functions `p : C → V`, `q : b(C) → V`. -/
def KiralyProperty (C : Finset (Finset V)) : Prop :=
  ∃ (p : C → V) (q : blocker C → V),
    (∀ X : C, p X ∈ X.1) ∧
    (∀ Y : blocker C, q Y ∈ Y.1) ∧
    ∀ (X : C) (Y : blocker C), p X = q Y → 1 < (X.1 ∩ Y.1).card

end Definitions

/-- Király's conjecture (MathDB 388087), literally: for every clutter on a finite ground set,
nonideal ⇔ the functions `p, q` exist. -/
def KiralyConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (C : Finset (Finset V)),
    IsClutter C → (¬ IsIdeal C ↔ KiralyProperty C)

/-! ## A kernel-checked case-split certificate -/

/-- Case tree: `node i c0 c1 c2` branches on the three possible values of `p` on edge `i`;
`leaf j` asserts that blocker member `j` has all of its elements "killed". -/
inductive CTree where
  | leaf (j : Nat)
  | node (i : Nat) (c0 c1 c2 : CTree)

/-- Under the partial assignment `a` (pairs `(edge, value)`), every entry `(v, is)` of `K[j]`
has some edge `i ∈ is` assigned the value `v`. -/
def deadB (K : List (List (Nat × List Nat))) (j : Nat) (a : List (Nat × Nat)) : Bool :=
  decide (j < K.length) && (K.getD j []).all (fun e => e.2.any (fun i => a.contains (i, e.1)))

def chk (D : List (List Nat)) (K : List (List (Nat × List Nat))) :
    CTree → List (Nat × Nat) → Bool
  | .leaf j, a => deadB K j a
  | .node i c0 c1 c2, a =>
    match D.getD i [] with
    | [d0, d1, d2] =>
      chk D K c0 ((i, d0) :: a) && chk D K c1 ((i, d1) :: a) && chk D K c2 ((i, d2) :: a)
    | _ => false

theorem chk_sound (D : List (List Nat)) (K : List (List (Nat × List Nat))) :
    ∀ (t : CTree) (a : List (Nat × Nat)), chk D K t a = true →
    ∀ b : Nat → Nat, (∀ e ∈ a, b e.1 = e.2) → (∀ i, D.getD i [] ≠ [] → b i ∈ D.getD i []) →
    ∃ j, j < K.length ∧ ∀ e ∈ K.getD j [], ∃ i ∈ e.2, b i = e.1 := by
  intro t
  induction t with
  | leaf j =>
    intro a h b ha _
    simp only [chk, deadB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.any_eq_true] at h
    obtain ⟨hj, hall⟩ := h
    refine ⟨j, hj, fun e he => ?_⟩
    obtain ⟨i, hi, hc⟩ := hall e he
    refine ⟨i, hi, ha (i, e.1) ?_⟩
    simpa using hc
  | node i c0 c1 c2 ih0 ih1 ih2 =>
    intro a h b ha hD
    simp only [chk] at h
    split at h
    · rename_i d0 d1 d2 hDi
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨h0, h1⟩, h2⟩ := h
      have hbi : b i ∈ [d0, d1, d2] := by
        rw [← hDi]; exact hD i (by rw [hDi]; simp)
      have ext : ∀ d, b i = d → ∀ e ∈ (i, d) :: a, b e.1 = e.2 := by
        intro d hd e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hd
        · exact ha e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbi
      rcases hbi with hb | hb | hb
      · exact ih0 _ h0 b (ext _ hb) hD
      · exact ih1 _ h1 b (ext _ hb) hD
      · exact ih2 _ h2 b (ext _ hb) hD
    · exact absurd h (by simp)
