import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Basic

namespace MathDB356266

def Permutation (n : Nat) (p : Fin n → Fin n) : Prop := Function.Injective p

def Overlaps {n : Nat} (p q : Fin (n+1) → Fin (n+1)) : Prop :=
  ∀ a b : Fin n, (p a.succ < p b.succ ↔ q a.castSucc < q b.castSucc)

def next {N : Nat} (i : Fin (N+1)) : Fin (N+1) :=
  ⟨(i.val + 1) % (N+1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩

def EulerOrdering {n N : Nat} (t : Fin (N+1) → Fin (n+1) → Fin (n+1)) : Prop :=
  (∀ i, Permutation (n+1) (t i)) ∧ Function.Injective t ∧
  (∀ p, Permutation (n+1) p → ∃ i, t i = p) ∧
  (∀ i, Overlaps (t i) (t (next i)))

def position {N n : Nat} (i : Fin (N+1)) (a : Fin (n+1)) : Fin (N+1) :=
  ⟨(i.val + a.val) % (N+1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩

def Realizes {n N : Nat} {A : Type} [LT A]
    (t : Fin (N+1) → Fin (n+1) → Fin (n+1)) (w : Fin (N+1) → A) : Prop :=
  ∀ i a b, t i a < t i b ↔ w (position i a) < w (position i b)

def tour : Fin 24 → Fin 4 → Fin 4 :=
![![0, 1, 2, 3], ![1, 2, 3, 0], ![1, 3, 0, 2], ![3, 1, 2, 0], ![2, 3, 1, 0], ![2, 1, 0, 3], ![1, 0, 2, 3], ![0, 1, 3, 2], ![0, 3, 1, 2], ![3, 0, 1, 2], ![0, 2, 3, 1], ![2, 3, 0, 1], ![3, 0, 2, 1], ![0, 2, 1, 3], ![2, 0, 3, 1], ![0, 3, 2, 1], ![3, 2, 1, 0], ![3, 1, 0, 2], ![2, 1, 3, 0], ![1, 2, 0, 3], ![1, 0, 3, 2], ![1, 3, 2, 0], ![3, 2, 0, 1], ![2, 0, 1, 3]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem tour_euler : EulerOrdering tour := by
  unfold EulerOrdering Permutation Overlaps Function.Injective
  decide

theorem tour_not_realizable {A : Type} [LinearOrder A] (w : Fin 24 → A) :
    ¬ Realizes tour w := by
  intro h
  have h0 : w 2 < w 5 := (h 2 0 3).mp (by decide)
  have h1 : w 5 < w 8 := (h 5 0 3).mp (by decide)
  have h2 : w 8 < w 10 := (h 8 0 2).mp (by decide)
  have h3 : w 10 < w 13 := (h 10 0 3).mp (by decide)
  have h4 : w 13 < w 15 := (h 13 0 2).mp (by decide)
  have h5 : w 15 < w 18 := (h 15 0 3).mp (by decide)
  have h6 : w 18 < w 20 := (h 18 0 2).mp (by decide)
  have h7 : w 20 < w 23 := (h 20 0 3).mp (by decide)
  have h8 : w 23 < w 2 := (h 23 0 3).mp (by decide)
  exact (lt_irrefl (w 2)) (lt_trans (lt_trans (lt_trans (lt_trans (lt_trans (lt_trans (lt_trans (lt_trans (h0) h1) h2) h3) h4) h5) h6) h7) h8)

/-- Literal counterexample: the edges form an Euler ordering of the clustered
    overlap graph, but no cyclic word realizes their order types. -/
theorem counterexample : ∃ t : Fin 24 → Fin 4 → Fin 4,
    EulerOrdering t ∧ ∀ (A : Type) [LinearOrder A] (w : Fin 24 → A), ¬ Realizes t w :=
  ⟨tour, tour_euler, fun _ _ w => tour_not_realizable w⟩

#print axioms tour_euler
#print axioms tour_not_realizable
#print axioms counterexample
end MathDB356266
