import FiniteBridge
set_option autoImplicit false
namespace Polyomino57.Diagonal.FiniteProof.Packed
/-- Little endian radix-64 digit. No boundedness premise is needed. -/
def digit (a i : ℕ) : ℕ :=
  Nat.rec (fun a => a % 64) (fun _ ih a => ih (a / 64)) i a
/-- Checks all coordinates using small, literal packed rows. -/
def mergeCheck (n a b c : ℕ) : Bool :=
  Nat.rec (fun _ _ _ => true) (fun _ ih a b c =>
    decide (c % 64 + 1 ≤ a % 64 + b % 64) &&
      ih (a / 64) (b / 64) (c / 64)) n a b c
theorem mergeCheck_sound {n a b c : ℕ} (h : mergeCheck n a b c = true) :
    ∀ i < n, digit c i + 1 ≤ digit a i + digit b i := by
  induction n generalizing a b c with
  | zero => intro i hi; omega
  | succ n ih =>
    simp only [mergeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    intro i hi
    cases i with
    | zero => exact h.1
    | succ i => exact ih h.2 i (by omega)
/-- A table with rows indexed by actual finite label sets avoids a mask bridge. -/
theorem certificate {V I : Type*} [DecidableEq V] [DecidableEq I]
    (n : ℕ) (idx : V → ℕ) (D : Finset V) (M : Finset I)
    (E : V → V → Prop) (H : I → V → Prop) (row : Finset I → ℕ)
    (hi : ∀ v ∈ D, idx v < n)
    (hb : ∀ A, A ⊆ M → A.Nonempty → ∀ v ∈ D,
      (∀ i ∈ A, H i v) → digit (row A) (idx v) ≤ 1)
    (he : ∀ A, A ⊆ M → A.Nonempty → ∀ v ∈ D, ∀ w ∈ D,
      E v w → digit (row A) (idx v) ≤ digit (row A) (idx w) + 1)
    (hm : ∀ A B, A ⊆ M → B ⊆ M → A.Nonempty → B.Nonempty → Disjoint A B →
      mergeCheck n (row A) (row B) (row (A ∪ B)) = true) :
    GraphPotential.Certificate E D M H (fun A v => digit (row A) (idx v)) := by
  constructor
  · exact fun A hA hne => hb A hA hne
  · exact fun A hA hne => he A hA hne
  · intro A B hA hB hneA hneB hd v hv
    exact mergeCheck_sound (hm A B hA hB hneA hneB hd) (idx v) (hi v hv)
end Polyomino57.Diagonal.FiniteProof.Packed
