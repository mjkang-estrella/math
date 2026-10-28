import Mathlib

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace KuTorus

abbrev Board (k : ℕ) := ZMod k × ZMod k

def AllowedDirection {k : ℕ} (v : Board k) : Prop :=
  (v.1 = -1 ∨ v.1 = 0 ∨ v.1 = 1) ∧
  (v.2 = -1 ∨ v.2 = 0 ∨ v.2 = 1) ∧ v ≠ (0, 0)

instance {k : ℕ} (v : Board k) : Decidable (AllowedDirection v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def line {k : ℕ} [NeZero k] (p v : Board k) : Finset (Board k) :=
  Finset.univ.image (fun t : ZMod k => (p.1 + t * v.1, p.2 + t * v.2))

def TwoFoldCover {k : ℕ} [NeZero k] (A : Finset (Board k)) : Prop :=
  ∀ p v, AllowedDirection v → 2 ≤ (A ∩ line p v).card

instance {k : ℕ} [NeZero k] (A : Finset (Board k)) : Decidable (TwoFoldCover A) :=
  inferInstanceAs (Decidable (∀ _p _v, _))

def witness : Finset (Board 6) :=
  {(0,0), (0,2), (0,3), (1,0), (1,3), (1,4), (2,0),
   (2,1), (3,1), (3,4), (4,2), (4,5), (5,0), (5,5)}

theorem witness_card : witness.card = 14 := by decide +kernel

theorem witness_cover : TwoFoldCover witness := by decide +kernel

-- Ku, arXiv:2606.12880v1, Conjecture 5.4.  The explicit k ≥ 6
-- restriction also respects the intended scope in the preceding paragraph.
def IntendedConjecture54 : Prop :=
  ∀ (k : ℕ) [NeZero k], 6 ≤ k → 3 ∣ k →
    ∀ A : Finset (Board k), A.card ≤ 2 * k + 2 → ¬ TwoFoldCover A

theorem intended_conjecture54_false : ¬ IntendedConjecture54 := by
  intro h
  exact h 6 (by norm_num) (by norm_num) witness (by rw [witness_card]) witness_cover

def SourceConjecture54 : Prop :=
  ∀ (k : ℕ) [NeZero k], 3 ∣ k →
    ∀ A : Finset (Board k), A.card ≤ 2 * k + 2 → ¬ TwoFoldCover A

theorem source_conjecture54_false : ¬ SourceConjecture54 := by
  intro h
  exact h 6 (by norm_num) witness (by rw [witness_card]) witness_cover

end KuTorus
