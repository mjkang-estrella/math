import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MathDB364205
abbrev Cube (n : ℕ) := Fin n → Bool
/-- Literal Hamming distance: number of coordinates on which two vertices differ. -/
def dist {n : ℕ} (x y : Cube n) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card
/-- A subset has diameter exactly r and is inclusion-maximal subject to diameter at most r. -/
def MaximalDiameter {n : ℕ} (A : Finset (Cube n)) (r : ℕ) : Prop :=
  (∀ x ∈ A, ∀ y ∈ A, dist x y ≤ r) ∧
  (∃ x ∈ A, ∃ y ∈ A, dist x y = r) ∧
  (∀ x, x ∉ A → ∃ y ∈ A, r < dist x y)
/-- Every point attains the diameter, as in Section 2 of the source. -/
def Rigid {n : ℕ} (A : Finset (Cube n)) (r : ℕ) : Prop :=
  ∀ x ∈ A, ∃ y ∈ A, dist x y = r

def vertex (k : ℕ) : Cube 8 := fun i => (k / 2 ^ i.val) % 2 == 1

def A : Finset (Cube 8) :=
  ([0, 3, 5, 8, 10, 11, 12, 15, 18, 23, 26, 30, 66, 68, 71, 74, 78, 79,
    130, 131, 132, 135, 137, 138, 140, 142, 143, 150, 158, 194, 198, 203, 206, 217].map vertex).toFinset

theorem card_A : A.card = 34 := by decide

theorem pair_bound : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 5 := by decide

theorem rigid_A : Rigid A 5 := by
  change ∀ x ∈ A, ∃ y ∈ A, dist x y = 5
  decide

theorem outside_A : ∀ x : Cube 8, x ∉ A → ∃ y ∈ A, 5 < dist x y := by decide

theorem diameter_attained : ∃ x ∈ A, ∃ y ∈ A, dist x y = 5 := by decide

theorem maximal_A : MaximalDiameter A 5 :=
  ⟨pair_bound, diameter_attained, outside_A⟩

/-- The exact extremal claim, expressed without a chosen maximum operator. -/
def SourceClaim : Prop := ∀ n r : ℕ, r ≤ n →
  IsGreatest {s : ℕ | ∃ S : Finset (Cube n), MaximalDiameter S r ∧ Rigid S r ∧ S.card = s} (2 ^ r)

theorem source_refutation : ¬ SourceClaim := by
  intro h
  have hgreat := h 8 5 (by decide)
  have hm : 34 ∈ {s : ℕ | ∃ S : Finset (Cube 8), MaximalDiameter S 5 ∧ Rigid S 5 ∧ S.card = s} :=
    ⟨A, maximal_A, rigid_A, card_A⟩
  have := hgreat.2 hm
  norm_num at this
end MathDB364205
#print axioms MathDB364205.source_refutation
