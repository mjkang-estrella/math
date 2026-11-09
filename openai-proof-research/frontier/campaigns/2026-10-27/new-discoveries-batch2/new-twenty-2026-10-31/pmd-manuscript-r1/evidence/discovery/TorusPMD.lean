import Mathlib.Basic.Real.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace TorusPMD
-- Vertices of the ordinary Cartesian product of two cycles.
abbrev V (m n : ℕ) := Fin m × Fin n
def cycleAdj {n : ℕ} (u v : Fin n) : Prop :=
  u ≠ v ∧ ((u.val + 1) % n = v.val ∨ (v.val + 1) % n = u.val)
def torus (m n : ℕ) (u v : V m n) : Prop :=
  (u.1 = v.1 ∧ cycleAdj u.2 v.2) ∨ (u.2 = v.2 ∧ cycleAdj u.1 v.1)
instance (m n : ℕ) (u v : V m n) : Decidable (torus m n u v) := by
  unfold torus cycleAdj; infer_instance
-- An edge coloring specifies an ordered partition; on the residual edges
-- (colors at least i), exactly the edges of color i have positive weight.
def Decomposition {α : Type} (G : α → α → Prop) (k : ℕ) : Prop :=
  ∃ c : α → α → Fin k, ∃ w : Fin k → α → ℝ,
    (∀ u v, c u v = c v u) ∧
    (∀ i, ∃ u v, G u v ∧ c u v = i) ∧
    (∀ u v z, G u v → G u z → c u v = c u z → v = z) ∧
    (∀ i u v, G u v → i.val ≤ (c u v).val →
      (0 < w i u + w i v ↔ c u v = i))
noncomputable def pmd {α : Type} (G : α → α → Prop) : ℕ :=
  sInf {k | Decomposition G k}
def idx (u : V 3 4) : Fin 12 := ⟨u.1.val * 4 + u.2.val, by omega⟩
def colors : Fin 12 → Fin 12 → Fin 5 := ![![0, 4, 0, 3, 2, 0, 0, 0, 1, 0, 0, 0], ![4, 0, 2, 0, 0, 1, 0, 0, 0, 3, 0, 0], ![0, 2, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0], ![3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2], ![2, 0, 0, 0, 0, 4, 0, 1, 3, 0, 0, 0], ![0, 1, 0, 0, 4, 0, 3, 0, 0, 0, 0, 0], ![0, 0, 4, 0, 0, 3, 0, 2, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 4], ![1, 0, 0, 0, 3, 0, 0, 0, 0, 4, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 3], ![0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 3, 0]]
def weights : Fin 5 → Fin 12 → ℤ := ![![-10, -10, -3, 2, -10, 8, -10, -1, 6, -7, 4, -5], ![-5, -3, 2, -1, -7, 4, -9, 8, 6, -12, 10, -12], ![-9, -3, 4, 8, 10, -12, -5, 6, -12, 2, -1, -7], ![-9, 8, -12, 10, -5, 4, -3, -12, 6, -7, 2, -1], ![10, -9, 8, -12, 6, -5, -7, 4, 2, -1, -12, -3]]
def c (u v : V 3 4) : Fin 5 := colors (idx u) (idx v)
def w (i : Fin 5) (u : V 3 4) : ℤ := weights i (idx u)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
 theorem certificate :
    (∀ u v, c u v = c v u) ∧
    (∀ i, ∃ u v, torus 3 4 u v ∧ c u v = i) ∧
    (∀ u v z, torus 3 4 u v → torus 3 4 u z → c u v = c u z → v = z) ∧
    (∀ i u v, torus 3 4 u v → i.val ≤ (c u v).val →
      (0 < w i u + w i v ↔ c u v = i)) := by decide
 theorem five_part_decomposition : Decomposition (torus 3 4) 5 := by
  refine ⟨c, fun i u => (w i u : ℝ), certificate.1,
    certificate.2.1, certificate.2.2.1, ?_⟩
  intro i u v hG hi
  have h := certificate.2.2.2 i u v hG hi
  constructor
  · intro hp
    apply h.mp
    dsimp only at hp ⊢
    norm_cast at hp ⊢
  · intro hc
    have hp := h.mpr hc
    dsimp only at hp ⊢
    norm_cast at hp ⊢
-- The infimum really is the minimum on every graph admitting a decomposition.
theorem pmd_minimum {α : Type} {G : α → α → Prop} {k : ℕ}
    (h : Decomposition G k) :
    Decomposition G (pmd G) ∧ ∀ j, Decomposition G j → pmd G ≤ j := by
  exact ⟨Nat.sInf_mem (s := {j | Decomposition G j}) ⟨k, h⟩, fun _ hj => Nat.sInf_le hj⟩
-- Each edge belongs to exactly one part of the coloring partition.
theorem parts_partition {α : Type} {G : α → α → Prop} {k : ℕ}
    (color : α → α → Fin k) (u v : α) :
    G u v ↔ ∃! i, G u v ∧ color u v = i := by
  constructor
  · intro h
    exact ⟨color u v, ⟨h, rfl⟩, fun _ hi => hi.2.symm⟩
  · rintro ⟨_, ⟨h, _⟩, _⟩
    exact h
-- Deleting earlier parts is exactly the residual-edge comparison used above.
theorem residual_partition {α : Type} {G : α → α → Prop} {k : ℕ}
    (color : α → α → Fin k) (i : Fin k) (u v : α) :
    (G u v ∧ ¬ ∃ j : Fin k, j.val < i.val ∧ G u v ∧ color u v = j) ↔
    (G u v ∧ i.val ≤ (color u v).val) := by
  constructor
  · rintro ⟨hG, hn⟩
    refine ⟨hG, ?_⟩
    by_contra h
    exact hn ⟨color u v, by omega, hG, rfl⟩
  · rintro ⟨hG, hi⟩
    refine ⟨hG, ?_⟩
    rintro ⟨j, hj, _, he⟩
    rw [← he] at hj
    omega
 theorem pmd_le_five : pmd (torus 3 4) ≤ 5 := by
  exact Nat.sInf_le five_part_decomposition
 theorem refutes_conjecture_4_7 :
    ¬ (∀ m n : ℕ, 3 ≤ m → 3 ≤ n →
       (Even (m+n) ∨ (m,n) = (3,4) ∨ (m,n) = (3,6) ∨ (m,n) = (5,6)) →
       pmd (torus m n) = 6) := by
  intro h
  have he := h 3 4 (by decide) (by decide) (Or.inr (Or.inl rfl))
  have hl := pmd_le_five
  omega
#print axioms certificate
#print axioms five_part_decomposition
#print axioms pmd_le_five
#print axioms refutes_conjecture_4_7
end TorusPMD
