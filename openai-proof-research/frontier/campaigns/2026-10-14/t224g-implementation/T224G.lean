import Mathlib.Tactic

/-! Exact finite algebra only. No percolation geometry, probability process,
conditional-law convergence, or J1 theorem is formalized here. -/
namespace T224G
noncomputable section

def bit (b : Bool) : ℝ := if b then 1 else 0

def Sandwich (w u b : Bool) : Prop :=
  (w = true → u = true) ∧ (u = true → b = true)

def drift (w u b : Bool) : ℝ := (bit w + bit b) / 2 - bit u

def pivotal (w b : Bool) : ℝ := bit b - bit w

def mixedCoefficient (f : Bool → Bool → ℝ) : ℝ :=
  f true true - f true false - f false true + f false false

def birthDifference (f : Bool → Bool → ℝ) (w u b : Bool) : ℝ :=
  (f u w + f u b) / 2 - f u u

def deathDifference (f : Bool → Bool → ℝ) (w u b : Bool) : ℝ :=
  (f w u + f b u) / 2 - f u u

def refreshDifference (f : Bool → Bool → ℝ) (w b : Bool) : ℝ :=
  (f w w + f w b + f b w + f b b) / 4 - (f w w + f b b) / 2

theorem birth_identity (f : Bool → Bool → ℝ) (w u b : Bool)
    (h : Sandwich w u b) :
    birthDifference f w u b =
      (f false true - f false false + mixedCoefficient f / 2) * drift w u b
      - mixedCoefficient f * pivotal w b / 4 := by
  cases w <;> cases u <;> cases b <;>
    simp_all [Sandwich, birthDifference, mixedCoefficient, drift, pivotal, bit] <;> ring

theorem death_identity (f : Bool → Bool → ℝ) (w u b : Bool)
    (h : Sandwich w u b) :
    deathDifference f w u b =
      (f true false - f false false + mixedCoefficient f / 2) * drift w u b
      - mixedCoefficient f * pivotal w b / 4 := by
  cases w <;> cases u <;> cases b <;>
    simp_all [Sandwich, deathDifference, mixedCoefficient, drift, pivotal, bit] <;> ring

theorem refresh_identity (f : Bool → Bool → ℝ) (w b : Bool)
    (h : w = true → b = true) :
    refreshDifference f w b = - mixedCoefficient f * pivotal w b / 4 := by
  cases w <;> cases b <;>
    simp_all [refreshDifference, mixedCoefficient, pivotal, bit] <;> ring

theorem birth_minus_refresh (f : Bool → Bool → ℝ) (w u b : Bool)
    (h : Sandwich w u b) :
    birthDifference f w u b - refreshDifference f w b =
      (f false true - f false false + mixedCoefficient f / 2) * drift w u b := by
  rw [birth_identity f w u b h, refresh_identity f w b (fun hw => h.2 (h.1 hw))]
  ring

theorem death_minus_refresh (f : Bool → Bool → ℝ) (w u b : Bool)
    (h : Sandwich w u b) :
    deathDifference f w u b - refreshDifference f w b =
      (f true false - f false false + mixedCoefficient f / 2) * drift w u b := by
  rw [death_identity f w u b h, refresh_identity f w b (fun hw => h.2 (h.1 hw))]
  ring

theorem replica_product_decomposition (x y : ℝ) :
    x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by ring

theorem two_factor_telescoping (a b c d : ℝ) :
    a * b - c * d = (a - c) * b + c * (b - d) := by ring

theorem pair_kernel (w u b w' u' b' : Bool)
    (h : Sandwich w u b) (h' : Sandwich w' u' b') :
    ((bit w - bit u) * (bit w' - bit u') +
      (bit b - bit u) * (bit b' - bit u')) / 2 =
    pivotal w b * pivotal w' b' / 2 * (if u = u' then 1 else 0) := by
  cases w <;> cases u <;> cases b <;> cases w' <;> cases u' <;> cases b' <;>
    simp_all [Sandwich, pivotal, bit]

end
end T224G
