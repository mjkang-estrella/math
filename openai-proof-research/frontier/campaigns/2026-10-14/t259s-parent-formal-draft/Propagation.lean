import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Set.Image
import Lean.Elab.Tactic.Omega

/-!
Provisional scoped support for T259S. No measure, cost or spectral-gap theorem.
The relation is an arbitrary equivalence relation, and all supplied row edges
are explicit hypotheses. Original code: MIT, Myeongjin Kang.
-/

namespace T259S

theorem interval_related {Y : Type*} (R : Setoid Y) (v : ℕ → Y)
    {i j : ℕ} (hij : i ≤ j)
    (hstep : ∀ m, i ≤ m → m < j → R.r (v m) (v (m + 1))) :
    R.r (v i) (v j) := by
  induction j, hij using Nat.le_induction with
  | base => exact R.refl _
  | succ j hij ih =>
    exact R.trans (ih (fun m hmi hmj => hstep m hmi (by omega)))
      (hstep j hij (by omega))

/-- A known endpoint relation and every row edge except one recover that edge.
`s i` and `t i` are the source and target of the i-th distinguished edge;
the intervening bridge from `t i` to `s (i+1)` is always supplied. -/
theorem recover_missing_edge {Y : Type*} (R : Setoid Y) (s t : ℕ → Y)
    (n k : ℕ) (hk : k ≤ n)
    (hbridge : ∀ i, i < n → R.r (t i) (s (i + 1)))
    (hedge : ∀ i, i ≤ n → i ≠ k → R.r (s i) (t i))
    (hwhole : R.r (s 0) (t n)) : R.r (s k) (t k) := by
  have hp : R.r (s 0) (s k) := interval_related R s (Nat.zero_le k) (by
    intro i _ hik
    exact R.trans (hedge i (by omega) (by omega)) (hbridge i (by omega)))
  have hs : R.r (t k) (t n) := interval_related R t hk (by
    intro i hki hin
    exact R.trans (hbridge i hin) (hedge (i + 1) (by omega) (by omega)))
  exact R.trans (R.symm hp) (R.trans hwhole (R.symm hs))

/-- Every point of each indicated fiber has its distinguished edge. -/
def Available {Y Z : Type*} (R : Setoid Y) (a : Y → Y) (π : Y → Z)
    (D : Set Z) : Prop := ∀ y, π y ∈ D → R.r y (a y)

/-- The one-exceptional-position mechanism, with its exact abstract interfaces.
Surjectivity of the exceptional row map and injectivity of the base shift are
separate hypotheses; neither is replaced by availability of a selected section. -/
theorem propagate_available {Y Z : Type*} (R : Setoid Y) (a : Y → Y)
    (π : Y → Z) (shift : Z → Z) (row : Y → ℕ → Y) (n k : ℕ)
    (hk : k ≤ n)
    (hbridge : ∀ y i, i < n → R.r (a (row y i)) (row y (i + 1)))
    (hwhole : ∀ y, R.r (row y 0) (a (row y n)))
    (hordinary : ∀ y i, i ≤ n → i ≠ k → π (row y i) = π y)
    (hexceptional : ∀ y, π (row y k) = shift (π y))
    (honto : Function.Surjective (fun y => row y k))
    (hinjective : Function.Injective shift)
    {D : Set Z} (hD : Available R a π D) :
    Available R a π (shift '' D) := by
  intro v hv
  obtain ⟨z, hz, hshift⟩ := hv
  obtain ⟨y, hy⟩ := honto v
  change row y k = v at hy
  have hbase : π y = z := hinjective (by
    rw [← hexceptional y, hy, hshift])
  have hmissing : R.r (row y k) (a (row y k)) :=
    recover_missing_edge R (row y) (fun i => a (row y i)) n k hk
      (hbridge y) (by
        intro i hi hik
        apply hD
        rw [hordinary y i hi hik, hbase]
        exact hz) (hwhole y)
  simpa only [hy] using hmissing

def layers {Z : Type*} (shift : Z → Z) (E : Set Z) : ℕ → Set Z
  | 0 => E
  | n + 1 => shift '' layers shift E n

/-- Pointwise one-sided marker coverage converts propagation into all edges. -/
theorem all_edges_of_coverage {Y Z : Type*} (R : Setoid Y) (a : Y → Y)
    (π : Y → Z) (shift : Z → Z) (E : Set Z)
    (hE : Available R a π E)
    (hprop : ∀ D, Available R a π D → Available R a π (shift '' D))
    (hcover : ∀ z, ∃ n, z ∈ layers shift E n) :
    ∀ y, R.r y (a y) := by
  have hav : ∀ n, Available R a π (layers shift E n) := by
    intro n
    induction n with
    | zero => exact hE
    | succ n ih => exact hprop _ ih
  intro y
  obtain ⟨n, hn⟩ := hcover (π y)
  exact hav n y hn

end T259S
