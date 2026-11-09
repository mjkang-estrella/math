import CrownVGraph

/-!
Component counting for crown induced graphs.

Upper bounds: a block function `f : V n → Fin k`, constant on crown edges inside
`s`, whose every fiber meeting `s` is path-connected inside `s`, bounds
`ccnt s ≤ k`.  Lower bounds: `k` pairwise path-disconnected vertices in `s`
force `k ≤ ccnt s`.
-/

namespace CrownV

variable {n : ℕ}

/-- Distinct components from vertices not path-connected in `s`. -/
theorem notSameC_comp_ne {s : Finset (V n)} {x y : V n} (hx : x ∈ s)
    (h : ¬ SameC s x y) : comp s x ≠ comp s y := by
  classical
  intro hEq
  apply h
  have h2 : x ∈ comp s x := comp_self hx
  rw [hEq] at h2
  exact SameC.symm (Finset.mem_filter.1 h2).2

/-- Lower bound: `k` pairwise path-disconnected vertices in `s`. -/
theorem ccnt_le_lower {s : Finset (V n)} {k : ℕ} (x : Fin k → V n)
    (hx : ∀ i, x i ∈ s) (hdiff : ∀ i j, i ≠ j → ¬ SameC s (x i) (x j)) :
    k ≤ ccnt s := by
  classical
  have hinj : Function.Injective fun i : Fin k => comp s (x i) := by
    intro i j hEq
    simp only at hEq
    by_contra hne
    exact absurd hEq (notSameC_comp_ne (hx i) (hdiff i j hne))
  have hsub : (Finset.univ.image fun i : Fin k => comp s (x i)) ⊆ comps s := by
    intro C hC
    obtain ⟨i, _, hEq⟩ := Finset.mem_image.1 hC
    rw [← hEq]; exact comp_mem_comps (hx i)
  have h1 : k = (Finset.univ.image fun i : Fin k => comp s (x i)).card := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  calc k = (Finset.univ.image fun i : Fin k => comp s (x i)).card := h1
    _ ≤ (comps s).card := Finset.card_le_card hsub

/-- Upper bound: blocks of `f` are edge-closed and connected inside `s`. -/
theorem ccnt_le {s : Finset (V n)} {k : ℕ} (f : V n → Fin k)
    (hedg : ∀ (x y : V n), x ∈ s → y ∈ s → cadj x y → f x = f y)
    (hconn : ∀ (x y : V n), x ∈ s → y ∈ s → f x = f y → SameC s x y) :
    ccnt s ≤ k := by
  classical
  set G : Fin k → Finset (V n) := fun i => s.filter fun y => f y = i with hGdef
  have hstep : ∀ (x y : V n), x ∈ s → y ∈ s → cadj x y → f y = f x := by
    intro x y hx hy hxy; exact (hedg x y hx hy hxy).symm
  have hfpres : ∀ x y, SameC s x y → y ∈ s → f y = f x := by
    intro x y h
    induction h with
    | refl => exact fun _ => rfl
    | tail h₁ hEd ih =>
      intro hyS
      exact (hstep _ _ hEd.1 hyS hEd.2.2).trans (ih hEd.1)
  have hcomp : ∀ x ∈ s, comp s x = G (f x) := by
    intro x hx
    ext y
    constructor
    · intro hy
      obtain ⟨hyS, hySame⟩ := Finset.mem_filter.1 hy
      exact Finset.mem_filter.2 ⟨hyS, hfpres x y hySame hyS⟩
    · intro hy
      obtain ⟨hyS, hyfx⟩ := Finset.mem_filter.1 hy
      have : SameC s x y := hconn x y hx hyS hyfx.symm
      exact Finset.mem_filter.2 ⟨hyS, this⟩
  have hsub : comps s ⊆ Finset.univ.image G := by
    intro C hC
    obtain ⟨x, hx, hEq⟩ := Finset.mem_image.1 hC
    rw [← hEq]
    exact Finset.mem_image.2 ⟨f x, Finset.mem_univ _, (hcomp x hx).symm⟩
  calc (comps s).card ≤ (Finset.univ.image G).card := Finset.card_le_card hsub
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = k := by simp

end CrownV
