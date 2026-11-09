module
public import GridSymmetry
@[expose] public section

namespace Grid343536

/-- Exact unsolved main theorem, including the path and ladder regimes. -/
def MainOrbit : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ∀ r : Setoid (Fin m × Fin n),
    IsEquitable (G m n) r → r = orbitSetoid (G m n) (Hpi r)

/-- Exact unsolved full-automorphism stabilizer classification. -/
def FreeClassification : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
    (HasFreeVertex (G m n) ↔ ¬ (2 ≤ m ∧ m = n ∧ n ≤ 3))

/-- Exact unsolved finite exceptional obstruction, for the abstract reading too. -/
def ExceptionalNoIso : Prop :=
  ∀ k : ℕ, 2 ≤ k → k ≤ 3 →
    ¬ Nonempty (EqPart (G k k) ≃o Subgroup (G k k ≃g G k k))

def NaturalLatticeIso (m n : ℕ) : Prop :=
  ∃ e : Subgroup (G m n ≃g G m n) ≃o EqPart (G m n),
    ∀ H, e H = orbitMap (G m n) H

theorem orbit_surjective (main : MainOrbit) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Function.Surjective (orbitMap (G m n)) := by
  intro r
  refine ⟨Hpi r.val, ?_⟩
  apply Subtype.ext
  exact (main m n hm hn r.val r.property).symm

theorem natural_iso_of_free (main : MainOrbit) (m n : ℕ)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hf : HasFreeVertex (G m n)) :
    NaturalLatticeIso m n :=
  ⟨naturalIso (G m n) hf (orbit_surjective main m n hm hn), fun _ => rfl⟩

/-- Conditional literal conjunction; the three remaining Props are explicit premises. -/
theorem mathdb_343536 (main : MainOrbit) (free : FreeClassification)
    (exceptional : ExceptionalNoIso) :
    ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (∀ r : Setoid (Fin m × Fin n),
        IsEquitable (G m n) r ↔
          ∃ H : Subgroup (G m n ≃g G m n), r = orbitSetoid (G m n) H) ∧
      (Nonempty (EqPart (G m n) ≃o Subgroup (G m n ≃g G m n)) ↔
        HasFreeVertex (G m n)) ∧
      (HasFreeVertex (G m n) ↔ ¬ (2 ≤ m ∧ m = n ∧ n ≤ 3)) := by
  intro m n hm hn
  refine ⟨?_, ?_, free m n hm hn⟩
  · intro r
    constructor
    · intro hr
      exact ⟨Hpi r, main m n hm hn r hr⟩
    · rintro ⟨H, rfl⟩
      exact orbit_equitable _ _
  · constructor
    · intro hi
      apply (free m n hm hn).mpr
      rintro ⟨h2, rfl, h3⟩
      exact exceptional m h2 h3 hi
    · intro hf
      exact ⟨(naturalIso _ hf (orbit_surjective main m n hm hn)).symm⟩

theorem natural_iso_iff (main : MainOrbit) (free : FreeClassification)
    (exceptional : ExceptionalNoIso) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    NaturalLatticeIso m n ↔ HasFreeVertex (G m n) := by
  constructor
  · rintro ⟨e, _⟩
    exact ((mathdb_343536 main free exceptional m n hm hn).2.1).mp ⟨e.symm⟩
  · exact natural_iso_of_free main m n hm hn
end Grid343536
