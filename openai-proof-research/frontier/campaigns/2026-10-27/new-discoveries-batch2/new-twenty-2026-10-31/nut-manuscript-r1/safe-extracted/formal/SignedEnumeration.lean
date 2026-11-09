import Augmentation
import OrderedSwitch
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace Nut8

/-- Independent negative-sign slots: loops of weight two and off-tree edges.
A double edge occupies one slot, regardless of its weight. -/
def signSlots (U : QuotientMatrix) (p : Fin 8 → Fin 8) : Finset (Fin 8 × Fin 8) :=
  Finset.univ.filter fun q =>
    (q.1 = q.2 ∧ U q.1 q.2 = 2) ∨
    (q.1 < q.2 ∧ p q.2 ≠ q.1 ∧ U q.1 q.2 ≠ 0)

def signedRepresentative (U : QuotientMatrix) (s : ℤ)
    (D : Finset (Fin 8 × Fin 8)) : QuotientMatrix := fun i j =>
  if i = j ∧ U i j = 1 then s
  else if edgeKey i j ∈ D then - U i j else U i j

def signedPatterns (U : QuotientMatrix) (p : Fin 8 → Fin 8) : Finset QuotientMatrix :=
  ((signSlots U p).powerset ×ˢ ({1, -1} : Finset ℤ)).image
    (fun ds => signedRepresentative U ds.2 ds.1)

lemma edgeKey_self (i : Fin 8) : edgeKey i i = (i,i) := by simp [edgeKey]

lemma edgeKey_abs (C : QuotientMatrix) (h : ∀ i j, C i j = C j i) (i j : Fin 8) :
    C (edgeKey i j).1 (edgeKey i j).2 = C i j := by
  by_cases hij : i < j <;> simp [edgeKey, hij, h j i]

/-- Literal image membership for every positive ordered-tree structural matrix.
Only negative free slots are selected; all magnitude-one loops share s. -/
theorem signedPatterns_complete (C : QuotientMatrix) (s : ℤ)
    (h : Structural C s) (p : Fin 8 → Fin 8)
    (hp : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ 0 < C (p i) i) :
    C ∈ signedPatterns (unsignedQuotient C) p := by
  let D := (signSlots (unsignedQuotient C) p).filter fun q => C q.1 q.2 < 0
  apply Finset.mem_image.mpr
  refine ⟨(D,s), Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr
    (Finset.filter_subset _ _), ?_⟩, ?_⟩
  · rcases h.2.1 with hs | hs <;> simp [hs]
  · funext i j
    have hsym := h.2.2.1
    have hk := edgeKey_abs C hsym i j
    have hD : edgeKey i j ∈ D ↔
        edgeKey i j ∈ signSlots (unsignedQuotient C) p ∧ C i j < 0 := by
      simp only [D, Finset.mem_filter, hk]
    change (if i = j ∧ |C i j| = 1 then s else if edgeKey i j ∈ D then -|C i j| else |C i j|) = C i j
    by_cases hij : i = j
    · subst j
      rw [edgeKey_self]
      rcases structural_diagonal_cases C s h i with hz | hs | ht
      · simp [unsignedQuotient, hz.1, D, signSlots]
      · simp only [hs.2, and_self, ite_true]; exact hs.1.symm
      · have ha := ht.2
        have hmem : (i,i) ∈ signSlots (unsignedQuotient C) p := by
          simp [signSlots, unsignedQuotient, ha]
        have hmemD : (i,i) ∈ D ↔ C i i < 0 := by simp [D, hmem]
        rcases ht.1 with ht | ht <;> simp [unsignedQuotient, hmemD, ht]
    · have hn : ¬ (i = j ∧ |C i j| = 1) := by simp [hij]
      simp only [hn, ↓reduceIte, unsignedQuotient, hD]
      by_cases hc : C i j < 0
      · have hm : edgeKey i j ∈ signSlots (unsignedQuotient C) p := by
          have hne : C i j ≠ 0 := ne_of_lt hc
          have hab : (unsignedQuotient C) (edgeKey i j).1 (edgeKey i j).2 ≠ 0 := by
            simpa only [unsignedQuotient, hk, ne_eq, abs_eq_zero] using hne
          have ht : (edgeKey i j).1 < (edgeKey i j).2 := by
            by_cases hi : i < j
            · simpa [edgeKey, hi]
            · simpa [edgeKey, hi] using (lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm hij))
          have hpne : p (edgeKey i j).2 ≠ (edgeKey i j).1 := by
            intro he
            have hi0 : (edgeKey i j).2 ≠ 0 := by
              intro hz
              have hlt := ht
              rw [hz] at hlt
              exact (not_lt_of_ge (Fin.zero_le _)) hlt
            have hpos := (hp _ hi0).2
            rw [he, hk] at hpos
            omega
          simp only [signSlots, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inr ⟨ht, hpne, hab⟩
        simp [hm, hc, abs_of_neg hc]
      · simp [hc, abs_of_nonneg (le_of_not_gt hc)]
end Nut8
