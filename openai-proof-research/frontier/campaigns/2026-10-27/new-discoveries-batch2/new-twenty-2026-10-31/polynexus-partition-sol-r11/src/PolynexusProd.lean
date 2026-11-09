import Mathlib.Data.Matrix.Mul
import PolynexusSrc

open Classical

/-!
# Ordinary products of coupled diagonal blocks (MathDB 352496)

The actual finite matrix product of two legal blocks `B(a,b,e)` and
`B(c,q,f)` has, for fixed row `r` and column `h`, at most one nonzero
summand: the middle index of a row is unique.  Hence the entry is `1`
exactly under the coupled witness `PMulWit` (a common middle index
`b+u = c+v`) and `0` otherwise.  Ordinary addition and multiplication of
natural entries only; no rectangle, distinct-output or multiset reading.
-/

/-- Coupled product witness for the entry at row `r`, column `h`: middle
index `j = b+u = c+v` with `u <= e`, `v <= f`, row `r = a+u`, output `h = q+v`. -/
def PMulWit (a b e c q f r h : ℕ) : Prop :=
  ∃ u v, u ≤ e ∧ v ≤ f ∧ r = a + u ∧ b + u = c + v ∧ h = q + v

/-- Two coupled entries of one block in the same row have equal columns:
the middle index is a function of the row alone. -/
theorem PCnd_row_col_unique {a b e j₁ j₂ r : ℕ}
    (h₁ : PCnd a b e r j₁) (h₂ : PCnd a b e r j₂) : j₁ = j₂ := by
  obtain ⟨t₁, _, hr₁, hj₁⟩ := PCnd_iff_t.1 h₁
  obtain ⟨t₂, _, hr₂, hj₂⟩ := PCnd_iff_t.1 h₂
  omega

/-- A product summand whose two entries are both coupled ones equals `1`. -/
theorem PBlk_mul_summand_one {n a b e c q f : ℕ} {r j k : Fin n}
    (h₁ : PCnd a b e (↑r) (↑j)) (h₂ : PCnd c q f (↑j) (↑k)) :
    PBlk n a b e r j * PBlk n c q f j k = 1 := by
  rw [PBlk_eq_one h₁, PBlk_eq_one h₂]

/-- A product summand with a vanishing factor equals `0`. -/
theorem PBlk_mul_summand_zero {n a b e c q f : ℕ} {r j k : Fin n}
    (h : ¬ (PCnd a b e (↑r) (↑j) ∧ PCnd c q f (↑j) (↑k))) :
    PBlk n a b e r j * PBlk n c q f j k = 0 := by
  have hor : ¬ PCnd a b e (↑r) (↑j) ∨ ¬ PCnd c q f (↑j) (↑k) := by
    by_cases h1 : PCnd a b e (↑r) (↑j)
    · exact Or.inr (fun h2 => h ⟨h1, h2⟩)
    · exact Or.inl h1
  rcases hor with h1 | h2
  · rw [PBlk_eq_zero h1, zero_mul]
  · rw [PBlk_eq_zero h2, mul_zero]

/-- The exact ordinary matrix product entry: the finite sum over middle
indices equals `1` under the coupled witness and `0` otherwise.  At most
one summand is nonzero, so no multiplicity or cancellation occurs. -/
theorem PBlk_mul_entry (n a b e c q f : ℕ)
    (hleg : a + e + 1 ≤ n ∧ b + e + 1 ≤ n ∧ c + f + 1 ≤ n ∧ q + f + 1 ≤ n)
    (r k : Fin n) :
    (PBlk n a b e * PBlk n c q f) r k
      = if PMulWit a b e c q f (↑r) (↑k) then 1 else 0 := by
  rw [Matrix.mul_apply]
  by_cases hw : PMulWit a b e c q f (↑r) (↑k)
  · obtain ⟨u, v, hue, hvf, hr, hjc, hk⟩ := id hw
    have hbn : b + u < n := by have h2 := hleg.2.1; omega
    have hc1 : PCnd a b e (↑r) ((⟨b + u, hbn⟩ : Fin n) : ℕ) :=
      PCnd_iff_t.2 ⟨u, hue, hr.symm, rfl⟩
    have hc2 : PCnd c q f ((⟨b + u, hbn⟩ : Fin n) : ℕ) (↑k) :=
      PCnd_iff_t.2 ⟨v, hvf, hjc.symm, hk.symm⟩
    refine (Finset.sum_eq_single (⟨b + u, hbn⟩ : Fin n) ?_ ?_).trans ?_
    · intro j _ hne
      refine PBlk_mul_summand_zero ?_
      rintro ⟨hc1', hc2'⟩
      exact hne (Fin.ext (PCnd_row_col_unique hc1' hc1))
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
    · rw [PBlk_mul_summand_one hc1 hc2, ite_eq_left hw]
  · refine (Finset.sum_eq_zero ?_).trans ?_
    · intro j _
      refine PBlk_mul_summand_zero ?_
      rintro ⟨hc1, hc2⟩
      obtain ⟨t₁, ht₁, hr₁, hj₁⟩ := PCnd_iff_t.1 hc1
      obtain ⟨t₂, ht₂, hr₂, hj₂⟩ := PCnd_iff_t.1 hc2
      exact hw ⟨t₁, t₂, ht₁, ht₂, hr₁.symm, by omega, hj₂.symm⟩
    · rw [ite_eq_right hw]

/-- A coupled product witness forces the middle intervals to overlap:
`b <= c+f` and `c <= b+e`. -/
theorem PMulWit_overlap {a b e c q f r h : ℕ}
    (w : PMulWit a b e c q f r h) : b ≤ c + f ∧ c ≤ b + e := by
  obtain ⟨u, v, hue, hvf, hr, hj, hk⟩ := w
  exact ⟨by omega, by omega⟩
