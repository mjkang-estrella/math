import StackSortInj2Doubling
namespace StackSort
/-- The source's root insertion, before choosing the label subset. -/
def rootGlue (m : ℕ) (p : List ℕ × List ℕ) : List ℕ := p.1 ++ m :: p.2

theorem rootGlue_take (m : ℕ) (L R : List ℕ) (hL : ∀ x ∈ L, x < m) :
    (rootGlue m (L,R)).takeWhile (· != m) = L := by
  unfold rootGlue
  rw [List.takeWhile_append_of_pos (fun x hx => by simpa using ne_of_lt (hL x hx))]
  simp

theorem rootGlue_drop (m : ℕ) (L R : List ℕ) (hL : ∀ x ∈ L, x < m) :
    ((rootGlue m (L,R)).dropWhile (· != m)).drop 1 = R := by
  unfold rootGlue
  rw [List.dropWhile_append_of_pos (fun x hx => by simpa using ne_of_lt (hL x hx))]
  simp

theorem rootGlue_injective (m : ℕ) {L R L' R' : List ℕ}
    (hL : ∀ x ∈ L, x < m) (hL' : ∀ x ∈ L', x < m)
    (h : rootGlue m (L,R) = rootGlue m (L',R')) : L = L' ∧ R = R' := by
  constructor
  · have ht := congrArg (fun w : List ℕ => w.takeWhile (· != m)) h
    simpa only [rootGlue_take m L R hL, rootGlue_take m L' R' hL'] using ht
  · have ht := congrArg (fun w : List ℕ => (w.dropWhile (· != m)).drop 1) h
    simpa only [rootGlue_drop m L R hL, rootGlue_drop m L' R' hL'] using ht

/-- Forward validity of the injection, with arbitrary increasing relabellings. -/
theorem rootGlue_same_sort (m : ℕ) (φ ψ : ℕ ↪o ℕ)
    {L L' R R' : List ℕ} (hLL : s L = s L') (hRR : s R = s R')
    (hL : ∀ x ∈ L.map φ, x < m) (hL' : ∀ x ∈ L'.map φ, x < m)
    (hR : ∀ x ∈ R.map ψ, x ≤ m) (hR' : ∀ x ∈ R'.map ψ, x ≤ m) :
    s (rootGlue m (L.map φ, R.map ψ)) = s (rootGlue m (L'.map φ, R'.map ψ)) := by
  unfold rootGlue
  rw [s_split _ _ _ hL hR, s_split _ _ _ hL' hR',
    standardisation_proved φ L, standardisation_proved φ L',
    standardisation_proved ψ R, standardisation_proved ψ R', hLL, hRR]

/-- Recovery also recovers the standardized source words. -/
theorem rootGlue_map_injective (m : ℕ) (φ ψ : ℕ ↪o ℕ)
    {L L' R R' : List ℕ}
    (hL : ∀ x ∈ L.map φ, x < m) (hL' : ∀ x ∈ L'.map φ, x < m)
    (h : rootGlue m (L.map φ,R.map ψ) = rootGlue m (L'.map φ,R'.map ψ)) :
    L = L' ∧ R = R' := by
  obtain ⟨hl, hr⟩ := rootGlue_injective m hL hL' h
  exact ⟨(List.map_inj_right φ.injective).mp hl, (List.map_inj_right ψ.injective).mp hr⟩
end StackSort
