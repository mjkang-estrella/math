import AdmissibleCounting
namespace Nut8
variable {m : ℕ} [NeZero m]

omit [NeZero m] in
lemma diagonal_shift_neg (G : SimpleGraph (Fin 8 × ZMod m))
    (ht : TranslationInvariant G) (i : Fin 8) (b : ZMod m)
    (hb : G.Adj (i,0) (i,b)) : G.Adj (i,0) (i,-b) := by
  simpa using (ht i i b 0).mp (G.adj_symm hb)

lemma self_inverse_shift_val (b : ZMod m) (hb : b ≠ 0) (hi : -b = b) :
    b.val = m / 2 := by
  let : NeZero b := ⟨hb⟩
  have h := congrArg ZMod.val hi
  rw [ZMod.val_neg_of_ne_zero] at h
  have hlt := b.val_lt
  omega

/-- In a fiber with at most two shifts, the singleton is the shared semi-edge;
coherence makes the two-shift case an ordinary signed loop. -/
theorem signedQuotient_diagonal
    (G : SimpleGraph (Fin 8 × ZMod m)) [DecidableRel G.Adj]
    (ht : TranslationInvariant G) (hc : Cubic G)
    (ε : ℤ) (he : ε = 1 ∨ ε = -1) (u : (Fin 8 × ZMod m) → ℝ)
    (hu : adjacency G u = 0) (hf : ∀ v, u v ≠ 0)
    (hchar : ∀ i b, u (i,b) = (character m ε b : ℝ) * u (i,0))
    (hbound : ∀ i j, |signedQuotient m G ε i j| ≤ 2) (i : Fin 8) :
    signedQuotient m G ε i i = 0 ∨ signedQuotient m G ε i i = 2 ∨
    signedQuotient m G ε i i = -2 ∨ signedQuotient m G ε i i = ε ^ (m/2) := by
  classical
  have habs := abs_signedQuotient_eq_card G hc ε he u hu hf hchar i i
  have hle := hbound i i
  by_cases hzero : (orbitNeighbors G i i).card = 0
  · left
    rw [hzero, Nat.cast_zero] at habs
    exact abs_eq_zero.mp habs
  by_cases hone : (orbitNeighbors G i i).card = 1
  · obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hone
    have hadj : G.Adj (i,0) (i,b) := (mem_orbitNeighbors G i i b).mp (by rw [hb]; simp)
    have hne : b ≠ 0 := by intro h; subst b; exact G.loopless.irrefl _ hadj
    have hneg : -b = b := by
      have hh := (mem_orbitNeighbors G i i (-b)).mpr (diagonal_shift_neg G ht i b hadj)
      simpa [hb] using hh
    have hv := self_inverse_shift_val b hne hneg
    right; right; right
    have hs : signedQuotient m G ε i i = ∑ b ∈ orbitNeighbors G i i, character m ε b := by
      simp [signedQuotient, orbitNeighbors, Finset.sum_filter]
    rw [hs, hb, Finset.sum_singleton]
    exact congrArg (fun n => ε ^ n) hv
  · have htwo : (orbitNeighbors G i i).card = 2 := by omega
    rw [htwo] at habs
    rcases le_total 0 (signedQuotient m G ε i i) with hp | hn
    · right; left; rw [abs_of_nonneg hp] at habs; exact habs
    · right; right; left; rw [abs_of_nonpos hn] at habs; norm_num at habs; omega
end Nut8
