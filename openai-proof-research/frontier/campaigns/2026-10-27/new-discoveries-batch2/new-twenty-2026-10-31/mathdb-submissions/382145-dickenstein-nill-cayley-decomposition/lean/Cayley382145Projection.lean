import Cayley382145Cert

/-! # MathDB 382145: heavy-row selection and the standard-simplex projection data

From an optimal minimal-support certificate (`∑ y_i ℓ_i ≡ σ` on the generators) we select a
nonempty proper subset `J` of the support consisting of heavy rows (`y_j > σ/2`). Integer slacks
of these rows on every generator are `0` or `1` with at most one `1`; every row of `J` attains
`1` and some generator has all `J`-slacks `0`. The count gives `n - |J| ≤ 2(n+1-μ)`. -/

namespace Cayley382145

open Finset

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem zDot_sum (J : Finset ι) (a : ι → Fin n → ℤ) (v : Fin n → ℤ) :
    zDot (∑ j ∈ J, a j) v = ∑ j ∈ J, zDot (a j) v := by
  simp only [zDot, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

omit [Fintype ι] [DecidableEq ι] in
theorem castPt_sum (J : Finset ι) (a : ι → Fin n → ℤ) :
    castPt (∑ j ∈ J, a j) = ∑ j ∈ J, castPt (a j) := by
  funext k
  simp [castPt, Finset.sum_apply]

theorem projection_core (a : ι → Fin n → ℤ) (β : ι → ℤ) (V : Finset (Fin n → ℤ)) (y : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hy0 : ∀ i, 0 ≤ y i) (hy1 : ∑ i, y i = 1)
    (hya : ∑ i, y i • castPt (a i) = 0)
    (hind : ∀ z : ι → ℝ, (∀ i, y i = 0 → z i = 0) → ∑ i, z i • castPt (a i) = 0 →
      ∑ i, z i = 0 → z = 0)
    (hnn : ∀ i, ∀ v ∈ V, β i ≤ zDot (a i) v)
    (hsum : ∀ v ∈ V, ∑ i, y i * ((zDot (a i) v - β i : ℤ) : ℝ) = σ)
    (hfull : ∀ c : Fin n → ℤ, c ≠ 0 → ∀ d : ℤ, ∃ v ∈ V, zDot c v ≠ d)
    (hprim : ∀ i, a i ≠ 0) (hμ : ((n : ℝ) + 1) / 2 < σ⁻¹) :
    ∃ J : Finset ι, J.Nonempty ∧ ((n : ℝ) - J.card ≤ 2 * ((n : ℝ) + 1 - σ⁻¹)) ∧
      (∀ v ∈ V, ∀ j ∈ J, zDot (a j) v - β j = 0 ∨ zDot (a j) v - β j = 1) ∧
      (∀ v ∈ V, ∀ j ∈ J, ∀ j' ∈ J, zDot (a j) v - β j = 1 → zDot (a j') v - β j' = 1 → j = j') ∧
      (∃ v ∈ V, ∀ j ∈ J, zDot (a j) v - β j = 0) ∧
      (∀ j ∈ J, ∃ v ∈ V, zDot (a j) v - β j = 1) := by
  have hLnn : ∀ i, ∀ v ∈ V, (0 : ℝ) ≤ ((zDot (a i) v - β i : ℤ) : ℝ) := fun i v hv => by
    have := hnn i v hv
    exact_mod_cast (show (0 : ℤ) ≤ zDot (a i) v - β i by omega)
  have hpart : ∀ v ∈ V, ∀ T : Finset ι, ∑ i ∈ T, y i * ((zDot (a i) v - β i : ℤ) : ℝ) ≤ σ := by
    intro v hv T
    rw [← hsum v hv]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun i _ _ => mul_nonneg (hy0 i) (hLnn i v hv))
  have hcap : ∀ i, y i ≤ σ := by
    intro i
    obtain ⟨v, hv, hne⟩ := hfull (a i) (hprim i) (β i)
    have h1 : (1 : ℝ) ≤ ((zDot (a i) v - β i : ℤ) : ℝ) := by
      have := hnn i v hv
      exact_mod_cast (show (1 : ℤ) ≤ zDot (a i) v - β i by omega)
    have h2 := hpart v hv {i}
    rw [Finset.sum_singleton] at h2
    have h3 := mul_le_mul_of_nonneg_left h1 (hy0 i)
    linarith
  have hσn : σ * (((n : ℝ) + 1) / 2) < 1 := by
    have := mul_lt_mul_of_pos_left hμ hσ
    rwa [mul_inv_cancel₀ hσ.ne'] at this
  set S := univ.filter (fun i => y i ≠ 0) with hS
  set H := univ.filter (fun i => σ / 2 < y i) with hH
  have hmemS : ∀ i, i ∈ S ↔ y i ≠ 0 := fun i => by simp [hS]
  have hmemH : ∀ i, i ∈ H ↔ σ / 2 < y i := fun i => by simp [hH]
  have hsle : (S.card : ℝ) ≤ n + 1 := by exact_mod_cast card_support_le hind
  have hHS : H ⊆ S := fun i hi => (hmemS i).mpr (by
    have := (hmemH i).mp hi
    intro h
    rw [h] at this
    linarith)
  have hySum : ∑ i ∈ S, y i = 1 := by
    rw [hS, Finset.sum_filter_ne_zero]
    exact hy1
  have hsumH : ∑ i ∈ H, y i ≤ σ * H.card := by
    calc ∑ i ∈ H, y i ≤ ∑ _i ∈ H, σ := Finset.sum_le_sum fun i _ => hcap i
      _ = σ * H.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsumSH : ∑ i ∈ S \ H, y i ≤ σ / 2 * (S \ H).card := by
    calc ∑ i ∈ S \ H, y i ≤ ∑ _i ∈ S \ H, σ / 2 := Finset.sum_le_sum fun i hi => by
          have h := (Finset.mem_sdiff.mp hi).2
          rw [hmemH] at h
          exact le_of_not_gt h
      _ = σ / 2 * (S \ H).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcardSH : ((S \ H).card : ℝ) + H.card = S.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hHS
  have hbound : 2 ≤ σ * (S.card + H.card) := by
    have h := Finset.sum_sdiff hHS (f := y)
    rw [hySum] at h
    have e : ((S \ H).card : ℝ) = S.card - H.card := by linarith
    rw [e] at hsumSH
    nlinarith
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hySum
    exact zero_ne_one hySum
  obtain ⟨J, hJH, hJne, k, hkS, hkJ, hJbound⟩ : ∃ J : Finset ι, J ⊆ H ∧ J.Nonempty ∧
      ∃ k, k ∈ S ∧ k ∉ J ∧ ((n : ℝ) - J.card ≤ 2 * ((n : ℝ) + 1 - σ⁻¹)) := by
    by_cases hEq : H = S
    · obtain ⟨k, hk⟩ := hSne
      refine ⟨S.erase k, ?_, ?_, k, hk, fun h => (Finset.mem_erase.mp h).1 rfl, ?_⟩
      · rw [hEq]
        exact Finset.erase_subset k S
      · by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hsingle : ∀ i, i ≠ k → y i = 0 := by
          intro i hik
          by_contra hy
          have hmem : i ∈ S.erase k := Finset.mem_erase.mpr ⟨hik, (hmemS i).mpr hy⟩
          rw [hne] at hmem
          simp at hmem
        have h1 : ∑ i, y i = y k := Fintype.sum_eq_single k hsingle
        have h2 : ∑ i, y i • castPt (a i) = y k • castPt (a k) :=
          Fintype.sum_eq_single k (fun i hik => by rw [hsingle i hik, zero_smul])
        rw [hy1] at h1
        rw [hya, ← h1, one_smul] at h2
        apply hprim k
        funext j
        have hj := congrFun h2 j
        simp only [Pi.zero_apply, castPt] at hj
        show a k j = 0
        exact_mod_cast hj.symm
      · have hcardS : ((S.erase k).card : ℝ) + 1 = S.card := by
          exact_mod_cast Finset.card_erase_add_one hk
        have hμs : σ⁻¹ ≤ S.card := by
          have h1 : 1 ≤ σ * S.card := by
            calc (1 : ℝ) = ∑ i ∈ S, y i := hySum.symm
              _ ≤ ∑ _i ∈ S, σ := Finset.sum_le_sum fun i _ => hcap i
              _ = σ * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
          calc σ⁻¹ = σ⁻¹ * 1 := (mul_one _).symm
            _ ≤ σ⁻¹ * (σ * S.card) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hσ.le)
            _ = S.card := by rw [← mul_assoc, inv_mul_cancel₀ hσ.ne', one_mul]
        linarith
    · have hHne : H.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        rw [h, Finset.card_empty, Nat.cast_zero, add_zero] at hbound
        have : σ * S.card ≤ σ * (n + 1) := mul_le_mul_of_nonneg_left hsle hσ.le
        nlinarith
      obtain ⟨k, hkS, hkH⟩ : ∃ k, k ∈ S ∧ k ∉ H := by
        by_contra hno
        push Not at hno
        exact hEq (Finset.Subset.antisymm hHS (fun i hi => hno i hi))
      refine ⟨H, subset_refl _, hHne, k, hkS, hkH, ?_⟩
      have h2 : 2 * σ⁻¹ ≤ S.card + H.card := by
        calc 2 * σ⁻¹ = σ⁻¹ * 2 := mul_comm _ _
          _ ≤ σ⁻¹ * (σ * (S.card + H.card)) :=
              mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hσ.le)
          _ = S.card + H.card := by rw [← mul_assoc, inv_mul_cancel₀ hσ.ne', one_mul]
      linarith
  have hJheavy : ∀ j ∈ J, σ / 2 < y j := fun j hj => (hmemH j).mp (hJH hj)
  have hJS : ∀ j ∈ J, y j ≠ 0 := fun j hj => (hmemS j).mp (hHS (hJH hj))
  have hle1 : ∀ v ∈ V, ∀ j ∈ J, zDot (a j) v - β j ≤ 1 := by
    intro v hv j hj
    by_contra h
    push Not at h
    have h2 : (2 : ℝ) ≤ ((zDot (a j) v - β j : ℤ) : ℝ) := by
      exact_mod_cast (show (2 : ℤ) ≤ zDot (a j) v - β j by omega)
    have h3 := hpart v hv {j}
    rw [Finset.sum_singleton] at h3
    have h4 := mul_le_mul_of_nonneg_left h2 (hy0 j)
    have h5 := hJheavy j hj
    linarith
  have h01 : ∀ v ∈ V, ∀ j ∈ J, zDot (a j) v - β j = 0 ∨ zDot (a j) v - β j = 1 := by
    intro v hv j hj
    have h1 := hle1 v hv j hj
    have h2 := hnn j v hv
    omega
  have hone : ∀ v ∈ V, ∀ j ∈ J, ∀ j' ∈ J, zDot (a j) v - β j = 1 → zDot (a j') v - β j' = 1 →
      j = j' := by
    intro v hv j hj j' hj' h1 h1'
    by_contra hne
    have h3 := hpart v hv {j, j'}
    rw [Finset.sum_pair hne, h1, h1', Int.cast_one, mul_one, mul_one] at h3
    have h4 := hJheavy j hj
    have h5 := hJheavy j' hj'
    linarith
  have hhit : ∀ j ∈ J, ∃ v ∈ V, zDot (a j) v - β j = 1 := by
    intro j hj
    obtain ⟨v, hv, hne⟩ := hfull (a j) (hprim j) (β j)
    refine ⟨v, hv, ?_⟩
    rcases h01 v hv j hj with h | h
    · exact absurd (by omega) hne
    · exact h
  have hzero : ∃ v ∈ V, ∀ j ∈ J, zDot (a j) v - β j = 0 := by
    have hc : ∑ j ∈ J, a j ≠ 0 := by
      intro h
      apply sum_ne_zero_of_proper hind hy1 hya hJS hJne ((hmemS k).mp hkS) hkJ
      rw [← castPt_sum, h]
      funext x
      simp [castPt]
    obtain ⟨v, hv, hne⟩ := hfull _ hc (∑ j ∈ J, β j + 1)
    refine ⟨v, hv, fun j hj => ?_⟩
    by_contra hj0
    have hj1 : zDot (a j) v - β j = 1 := (h01 v hv j hj).resolve_left hj0
    have hsumJ : ∑ i ∈ J, (zDot (a i) v - β i) = 1 := by
      rw [Finset.sum_eq_single_of_mem j hj]
      · exact hj1
      · intro i hi hij
        rcases h01 v hv i hi with h | h
        · exact h
        · exact absurd (hone v hv i hi j hj h hj1) hij
    apply hne
    rw [zDot_sum]
    rw [Finset.sum_sub_distrib] at hsumJ
    omega
  exact ⟨J, hJne, hJbound, h01, hone, hzero, hhit⟩

end Cayley382145
