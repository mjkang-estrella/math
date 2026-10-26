import UniversalBound

open scoped BigOperators

namespace MaxIndex

abbrev WitnessIndex (m : ℕ) := Option (Fin m ⊕ Bool)

noncomputable def witnessRadius (m : ℕ) : ℝ := 2 * m
noncomputable def witnessDenominator (m : ℕ) : ℝ := witnessRadius m ^ 2 + m

noncomputable def witnessProbability (m : ℕ) : WitnessIndex m → ℝ
  | none => witnessRadius m ^ 2 / witnessDenominator m
  | some (.inl _) => 1 / witnessDenominator m
  | some (.inr _) => 0

theorem witnessDenominator_pos (m : ℕ) (hm : 2 ≤ m) :
    0 < witnessDenominator m := by
  dsimp [witnessDenominator, witnessRadius]
  positivity

theorem witnessProbability_nonneg (m : ℕ) (hm : 2 ≤ m) (i : WitnessIndex m) :
    0 ≤ witnessProbability m i := by
  cases i with
  | none => exact div_nonneg (sq_nonneg _) (witnessDenominator_pos m hm).le
  | some i => cases i <;> simp [witnessProbability, (witnessDenominator_pos m hm).le]

theorem witnessProbability_sum (m : ℕ) (hm : 2 ≤ m) :
    ∑ i, witnessProbability m i = 1 := by
  rw [Fintype.sum_option]
  simp only [Fintype.sum_sum_type, witnessProbability, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fin, Fintype.card_bool, mul_zero, add_zero]
  have hd := (witnessDenominator_pos m hm).ne'
  dsimp [witnessDenominator] at *
  field_simp

def starMask (m : ℕ) : Finset (WitnessIndex m × WitnessIndex m) :=
  (Finset.univ.image (fun i : Fin m => (none, some (Sum.inl i)))) ∪
  (Finset.univ.image (fun i : Fin m => (some (Sum.inl i), none)))

theorem starMask_disjoint (m : ℕ) :
    Disjoint (Finset.univ.image (fun i : Fin m => ((none : WitnessIndex m), some (Sum.inl i))))
      (Finset.univ.image (fun i : Fin m => (some (Sum.inl i), (none : WitnessIndex m)))) := by
  simp [Finset.disjoint_left]

theorem starMask_card (m : ℕ) : (starMask m).card = 2 * m := by
  rw [starMask, Finset.card_union_of_disjoint (starMask_disjoint m)]
  rw [Finset.card_image_of_injective _ (by intro a b h; simpa using h),
    Finset.card_image_of_injective _ (by intro a b h; simpa using h)]
  simp
  omega

def arithmeticWitnessMask (m : ℕ) : Finset (WitnessIndex m × WitnessIndex m) :=
  insert (none, none) (insert (none, some (.inr false)) (starMask m))

def geometricWitnessMask (m : ℕ) (hm : 2 ≤ m) :
    Finset (WitnessIndex m × WitnessIndex m) :=
  let j : Fin m := ⟨0, by omega⟩
  insert (none, none) (insert (some (.inl j), some (.inl j)) (starMask m))

theorem arithmeticWitnessMask_card (m : ℕ) : (arithmeticWitnessMask m).card = 2 * m + 2 := by
  have hnone : (none, none) ∉
      insert (none, some (.inr false)) (starMask m) := by simp [starMask]
  have hzero : (none, some (.inr false)) ∉ starMask m := by simp [starMask]
  rw [arithmeticWitnessMask, Finset.card_insert_of_notMem hnone,
    Finset.card_insert_of_notMem hzero, starMask_card]

theorem geometricWitnessMask_card (m : ℕ) (hm : 2 ≤ m) :
    (geometricWitnessMask m hm).card = 2 * m + 2 := by
  let j : Fin m := ⟨0, by omega⟩
  have hnone : (none, none) ∉
      insert (some (.inl j), some (.inl j)) (starMask m) := by simp [starMask]
  have hleaf : (some (.inl j), some (.inl j)) ∉ starMask m := by simp [starMask]
  change (insert (none, none) (insert (some (.inl j), some (.inl j)) (starMask m))).card = _
  rw [Finset.card_insert_of_notMem hnone, Finset.card_insert_of_notMem hleaf, starMask_card]

theorem sum_starMask (m : ℕ) (f : WitnessIndex m × WitnessIndex m → ℝ) :
    (∑ e ∈ starMask m, f e) =
      (∑ i : Fin m, f (none, some (.inl i))) +
      (∑ i : Fin m, f (some (.inl i), none)) := by
  rw [starMask, Finset.sum_union (starMask_disjoint m)]
  congr 1 <;> apply Finset.sum_image <;> intro a _ b _ h <;> simpa using h

theorem witness_geometric_star (m : ℕ) (hm : 2 ≤ m) (i : Fin m) :
    geometricEntry (witnessProbability m) (none, some (.inl i)) =
      witnessRadius m / witnessDenominator m := by
  have hd := witnessDenominator_pos m hm
  have hr : 0 ≤ witnessRadius m := by dsimp [witnessRadius]; positivity
  change Real.sqrt ((witnessRadius m ^ 2 / witnessDenominator m) *
    (1 / witnessDenominator m)) = _
  have he : (witnessRadius m ^ 2 / witnessDenominator m) * (1 / witnessDenominator m) =
      (witnessRadius m / witnessDenominator m) ^ 2 := by ring
  rw [he, Real.sqrt_sq (div_nonneg hr hd.le)]

theorem witness_arithmetic_selected_sum (m : ℕ) :
    (∑ e ∈ arithmeticWitnessMask m, arithmeticEntry (witnessProbability m) e) =
      ((m + 3 / 2) * witnessRadius m ^ 2 + m) / witnessDenominator m := by
  have hnone : (none, none) ∉
      insert (none, some (.inr false)) (starMask m) := by simp [starMask]
  have hzero : (none, some (.inr false)) ∉ starMask m := by simp [starMask]
  rw [arithmeticWitnessMask, Finset.sum_insert hnone, Finset.sum_insert hzero,
    sum_starMask]
  simp only [arithmeticEntry, witnessProbability, add_zero, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  ring

theorem witness_geometric_selected_sum (m : ℕ) (hm : 2 ≤ m) :
    (∑ e ∈ geometricWitnessMask m hm, geometricEntry (witnessProbability m) e) =
      (witnessRadius m ^ 2 + 2 * m * witnessRadius m + 1) / witnessDenominator m := by
  let j : Fin m := ⟨0, by omega⟩
  have hnone : (none, none) ∉
      insert (some (.inl j), some (.inl j)) (starMask m) := by simp [starMask]
  have hleaf : (some (.inl j), some (.inl j)) ∉ starMask m := by simp [starMask]
  change (∑ e ∈ insert (none, none) (insert (some (.inl j), some (.inl j))
    (starMask m)), geometricEntry (witnessProbability m) e) = _
  rw [Finset.sum_insert hnone, Finset.sum_insert hleaf, sum_starMask,
    geometricEntry_diagonal _ (witnessProbability_nonneg m hm),
    geometricEntry_diagonal _ (witnessProbability_nonneg m hm)]
  have hsymm : ∀ i : Fin m,
      geometricEntry (witnessProbability m) (some (.inl i), none) =
        witnessRadius m / witnessDenominator m := by
    intro i
    simpa only [geometricEntry, mul_comm] using witness_geometric_star m hm i
  simp_rw [witness_geometric_star m hm, hsymm]
  simp only [witnessProbability, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin]
  ring

theorem witness_next_index_fails (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) + 3 < maskTopSum (arithmeticEntry (witnessProbability m)) (2 * m + 2) +
      maskTopSum (geometricEntry (witnessProbability m)) (2 * m + 2) := by
  have ha := selected_sum_le_maskTopSum (arithmeticEntry (witnessProbability m))
    (2 * m + 2) (arithmeticWitnessMask m) (arithmeticWitnessMask_card m).le
  have hg := selected_sum_le_maskTopSum (geometricEntry (witnessProbability m))
    (2 * m + 2) (geometricWitnessMask m hm) (geometricWitnessMask_card m hm).le
  rw [witness_arithmetic_selected_sum] at ha
  rw [witness_geometric_selected_sum] at hg
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have he := sharpness_selected_sum (m : ℝ) hmreal
  have hpos := sharpness_gap_positive (m : ℝ) hmreal
  dsimp [witnessRadius, witnessDenominator] at ha hg
  linarith

end MaxIndex
