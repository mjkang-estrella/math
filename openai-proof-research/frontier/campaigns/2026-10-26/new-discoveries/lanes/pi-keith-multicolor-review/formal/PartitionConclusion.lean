import PartitionWitnesses

namespace KeithMulticolor

def witnessPartition (t : {t // t ∈ triples25}) : Nat.Partition 325 where
  parts := witnessParts t.val
  parts_pos := by
    intro a ha
    have hs := (witnessParts_certificate t.val t.property).2.2.1
    exact (Finset.mem_Icc.mp (hs (by simpa using ha))).1
  parts_sum := (witnessParts_certificate t.val t.property).2.1

theorem witnessPartition_isBox (t : {t // t ∈ triples25}) :
    IsSquareBox 25 (witnessPartition t) := by
  constructor
  · exact (witnessParts_certificate t.val t.property).1.le
  · intro a ha
    have hs := (witnessParts_certificate t.val t.property).2.2.1
    exact (Finset.mem_Icc.mp (hs (by simpa [witnessPartition] using ha))).2

theorem witnessPartition_distinct (t : {t // t ∈ triples25}) :
    distinctCount (witnessPartition t) = 23 :=
  (witnessParts_certificate t.val t.property).2.2.2.1

theorem witnessPartition_injective : Function.Injective witnessPartition := by
  intro a b h
  apply Subtype.ext
  have hh := congrArg (fun p : Nat.Partition 325 => decodeParts p.parts) h
  change decodeParts (witnessParts a.val) = decodeParts (witnessParts b.val) at hh
  rwa [(witnessParts_certificate a.val a.property).2.2.2.2,
    (witnessParts_certificate b.val b.property).2.2.2.2] at hh

def witnessPartitionSet : Finset (Nat.Partition 325) :=
  triples25.attach.image witnessPartition

theorem witnessPartitionSet_card : witnessPartitionSet.card = 2300 := by
  rw [witnessPartitionSet, Finset.card_image_of_injective _ witnessPartition_injective,
    Finset.card_attach, triples25_card]

theorem witnessPartitionSet_subset : witnessPartitionSet ⊆ squareBox 25 325 := by
  classical
  intro p hp
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hp
  simp [squareBox, witnessPartition_isBox]

theorem sourceArray_third_lower : 52900 ≤ sourceArray 25 325 22 1 := by
  classical
  let weight := fun p : Nat.Partition 325 =>
    (distinctCount p).choose 22 * (distinctCount p - 22).choose 1
  have hs : (∑ p ∈ witnessPartitionSet, weight p) = 52900 := by
    calc
      _ = ∑ _p ∈ witnessPartitionSet, 23 := by
        apply Finset.sum_congr rfl
        intro p hp
        obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hp
        dsimp [weight]
        rw [witnessPartition_distinct]
        norm_num [Nat.choose]
      _ = 52900 := by simp [witnessPartitionSet_card]
  have hle : (∑ p ∈ witnessPartitionSet, weight p) ≤
      ∑ p ∈ squareBox 25 325, weight p :=
    Finset.sum_le_sum_of_subset_of_nonneg witnessPartitionSet_subset (by
      intro p _ _
      exact Nat.zero_le _)
  rw [hs] at hle
  exact hle

/-- Consecutive lattice points on the full nonnegative-lattice line y=45-2x. -/
noncomputable def sourceCut : Fin 23 → ℕ :=
  fun x => sourceArray 25 325 x.val (45 - 2 * x.val)

theorem sourceCut_strict_valley :
    sourceCut 21 < sourceCut 20 ∧ sourceCut 21 < sourceCut 22 := by
  have h₀ := sourceArray_first
  have h₁ := sourceArray_middle
  have h₂ := sourceArray_third_lower
  change sourceArray 25 325 21 3 < sourceArray 25 325 20 5 ∧
    sourceArray 25 325 21 3 < sourceArray 25 325 22 1
  omega

/-- Literal box-partition count endpoint; no coefficient, counting, or
classification assumptions remain. -/
theorem source_not_unimodal : ¬ Unimodal sourceCut := by
  obtain ⟨h₀, h₂⟩ := sourceCut_strict_valley
  rintro ⟨peak, hleft, hright⟩
  by_cases hp : (21 : Fin 23) ≤ peak
  · have := hleft 20 21 (by decide) hp
    omega
  · have hp' : peak ≤ (21 : Fin 23) := le_of_not_ge hp
    have := hright 21 22 hp' (by decide)
    omega

end KeithMulticolor
