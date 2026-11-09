import PartitionTopCounts

namespace KeithMulticolor

/-- Literal uncolored box partitions: positive parts, prescribed sum, at most
N parts and no part larger than N. -/
def IsSquareBox {n : ℕ} (N : ℕ) (p : Nat.Partition n) : Prop :=
  p.parts.card ≤ N ∧ ∀ a ∈ p.parts, a ≤ N

def distinctCount {n : ℕ} (p : Nat.Partition n) : ℕ := p.parts.toFinset.card

noncomputable def squareBox (N n : ℕ) : Finset (Nat.Partition n) := by
  classical
  exact Finset.univ.filter (IsSquareBox N)

/-- Choose disjoint sets of i and j distinct sizes for the first two colors;
the remaining sizes have the third color, whose variable is set to one. -/
noncomputable def sourceArray (N n i j : ℕ) : ℕ :=
  ∑ p ∈ squareBox N n,
    (distinctCount p).choose i * (distinctCount p - i).choose j

theorem distinctCount_le {N n : ℕ} {p : Nat.Partition n}
    (hp : IsSquareBox N p) : distinctCount p ≤ N :=
  p.parts.toFinset_card_le.trans hp.1

theorem support_subset {N n : ℕ} {p : Nat.Partition n}
    (hp : IsSquareBox N p) : p.parts.toFinset ⊆ Finset.Icc 1 N := by
  intro a ha
  have hm : a ∈ p.parts := by simpa using ha
  exact Finset.mem_Icc.mpr ⟨p.parts_pos hm, hp.2 a hm⟩

def staircase25 : Nat.Partition 325 where
  parts := (Finset.Icc 1 25).val
  parts_pos := by
    intro a ha
    change a ∈ Finset.Icc 1 25 at ha
    have := (Finset.mem_Icc.mp ha).1
    omega
  parts_sum := by decide +kernel

theorem staircase25_isBox : IsSquareBox 25 staircase25 := by
  constructor
  · decide +kernel
  · intro a ha
    exact (Finset.mem_Icc.mp ha).2

theorem staircase25_distinct : distinctCount staircase25 = 25 := by
  simp [distinctCount, staircase25]

theorem full_support_unique {p : Nat.Partition 325}
    (hp : IsSquareBox 25 p) (hr : distinctCount p = 25) : p = staircase25 := by
  have hs : p.parts.toFinset = Finset.Icc 1 25 := by
    apply Finset.eq_of_subset_of_card_le (support_subset hp)
    simpa [distinctCount] using hr.ge
  have hd : p.parts.dedup = p.parts :=
    Multiset.eq_of_le_of_card_le (Multiset.dedup_le _) (by
      rw [← Multiset.card_toFinset]
      change p.parts.card ≤ distinctCount p
      rw [hr]
      exact hp.1)
  apply Nat.Partition.ext
  change p.parts = (Finset.Icc 1 25).val
  rw [← hd, ← Multiset.toFinset_val, hs]

theorem no_twentyfour_sizes {p : Nat.Partition 325}
    (hp : IsSquareBox 25 p) : distinctCount p ≠ 24 := by
  intro hr
  have hsub := support_subset hp
  have hdiff : (Finset.Icc 1 25 \ p.parts.toFinset).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub]
    change (Finset.Icc 1 25).card - distinctCount p = 1
    rw [hr]
    norm_num
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hdiff
  have hamem : a ∈ Finset.Icc 1 25 \ p.parts.toFinset := by
    rw [ha]
    simp
  obtain ⟨haS, haT⟩ := Finset.mem_sdiff.mp hamem
  have hT : p.parts.toFinset = (Finset.Icc 1 25).erase a := by
    ext b
    have hb : b ∈ Finset.Icc 1 25 \ p.parts.toFinset ↔ b = a := by
      rw [ha]
      simp
    simp only [Finset.mem_sdiff] at hb
    simp only [Finset.mem_erase]
    constructor
    · intro h
      exact ⟨fun e => haT (e ▸ h), hsub h⟩
    · rintro ⟨hne, hmem⟩
      by_contra hnot
      exact hne (hb.mp ⟨hmem, hnot⟩)
  let extra := p.parts - p.parts.dedup
  have hparts : extra + p.parts.dedup = p.parts :=
    Multiset.sub_add_cancel (Multiset.dedup_le _)
  have hecard : extra.card ≤ 1 := by
    dsimp [extra]
    rw [Multiset.card_sub (Multiset.dedup_le _), ← Multiset.card_toFinset]
    change p.parts.card - distinctCount p ≤ 1
    rw [hr]
    have := hp.1
    omega
  have hbase : p.parts.dedup.sum + a = 325 := by
    rw [← Multiset.toFinset_val, hT]
    have hh : (∑ x ∈ (Finset.Icc 1 25).erase a, x) + a = 325 := by
      rw [Finset.sum_erase_add _ _ haS]
      decide +kernel
    rw [Finset.sum_val]
    exact hh
  have hesum : extra.sum = a := by
    have hh := congrArg Multiset.sum hparts
    simp only [Multiset.sum_add, p.parts_sum] at hh
    omega
  have hepos : 0 < extra.card := by
    by_contra h
    have hz : extra = 0 := Multiset.card_eq_zero.mp (by omega)
    rw [hz] at hesum
    have := (Finset.mem_Icc.mp haS).1
    simp only [Multiset.sum_zero] at hesum
    omega
  obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp (by omega : extra.card = 1)
  have hab : b = a := by simpa [hb] using hesum
  have hae : a ∈ extra := by rw [hb, hab]; simp
  have hap : a ∈ p.parts :=
    Multiset.mem_of_le (Multiset.sub_le_self _ _) hae
  exact haT (by simpa using hap)

theorem colorWeight_zero_of_lt {r i j : ℕ} (h : r < i + j) :
    r.choose i * (r - i).choose j = 0 := by
  by_cases hi : r < i
  · rw [Nat.choose_eq_zero_of_lt hi, zero_mul]
  · have hj : r - i < j := by omega
    rw [Nat.choose_eq_zero_of_lt hj, mul_zero]

theorem sourceArray_first : sourceArray 25 325 20 5 = 53130 := by
  classical
  unfold sourceArray
  rw [Finset.sum_eq_single staircase25]
  · rw [staircase25_distinct]
    norm_num [Nat.choose]
  · intro p hp hne
    have hb : IsSquareBox 25 p := (Finset.mem_filter.mp hp).2
    have hl := distinctCount_le hb
    have hne' : distinctCount p ≠ 25 := fun h => hne (full_support_unique hb h)
    apply colorWeight_zero_of_lt
    omega
  · intro hn
    exact False.elim (hn (by simp [squareBox, staircase25_isBox]))

theorem sourceArray_middle : sourceArray 25 325 21 3 = 50600 := by
  classical
  unfold sourceArray
  rw [Finset.sum_eq_single staircase25]
  · rw [staircase25_distinct]
    norm_num [Nat.choose]
  · intro p hp hne
    have hb : IsSquareBox 25 p := (Finset.mem_filter.mp hp).2
    have hl := distinctCount_le hb
    have hne' : distinctCount p ≠ 25 := fun h => hne (full_support_unique hb h)
    have h24 := no_twentyfour_sizes hb
    apply colorWeight_zero_of_lt
    omega
  · intro hn
    exact False.elim (hn (by simp [squareBox, staircase25_isBox]))

end KeithMulticolor
