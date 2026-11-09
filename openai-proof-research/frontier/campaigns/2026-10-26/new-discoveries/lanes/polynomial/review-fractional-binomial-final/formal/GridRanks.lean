import Mathlib

namespace GridRanks

/-- Rank of the left grid point, with ties placed after the right grid point. -/
def L (j l r : ℕ) : ℕ := r + (l * r) / j

/-- Rank of the right grid point, with ties placed before the left grid point. -/
def R (j l s : ℕ) : ℕ := s + (j * s - 1) / l

lemma L_strictMono (j l : ℕ) : StrictMono (L j l) := by
  intro r t hrt
  have hdiv : (l * r) / j ≤ (l * t) / j :=
    Nat.div_le_div_right (Nat.mul_le_mul_left l (Nat.le_of_lt hrt))
  unfold L
  omega

lemma R_strictMono (j l : ℕ) : StrictMono (R j l) := by
  intro r t hrt
  have hmul : j * r - 1 ≤ j * t - 1 :=
    Nat.sub_le_sub_right (Nat.mul_le_mul_left j (Nat.le_of_lt hrt)) 1
  have hdiv : (j * r - 1) / l ≤ (j * t - 1) / l := Nat.div_le_div_right hmul
  unfold R
  omega

lemma L_injective (j l : ℕ) : Function.Injective (L j l) :=
  (L_strictMono j l).injective

lemma R_injective (j l : ℕ) : Function.Injective (R j l) :=
  (R_strictMono j l).injective

lemma L_mem_Icc {j l r : ℕ} (hj : 0 < j) (hr : r ∈ Finset.Icc 1 j) :
    L j l r ∈ Finset.Icc 1 (j + l) := by
  obtain ⟨hr1, hrj⟩ := Finset.mem_Icc.mp hr
  have hdiv : (l * r) / j ≤ l := by
    calc
      (l * r) / j ≤ (l * j) / j := Nat.div_le_div_right (Nat.mul_le_mul_left l hrj)
      _ = l := by rw [Nat.mul_comm, Nat.mul_div_cancel_left _ hj]
  apply Finset.mem_Icc.mpr
  constructor
  · exact hr1.trans (Nat.le_add_right r _)
  · exact Nat.add_le_add hrj hdiv

lemma R_mem_Icc {j l s : ℕ} (hj : 0 < j) (hl : 0 < l)
    (hs : s ∈ Finset.Icc 1 l) : R j l s ∈ Finset.Icc 1 (j + l) := by
  obtain ⟨hs1, hsl⟩ := Finset.mem_Icc.mp hs
  have hjs : 0 < j * s := Nat.mul_pos hj hs1
  have hsub : j * s - 1 < j * l := by
    have hmul := Nat.mul_le_mul_left j hsl
    omega
  have hdiv : (j * s - 1) / l < j := (Nat.div_lt_iff_lt_mul hl).mpr hsub
  apply Finset.mem_Icc.mpr
  constructor
  · exact hs1.trans (Nat.le_add_right s _)
  · simpa only [R, Nat.add_comm] using Nat.add_le_add hsl (Nat.le_of_lt hdiv)

/-- The two tie conventions ensure that no positive right-grid point has a left rank. -/
lemma L_ne_R {j l r s : ℕ} (hj : 0 < j) (hl : 0 < l) (hs : 0 < s) :
    L j l r ≠ R j l s := by
  intro heq
  have hsum : r + (l * r) / j = s + (j * s - 1) / l := heq
  have hleftLow : j * ((l * r) / j) ≤ l * r := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self (l * r) j
  have hrightLow : l * ((j * s - 1) / l) ≤ j * s - 1 := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self (j * s - 1) l
  have hjs : 0 < j * s := Nat.mul_pos hj hs
  by_cases ha : s ≤ (l * r) / j
  · have hb : r ≤ (j * s - 1) / l := by omega
    have h1 := Nat.mul_le_mul_left j ha
    have h2 := Nat.mul_le_mul_left l hb
    omega
  · have hb : (j * s - 1) / l < r := by omega
    have hleftUp := Nat.lt_mul_div_succ (l * r) hj
    have hrightUp := Nat.lt_mul_div_succ (j * s - 1) hl
    have h1 := Nat.mul_le_mul_left j (show (l * r) / j + 1 ≤ s by omega)
    have h2 := Nat.mul_le_mul_left l (show (j * s - 1) / l + 1 ≤ r by omega)
    omega

def leftRanks (j l : ℕ) : Finset ℕ := (Finset.Icc 1 j).image (L j l)
def rightRanks (j l : ℕ) : Finset ℕ := (Finset.Icc 1 l).image (R j l)

lemma leftRanks_subset {j l : ℕ} (hj : 0 < j) :
    leftRanks j l ⊆ Finset.Icc 1 (j + l) := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
  exact L_mem_Icc hj hr

lemma rightRanks_subset {j l : ℕ} (hj : 0 < j) (hl : 0 < l) :
    rightRanks j l ⊆ Finset.Icc 1 (j + l) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
  exact R_mem_Icc hj hl hs

lemma ranks_disjoint {j l : ℕ} (hj : 0 < j) (hl : 0 < l) :
    Disjoint (leftRanks j l) (rightRanks j l) := by
  apply Finset.disjoint_left.mpr
  intro t htL htR
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp htL
  obtain ⟨s, hs, hsr⟩ := Finset.mem_image.mp htR
  exact L_ne_R hj hl (Finset.mem_Icc.mp hs).1 (hr.trans hsr.symm)

lemma leftRanks_card (j l : ℕ) : (leftRanks j l).card = j := by
  rw [leftRanks, Finset.card_image_of_injective _ (L_injective j l), Nat.card_Icc]
  omega

lemma rightRanks_card (j l : ℕ) : (rightRanks j l).card = l := by
  rw [rightRanks, Finset.card_image_of_injective _ (R_injective j l), Nat.card_Icc]
  omega

/-- The ranks form an exact partition of all ranks 1 through j+l. -/
theorem ranks_union {j l : ℕ} (hj : 0 < j) (hl : 0 < l) :
    leftRanks j l ∪ rightRanks j l = Finset.Icc 1 (j + l) := by
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.union_subset (leftRanks_subset hj) (rightRanks_subset hj hl)
  · rw [Finset.card_union_of_disjoint (ranks_disjoint hj hl),
      leftRanks_card, rightRanks_card, Nat.card_Icc]
    omega

/-- Multiplication form of the left grid's comparison with its assigned rank. -/
lemma L_rank_bound (j l r : ℕ) : j * L j l r ≤ (j + l) * r := by
  have h := Nat.div_mul_le_self (l * r) j
  unfold L
  nlinarith

/-- The right grid's assigned rank is strictly before the point, including at ties. -/
lemma R_rank_bound {j l s : ℕ} (hj : 0 < j) (hs : 0 < s) :
    l * R j l s < (j + l) * s := by
  have h := Nat.div_mul_le_self (j * s - 1) l
  have hjs : 0 < j * s := Nat.mul_pos hj hs
  unfold R
  nlinarith [Nat.sub_add_cancel (show 1 ≤ j * s by omega)]

/-- Sum over the merged rank interval, expressed in the two original grids. -/
theorem sum_partition {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    {j l : ℕ} (hj : 0 < j) (hl : 0 < l) :
    (∑ r ∈ Finset.Icc 1 j, f (L j l r)) +
      (∑ s ∈ Finset.Icc 1 l, f (R j l s)) =
      ∑ t ∈ Finset.Icc 1 (j + l), f t := by
  rw [← ranks_union hj hl, Finset.sum_union (ranks_disjoint hj hl)]
  congr 1
  · rw [leftRanks, Finset.sum_image]
    intro a _ b _ hab
    exact L_injective j l hab
  · rw [rightRanks, Finset.sum_image]
    intro a _ b _ hab
    exact R_injective j l hab

end GridRanks
