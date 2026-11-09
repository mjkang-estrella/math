import CountR7CWeights
noncomputable section
open scoped BigOperators
namespace ChanLevine.Round7C
open Round6 Round3
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Exact-total chip sum, with selected matching endpoints forced empty. -/
def chipSum {F : Type*} [CommRing F] (z : F) (s : Finset (ZMod n)) (m : ℕ) : F :=
  ∑ x : BoundedChips n m, (∏ v, (z ^ v.val) ^ (x.val v).val) *
    (if ∀ v ∈ s ∪ rightEnds s, (x.val v).val = 0 then 1 else 0)

/-- Rotor summation now acts on the literal frozen configuration character. -/
theorem forced_config_sum (k : ZMod n) (s : Finset (ZMod n)) (hs : Matching s)
    (m : ℕ) :
    (∑ c : {c : Config n // chipLevel c = m},
      (countingChar n).char (-(chipWeight c.val*k)) *
        ∏ v ∈ s, (if Round5.emptyFacing c.val v then 1 else 0)) =
      chipSum (frequencyRoot n k) s m *
        ((frequencyRoot n k)^s.card * (1+frequencyRoot n k)^(n-2*s.card)) := by
  rw [sum_level_reindex m (fun c =>
    (countingChar n).char (-(chipWeight c*k)) *
      ∏ v ∈ s, (if Round5.emptyFacing c v then 1 else 0))]
  simp_rw [Fintype.sum_prod_type, char_chipWeight, selected_indicator]
  have he (x : BoundedChips n m) (q : ZMod n → Bool) :
      ((∏ v, (frequencyRoot n k ^ v.val) ^ (x.val v).val) *
          (∏ v, if q v then 1 else frequencyRoot n k)) *
        ((if ∀ v ∈ s ∪ rightEnds s, (x.val v).val = 0 then 1 else 0) *
          (if ∀ v ∈ s, q v = true ∧ q (v+1) = false then 1 else 0)) =
      ((∏ v, (frequencyRoot n k ^ v.val) ^ (x.val v).val) *
          (if ∀ v ∈ s ∪ rightEnds s, (x.val v).val = 0 then 1 else 0)) *
        ((∏ v, if q v then 1 else frequencyRoot n k) *
          (if ∀ v ∈ s, q v = true ∧ q (v+1) = false then 1 else 0)) := by ring
  simp_rw [he, ← Finset.mul_sum, forced_rotor_sum _ s hs]
  rw [← Finset.sum_mul]
  rfl

def matchingSeries {F : Type*} [CommRing F] (z : F) (m : ℕ) : F :=
  ∑ s ∈ (Finset.univ : Finset (ZMod n)).powerset,
    if Matching s then (-z)^s.card * (1+z)^(n-2*s.card) * chipSum z s m else 0

/-- Positive-level matching expansion of the original Fourier count. -/
theorem fourier_matching (m : ℕ) (hm : 0 < m) (k : ZMod n) :
    finiteFourier (countingChar n).char (countVector n m) k =
      matchingSeries (n := n) (frequencyRoot n k) m := by
  rw [Round5.fourier_inclusion_exclusion m hm k]
  unfold matchingSeries
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Matching s
  · rw [ite_eq_left hs]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [forced_config_sum k s hs m]
    rw [neg_eq_neg_one_mul, mul_pow]
    ring
  · rw [ite_eq_right hs]
    apply Finset.sum_eq_zero
    intro c _
    rw [nonmatching_indicator c.val s hs, mul_zero]
end ChanLevine.Round7C
