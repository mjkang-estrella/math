import CountR5Inclusion
noncomputable section
open scoped BigOperators
namespace ChanLevine.Round5
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

abbrev TestedLevel (n m : ℕ) [NeZero n] :=
  {c : Config n // CycleTest c ∧ chipLevel c = m}

instance testedLevel_finite (m : ℕ) : Finite (TestedLevel n m) :=
  Finite.of_injective
    (fun c => (⟨c.val, c.property.2⟩ : {c : Config n // chipLevel c = m}))
    (by intro a b h; exact Subtype.ext (congrArg (fun t : {c : Config n // chipLevel c = m} => t.val) h))

noncomputable instance testedLevel_fintype (m : ℕ) : Fintype (TestedLevel n m) :=
  Fintype.ofFinite _

def weightFibreEquiv (m : ℕ) (i : ZMod n) :
    {c : TestedLevel n m // chipWeight c.val = i} ≃
      {c : Config n // CycleTest c ∧ chipLevel c = m ∧ chipWeight c = i} where
  toFun c := ⟨c.val.val, c.val.property.1, c.val.property.2, c.property⟩
  invFun c := ⟨⟨c.val, c.property.1, c.property.2.1⟩, c.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Fourier sum of the original cardinality function is the weighted sum over
its literal finite configuration fibre. No transfer assumption is used. -/
theorem fourier_literal_fibre (m : ℕ) (k : ZMod n) :
    finiteFourier (countingChar n).char (countVector n m) k =
      ∑ c : TestedLevel n m, (countingChar n).char (-(chipWeight c.val*k)) := by
  classical
  have h := Fintype.sum_fiberwise' (fun c : TestedLevel n m => chipWeight c.val)
    (fun i => (countingChar n).char (-(i*k)))
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  have hc : Fintype.card {c : TestedLevel n m // chipWeight c.val = i} = testCount n m i := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (weightFibreEquiv m i)
  simp [countVector, hc, mul_comm]

noncomputable instance level_fintype (m : ℕ) :
    Fintype {c : Config n // chipLevel c = m} := Fintype.ofFinite _

/-- Weighted inclusion-exclusion after summing over the literal level fibre.
The character is applied to the full frozen chipWeight, including all rotors. -/
theorem fourier_inclusion_exclusion (m : ℕ) (hm : 0 < m) (k : ZMod n) :
    finiteFourier (countingChar n).char (countVector n m) k =
      ∑ s ∈ (Finset.univ : Finset (ZMod n)).powerset,
        ∑ c : {c : Config n // chipLevel c = m},
          (-1 : CountingField n)^s.card *
            (countingChar n).char (-(chipWeight c.val*k)) *
              ∏ v ∈ s, (if emptyFacing c.val v then 1 else 0) := by
  classical
  rw [fourier_literal_fibre]
  let e : TestedLevel n m → {c : Config n // chipLevel c = m} :=
    fun c => ⟨c.val, c.property.2⟩
  have he : Function.Injective e := by
    intro a b h
    exact Subtype.ext (congrArg (fun t : {c : Config n // chipLevel c = m} => t.val) h)
  have hs := Fintype.sum_of_injective e he
    (fun c => (countingChar n).char (-(chipWeight c.val*k)))
    (fun c => (countingChar n).char (-(chipWeight c.val*k)) *
      if CycleTest c.val then 1 else 0)
    (by
      intro c hc
      have hn : ¬ CycleTest c.val := by
        intro ht
        exact hc ⟨⟨c.val, ht, c.property⟩, rfl⟩
      simp [hn])
    (by intro c; simp [e, c.property.1])
  rw [hs]
  trans ∑ c : {c : Config n // chipLevel c = m},
    ∑ s ∈ (Finset.univ : Finset (ZMod n)).powerset,
      (-1 : CountingField n)^s.card *
        (countingChar n).char (-(chipWeight c.val*k)) *
          ∏ v ∈ s, (if emptyFacing c.val v then 1 else 0)
  · apply Finset.sum_congr rfl
    intro c _
    exact weighted_inclusion_exclusion c.val (by simpa only [c.property] using hm) _
  · rw [Finset.sum_comm]
end ChanLevine.Round5
