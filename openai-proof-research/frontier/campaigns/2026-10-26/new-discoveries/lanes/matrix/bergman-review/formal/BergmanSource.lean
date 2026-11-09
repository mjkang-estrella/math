import BergmanConvolution

open Finset
namespace BergmanUnitCircle

/-- The source triangular coefficient, including its zero extension to all integers. -/
def D (m : ℕ) (u : ℤ) : ℕ :=
  if u < 0 then 0 else if u < m then (u+1).toNat else (2*(m:ℤ)-1-u).toNat

lemma D_nat_cast (m r : ℕ) : D m (r:ℤ) = BergmanConvolution.triangle m r := by
  unfold D BergmanConvolution.triangle
  split_ifs <;> omega

lemma D_support {m : ℕ} {u : ℤ} (h : D m u ≠ 0) :
    0 ≤ u ∧ u < 2*(m:ℤ)-1 := by
  unfold D at h
  split_ifs at h <;> omega

/-- The exact second triangular index in source Proposition1.10, equation1.11. -/
def sourceIndex (m n r b : ℕ) : ℤ :=
  (m:ℤ)*b + (n:ℤ)*r + m+n-1-2*(m:ℤ)*n

lemma sourceIndex_divisible (m n r b : ℕ) :
    (m:ℤ) ∣ sourceIndex m n r b - (n:ℤ)*r-n+1 := by
  refine ⟨(b:ℤ)+1-2*n, ?_⟩
  unfold sourceIndex
  ring

lemma sourceIndex_injective {m n r : ℕ} (hm : 0 < m) :
    Function.Injective (sourceIndex m n r) := by
  intro a b he
  have hmi : (0:ℤ)< m := by exact_mod_cast hm
  unfold sourceIndex at he
  have hab : (a:ℤ)=(b:ℤ) := by nlinarith
  exact_mod_cast hab

lemma sourceIndex_preimage {m n r q : ℕ} (hn : 0< n) (hmn : n< m)
    (hr : r< 2*m-1) (hq : q< 2*m-1)
    (hd : (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*r-n+1) :
    ∃ b< 2*n+1, sourceIndex m n r b=(q:ℤ) := by
  have hmi : (0:ℤ)< m := by exact_mod_cast (by omega : 0< m)
  have hni : (0:ℤ)< n := by exact_mod_cast hn
  have hri : (r:ℤ)≤2*(m:ℤ)-2 := by omega
  have hqi : (q:ℤ)≤2*(m:ℤ)-2 := by omega
  obtain ⟨t,ht⟩ := hd
  let b : ℤ := t+2*n-1
  have he : (m:ℤ)*b+(n:ℤ)*r+m+n-1-2*(m:ℤ)*n=q := by
    dsimp [b]
    nlinarith [ht]
  have hb0 : 0≤b := by
    by_contra hh
    have hb : b≤-1 := by omega
    have h1 := mul_nonneg hmi.le (by omega : 0≤-b-1)
    have h2 := mul_nonneg hni.le (by omega : 0≤2*(m:ℤ)-2-r)
    nlinarith
  have hb2 : b≤2*(n:ℤ) := by
    by_contra hh
    have hb : 2*(n:ℤ)+1≤b := by omega
    have h1 := mul_nonneg hmi.le (by omega : 0≤b-2*(n:ℤ)-1)
    have h2 := mul_nonneg hni.le (Int.natCast_nonneg r)
    nlinarith
  refine ⟨b.toNat, ?_, ?_⟩
  · omega
  · unfold sourceIndex
    rw [Int.toNat_of_nonneg hb0]
    exact he

/-- Reindexing the literal source coefficient row by its supported triangular index. -/
theorem source_row_reindex {R : Type*} [AddCommMonoid R]
    {m n r : ℕ} (hn : 0< n) (hmn : n< m) (hr : r< 2*m-1) (F : ℤ→R) :
    (∑ b ∈ range (2*n+1), D m (sourceIndex m n r b) • F (sourceIndex m n r b)) =
    ∑ q ∈ range (2*m-1),
      if (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*r-n+1 then D m (q:ℤ) • F q else 0 := by
  have hm : 0< m := by omega
  apply Finset.sum_bij_ne_zero (fun b _ _ => (sourceIndex m n r b).toNat)
  · intro b hb hf
    have hd : D m (sourceIndex m n r b) ≠ 0 := by
      intro he
      simp [he] at hf
    obtain ⟨h0,h2⟩ := D_support hd
    apply mem_range.mpr
    omega
  · intro a ha hfa b hb hfb he
    have hda : D m (sourceIndex m n r a) ≠ 0 := by
      intro hz
      simp [hz] at hfa
    have hdb : D m (sourceIndex m n r b) ≠ 0 := by
      intro hz
      simp [hz] at hfb
    apply sourceIndex_injective (n:=n) (r:=r) hm
    have h0a := (D_support hda).1
    have h0b := (D_support hdb).1
    omega
  · intro q hq hg
    have hd : (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*r-n+1 := by
      by_contra hh
      simp [hh] at hg
    obtain ⟨b,hb,he⟩ := sourceIndex_preimage hn hmn hr (mem_range.mp hq) hd
    refine ⟨b,mem_range.mpr hb, ?_, ?_⟩
    · simpa only [he,ite_eq_left hd] using hg
    · rw [he]
      simp
  · intro b hb hf
    have hd : D m (sourceIndex m n r b) ≠ 0 := by
      intro he
      simp [he] at hf
    have h0 := (D_support hd).1
    have he : ((sourceIndex m n r b).toNat:ℤ)=sourceIndex m n r b :=
      Int.toNat_of_nonneg h0
    simp only [he,ite_eq_left (sourceIndex_divisible m n r b)]

/-- Literal numerator in source Proposition1.10, with the stated finite support1.12. -/
noncomputable def sourceP (m n : ℕ) (s t : ℂ) : ℂ :=
  ∑ r ∈ range (2*m-1), ∑ b ∈ range (2*n+1),
    ((D m r * D m (sourceIndex m n r b) : ℕ):ℂ) * s^r * t^b

/-- The source diagonal normalization Q(z)=z^(1-2n)P(z,z). -/
noncomputable def sourceQ (m n : ℕ) (z : ℂ) : ℂ :=
  z^((1:ℤ)-2*n) * sourceP m n z z

/-- The equivalent supported triangular coefficient sum, with integer exponents. -/
noncomputable def compressedQ (m n : ℕ) (z : ℂ) : ℂ :=
  ∑ r ∈ range (2*m-1), ∑ q ∈ range (2*m-1),
    if (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*r-n+1 then
      ((D m r * D m q : ℕ):ℂ) * z^((((m:ℤ)-n)*r+q-n+1)/(m:ℤ))
    else 0

lemma source_exponent {m : ℕ} (hm : 0 < m) (n r b : ℕ) :
    (((m:ℤ)-n)*r+sourceIndex m n r b-n+1)/(m:ℤ)=
      (r:ℤ)+b+1-2*n := by
  apply Int.ediv_eq_of_eq_mul_left (by exact_mod_cast (Nat.ne_of_gt hm))
  unfold sourceIndex
  ring

/-- Exact, unconditional source-to-supported-sum bridge; no sum-of-squares premise. -/
theorem sourceQ_eq_compressedQ {m n : ℕ} (hn : 0 < n) (hmn : n < m)
    {z : ℂ} (hz : z ≠ 0) : sourceQ m n z = compressedQ m n z := by
  have hm : 0 < m := by omega
  unfold sourceQ sourceP compressedQ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    _ = (D m r:ℂ) * ∑ b ∈ range (2*n+1),
        (D m (sourceIndex m n r b):ℂ) *
          z^((((m:ℤ)-n)*r+sourceIndex m n r b-n+1)/(m:ℤ)) := by
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [source_exponent hm]
      have he : (r:ℤ)+b+1-2*n=((1:ℤ)-2*n)+((r:ℤ)+(b:ℤ)) := by ring
      rw [he,zpow_add₀ hz,zpow_add₀ hz]
      simp only [zpow_natCast,Nat.cast_mul]
      ring
    _ = (D m r:ℂ) * ∑ q ∈ range (2*m-1),
        if (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*r-n+1 then
          (D m q:ℂ)*z^((((m:ℤ)-n)*r+q-n+1)/(m:ℤ)) else 0 := by
      congr 1
      have h := source_row_reindex hn hmn (mem_range.mp hr)
        (fun q : ℤ => z^((((m:ℤ)-n)*r+q-n+1)/(m:ℤ)))
      simpa only [nsmul_eq_mul] using h
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> simp [Nat.cast_mul,mul_assoc]

end BergmanUnitCircle
