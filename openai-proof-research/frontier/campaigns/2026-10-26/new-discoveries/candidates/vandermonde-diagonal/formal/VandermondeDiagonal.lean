import Mathlib

open scoped BigOperators
open Matrix Polynomial Finset Filter
namespace VandermondeDiagonal

noncomputable def geometric (b : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => b ^ (i.val * j.val)

lemma geometric_vandermonde (b : ℝ) (n : ℕ) :
    geometric b n = Matrix.vandermonde (fun i : Fin n => b ^ i.val) := by
  ext i j
  simp [geometric, Matrix.vandermonde_apply, pow_mul]

lemma geometric_det_ne_zero (b : ℝ) (hb : 1 < b) (n : ℕ) :
    (geometric b n).det ≠ 0 := by
  rw [geometric_vandermonde, Matrix.det_vandermonde_ne_zero_iff]
  intro i j h
  apply Fin.ext
  exact (pow_right_injective₀ (zero_lt_one.trans hb) hb.ne') h

lemma exp_kernel_posSemidef {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 ≤ c) (x : ι → ℝ) :
    Matrix.PosSemidef (fun i j : ι => Real.exp (c * x i * x j)) := by
  let term : ℕ → Matrix ι ι ℝ := fun k i j => (c * x i * x j) ^ k / k.factorial
  have ht (k : ℕ) : (term k).PosSemidef := by
    have hp := (Matrix.posSemidef_vecMulVec_self_star (fun i => x i ^ k)).smul
      (div_nonneg (pow_nonneg hc k) (Nat.cast_nonneg k.factorial))
    convert hp using 1
    ext i j
    simp [term, Matrix.vecMulVec, mul_pow, div_eq_mul_inv]
    ring
  have hs : HasSum term (fun i j => Real.exp (c * x i * x j)) := by
    apply Pi.hasSum.mpr
    intro i
    apply Pi.hasSum.mpr
    intro j
    simpa [term, ← Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp (c * x i * x j)
  exact Matrix.posSemidef_is_closed.mem_of_tendsto hs
    (Filter.Eventually.of_forall fun s => Matrix.posSemidef_sum s (fun k _ => ht k))

lemma geometric_posDef (b : ℝ) (hb : 1 < b) (n : ℕ) :
    (geometric b n).PosDef := by
  have hp := exp_kernel_posSemidef (Real.log b) (Real.log_nonneg hb.le)
    (fun i : Fin n => (i.val : ℝ))
  have he : (fun i j : Fin n => Real.exp (Real.log b * (i.val : ℝ) * j.val)) =
      geometric b n := by
    funext i j
    simp only [geometric]
    rw [show Real.log b * (i.val : ℝ) * j.val =
      ((i.val * j.val : ℕ) : ℝ) * Real.log b by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans hb)]
  rw [he] at hp
  exact hp.posDef_iff_det_ne_zero.mpr (geometric_det_ne_zero b hb n)

lemma inverse_entry_bound (b : ℝ) (hb : 1 < b) (n : ℕ) (i j : Fin n) :
    ((geometric b n)⁻¹ i j) ^ 2 ≤
      ((geometric b n)⁻¹ i i) * ((geometric b n)⁻¹ j j) := by
  have hp := (geometric_posDef b hb n).inv
  have hc := hp.star_dotProduct_mulVec_mul_le (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq',
    Finset.sum_ite_eq, sq] using hc

lemma diagonal_maximum (b : ℝ) (hb : 1 < b) (n : ℕ) (hn : 0 < n) :
    ∃ i : Fin n, ∀ j k : Fin n,
      |(geometric b n)⁻¹ j k| ≤ |(geometric b n)⁻¹ i i| := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n => (geometric b n)⁻¹ i i) Finset.univ_nonempty
  refine ⟨i, fun j k => ?_⟩
  have hd (a : Fin n) := (geometric_posDef b hb n).inv.diag_pos (i := a)
  have hij := hi.2 j (Finset.mem_univ j)
  have hik := hi.2 k (Finset.mem_univ k)
  have hprod := mul_le_mul hij hik (hd k).le (hd i).le
  have hsq := (inverse_entry_bound b hb n j k).trans hprod
  rw [abs_of_pos (hd i)]
  exact (sq_le_sq₀ (abs_nonneg _) (hd i).le).mp (by simpa [sq_abs, sq] using hsq)



lemma inverse_vandermonde_coeff {n : ℕ} (a : Fin n → ℝ) (ha : Function.Injective a)
    (i j : Fin n) :
    (Matrix.vandermonde a)⁻¹ i j =
      (Lagrange.basis Finset.univ a j).coeff i.val := by
  classical
  let L : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    (Lagrange.basis Finset.univ a j).coeff i.val
  have hvl : Matrix.vandermonde a * L = 1 := by
    ext r c
    have hd : (Lagrange.basis Finset.univ a c).natDegree < n := by
      rw [Lagrange.natDegree_basis ha.injOn (Finset.mem_univ c), Finset.card_univ,
        Fintype.card_fin]
      have := c.isLt
      omega
    have he := Polynomial.eval_eq_sum_range' hd (a r)
    change (∑ k : Fin n, a r ^ k.val * (Lagrange.basis Finset.univ a c).coeff k.val) =
      (if r = c then 1 else 0)
    rw [show (∑ k : Fin n, a r ^ k.val * (Lagrange.basis Finset.univ a c).coeff k.val) =
      ∑ k ∈ Finset.range n, a r ^ k * (Lagrange.basis Finset.univ a c).coeff k from
      Fin.sum_univ_eq_sum_range (fun k => a r ^ k * (Lagrange.basis Finset.univ a c).coeff k) n]
    simp_rw [mul_comm (a r ^ _)]
    rw [← he]
    by_cases h : r = c
    · subst r
      simp [Lagrange.eval_basis_self ha.injOn]
    · simp [Lagrange.eval_basis_of_ne (Ne.symm h), h]
  have hm : (Matrix.vandermonde a)⁻¹ = L := by
    calc
      (Matrix.vandermonde a)⁻¹ = (Matrix.vandermonde a)⁻¹ * 1 := by simp
      _ = (Matrix.vandermonde a)⁻¹ * (Matrix.vandermonde a * L) := by rw [hvl]
      _ = L := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
        (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr ha)), Matrix.one_mul]
  exact congrFun (congrFun hm i) j


lemma coeff_mul_nonneg (p q : ℝ[X])
    (hp : ∀ k, 0 ≤ p.coeff k) (hq : ∀ k, 0 ≤ q.coeff k) (k : ℕ) :
    0 ≤ (p * q).coeff k := by
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun ij _ => mul_nonneg (hp ij.1) (hq ij.2)

lemma plus_product_coeff_nonneg {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (k : ℕ) :
    0 ≤ (∏ i ∈ s, (X + C (a i))).coeff k := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => simp only [Finset.prod_empty, Polynomial.coeff_one]; split_ifs <;> norm_num
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    apply coeff_mul_nonneg
    · intro j
      simp only [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
      split_ifs <;> simp_all
    · exact fun j => ih (fun h hh => ha h (Finset.mem_insert_of_mem hh)) j

lemma prod_minus_comp_neg {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (∏ i ∈ s, (X - C (a i))).comp (-X) =
      C ((-1 : ℝ) ^ s.card) * ∏ i ∈ s, (X + C (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi,
      Polynomial.mul_comp, ih]
    simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, pow_succ, map_mul, map_neg, map_one]
    ring

lemma abs_minus_product_coeff {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (k : ℕ) :
    |(∏ i ∈ s, (X - C (a i))).coeff k| =
      (∏ i ∈ s, (X + C (a i))).coeff k := by
  have he := congrArg (fun p : ℝ[X] => |p.coeff k|) (prod_minus_comp_neg s a)
  rw [show (-X : ℝ[X]) = C (-1) * X by simp,
    Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_C_mul] at he
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, mul_one,
    abs_of_nonneg (plus_product_coeff_nonneg s a ha k)] using he

noncomputable def denominator {n : ℕ} (a : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∏ h ∈ Finset.univ.erase j, |a j - a h|

noncomputable def plusPolynomial {n : ℕ} (a : Fin n → ℝ) (j : Fin n) : ℝ[X] :=
  ∏ h ∈ Finset.univ.erase j, (X + C (a h))

lemma inverse_vandermonde_abs_coeff {n : ℕ} (a : Fin n → ℝ)
    (ha : Function.Injective a) (hpos : ∀ i, 0 ≤ a i) (i j : Fin n) :
    |(Matrix.vandermonde a)⁻¹ i j| = (plusPolynomial a j).coeff i.val / denominator a j := by
  rw [inverse_vandermonde_coeff a ha]
  have hb : Lagrange.basis Finset.univ a j =
      C ((∏ h ∈ Finset.univ.erase j, (a j - a h))⁻¹) *
      ∏ h ∈ Finset.univ.erase j, (X - C (a h)) := by
    simp [Lagrange.basis, Lagrange.basisDivisor, Finset.prod_mul_distrib,
      ← map_prod, ← Finset.prod_inv_distrib]
  rw [hb, Polynomial.coeff_C_mul, abs_mul, abs_inv,
    abs_minus_product_coeff _ a (fun h _ => hpos h)]
  simp only [plusPolynomial, denominator, Finset.abs_prod, div_eq_mul_inv]
  ring


lemma plusPolynomial_antitone {n : ℕ} (a : Fin n → ℝ)
    (hpos : ∀ i, 0 ≤ a i) (j k : Fin n) (hjk : j ≠ k) (hak : a j ≤ a k) (r : ℕ) :
    (plusPolynomial a k).coeff r ≤ (plusPolynomial a j).coeff r := by
  classical
  let s := (Finset.univ.erase j).erase k
  have hpj : plusPolynomial a j = (X + C (a k)) * ∏ h ∈ s, (X + C (a h)) := by
    exact (Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩)).symm
  have hpk : plusPolynomial a k = (X + C (a j)) * ∏ h ∈ s, (X + C (a h)) := by
    have he : (Finset.univ.erase k).erase j = s := by
      ext h
      simp only [Finset.mem_erase, s]
      tauto
    rw [← he]
    exact (Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩)).symm
  rw [hpj, hpk, add_mul, add_mul, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hak
    (plus_product_coeff_nonneg s a (fun h _ => hpos h) r))

noncomputable def denominatorNat (b : ℝ) (n j : ℕ) : ℝ :=
  ∏ h ∈ Finset.range n, if h = j then 1 else |b ^ j - b ^ h|

lemma denominatorNat_pos (b : ℝ) (hb : 1 < b) (n j : ℕ) :
    0 < denominatorNat b n j := by
  apply Finset.prod_pos
  intro h hh
  split_ifs with he
  · norm_num
  · exact abs_pos.mpr (sub_ne_zero.mpr (fun hpow => he
      (((pow_right_strictMono₀ hb).injective hpow).symm)))

lemma denominatorNat_append (b : ℝ) (n j : ℕ) (hj : j < n) :
    denominatorNat b (n+1) j = denominatorNat b n j * |b ^ j - b ^ n| := by
  rw [denominatorNat, Finset.prod_range_succ]
  simp only [ite_eq_right (show n ≠ j by omega)]
  rfl

lemma denominatorNat_shift (b : ℝ) (hb : 0 ≤ b) (n j : ℕ) (hj : j < n) :
    denominatorNat b (n+1) (j+1) =
      |b ^ (j+1) - 1| * b ^ (n-1) * denominatorNat b n j := by
  rw [denominatorNat, Finset.prod_range_succ']
  simp only [show ¬(0 = j + 1) by omega, ↓reduceIte, pow_zero]
  have hf (h : ℕ) : (if h + 1 = j + 1 then (1 : ℝ) else |b ^ (j+1) - b ^ (h+1)|) =
      (if h = j then 1 else b) * (if h = j then 1 else |b ^ j - b ^ h|) := by
    by_cases he : h = j
    · simp [he]
    · simp only [Nat.add_right_cancel_iff, he, ↓reduceIte, pow_succ,
        ← sub_mul, abs_mul, abs_of_nonneg hb]
      ring
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  have hprod : (∏ h ∈ Finset.range n, if h = j then (1 : ℝ) else b) = b ^ (n-1) := by
    rw [← Finset.prod_erase (Finset.range n) (f := fun h => if h = j then (1 : ℝ) else b) (a := j)
      (by simp)]
    simp only [Finset.prod_ite, Finset.filter_eq', Finset.prod_const_one, one_mul]
    have he : {h ∈ (Finset.range n).erase j | ¬h = j} = (Finset.range n).erase j := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
      tauto
    rw [he, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_range.mpr hj),
      Finset.card_range]
  rw [hprod]
  unfold denominatorNat
  ring


lemma denominatorNat_mono_step (b : ℝ) (hb : 1 < b) (n j : ℕ)
    (hj : j < n) (hcut : 1 + 1/b ≤ b ^ j) :
    denominatorNat b (n+1) j ≤ denominatorNat b (n+1) (j+1) := by
  have hbpos := zero_lt_one.trans hb
  have hpow : b ^ j ≤ b ^ n := (pow_right_strictMono₀ hb).monotone hj.le
  have hpowone : 1 ≤ b ^ (j+1) := one_le_pow₀ hb.le
  rw [denominatorNat_append b n j hj, denominatorNat_shift b hbpos.le n j hj,
    abs_of_nonpos (sub_nonpos.mpr hpow), abs_of_nonneg (sub_nonneg.mpr hpowone)]
  have hm : b + 1 ≤ b * b ^ j := by
    have := mul_le_mul_of_nonneg_left hcut hbpos.le
    have he : b * (1 + 1/b) = b + 1 := by field_simp
    rwa [he] at this
  have hy : 0 ≤ b ^ (n-1) := pow_nonneg hbpos.le _
  have hh : 0 ≤ (b * b ^ j - b - 1) * b ^ (n-1) :=
    mul_nonneg (by linarith) hy
  have hn : n - 1 + 1 = n := by omega
  have he : b ^ n = b ^ (n-1) * b := by rw [← pow_succ, hn]
  have hweight : -(b ^ j - b ^ n) ≤ (b ^ (j+1) - 1) * b ^ (n-1) := by
    rw [he, pow_succ]
    nlinarith [pow_nonneg hbpos.le j]
  calc
    denominatorNat b n j * -(b ^ j - b ^ n) ≤
        denominatorNat b n j * ((b ^ (j+1) - 1) * b ^ (n-1)) :=
      mul_le_mul_of_nonneg_left hweight (denominatorNat_pos b hb n j).le
    _ = _ := by ring

lemma denominator_geometric_nat {n : ℕ} (b : ℝ) (j : Fin n) :
    denominator (fun i : Fin n => b ^ i.val) j = denominatorNat b n j.val := by
  classical
  unfold denominator denominatorNat
  rw [show (∏ h ∈ Finset.univ.erase j, |b ^ j.val - b ^ h.val|) =
      ∏ h : Fin n, if h = j then 1 else |b ^ j.val - b ^ h.val| by
    rw [← Finset.prod_erase Finset.univ (a := j) (by simp)]
    apply Finset.prod_congr rfl
    intro h hh
    simp only [Finset.mem_erase] at hh
    simp [hh.1]]
  convert Fin.prod_univ_eq_prod_range
    (fun h => if h = j.val then (1 : ℝ) else |b ^ j.val - b ^ h|) n using 1
  apply Finset.prod_congr rfl
  intro h _
  simp only [Fin.ext_iff]

noncomputable def cutoff (b : ℝ) : ℕ := ⌈Real.logb b (1 + 1/b)⌉₊

lemma cutoff_power (b : ℝ) (hb : 1 < b) (j : ℕ) (hj : cutoff b ≤ j) :
    1 + 1/b ≤ b ^ j := by
  have hx : 0 < 1 + 1/b := by positivity
  have hle : Real.logb b (1 + 1/b) ≤ (j : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hj)
  have := (Real.logb_le_iff_le_rpow hb hx).mp hle
  simpa only [Real.rpow_natCast] using this


lemma inverse_column_step {n : ℕ} (b : ℝ) (hb : 1 < b) (i j k : Fin n)
    (hjk : k.val = j.val + 1) (hcut : cutoff b ≤ j.val) :
    |(geometric b n)⁻¹ i k| ≤ |(geometric b n)⁻¹ i j| := by
  have hpos : ∀ h : Fin n, 0 ≤ b ^ h.val := fun h => pow_nonneg (zero_lt_one.trans hb).le _
  have ha : Function.Injective (fun h : Fin n => b ^ h.val) := by
    intro h l he
    exact Fin.ext ((pow_right_strictMono₀ hb).injective he)
  have hneq : j ≠ k := by intro h; have := congrArg Fin.val h; omega
  have hnodes : b ^ j.val ≤ b ^ k.val := (pow_right_strictMono₀ hb).monotone (by omega)
  have hnum := plusPolynomial_antitone (fun h : Fin n => b ^ h.val) hpos j k hneq hnodes i.val
  have hden : denominatorNat b n j.val ≤ denominatorNat b n k.val := by
    have hn : n-1+1 = n := by have := k.isLt; omega
    have ht : j.val < n-1 := by have := k.isLt; omega
    have hd := denominatorNat_mono_step b hb (n-1) j.val ht (cutoff_power b hb j.val hcut)
    simpa only [hn, ← hjk] using hd
  rw [geometric_vandermonde,
    inverse_vandermonde_abs_coeff _ ha hpos i k,
    inverse_vandermonde_abs_coeff _ ha hpos i j,
    denominator_geometric_nat, denominator_geometric_nat]
  apply (div_le_div_iff₀ (denominatorNat_pos b hb n k.val)
    (denominatorNat_pos b hb n j.val)).mpr
  exact mul_le_mul hnum hden (denominatorNat_pos b hb n j.val).le
    (plus_product_coeff_nonneg _ _ (fun h _ => hpos h) i.val)

lemma inverse_column_localization {n : ℕ} (b : ℝ) (hb : 1 < b)
    (i c j : Fin n) (hc : c.val = cutoff b) (hj : cutoff b ≤ j.val) :
    |(geometric b n)⁻¹ i j| ≤ |(geometric b n)⁻¹ i c| := by
  have hall : ∀ t, cutoff b ≤ t → ∀ ht : t < n,
      |(geometric b n)⁻¹ i ⟨t, ht⟩| ≤ |(geometric b n)⁻¹ i c| := by
    intro t hle
    induction t, hle using Nat.le_induction with
    | base =>
      intro ht
      have he : (⟨cutoff b, ht⟩ : Fin n) = c := Fin.ext hc.symm
      rw [he]
    | succ t hle ih =>
      intro ht
      have ht' : t < n := by omega
      exact (inverse_column_step b hb i ⟨t, ht'⟩ ⟨t+1, ht⟩ rfl hle).trans (ih ht')
  exact hall j.val hj j.isLt

lemma geometric_inverse_symm (b : ℝ) (hb : 1 < b) (n : ℕ) (i j : Fin n) :
    (geometric b n)⁻¹ i j = (geometric b n)⁻¹ j i := by
  simpa using ((geometric_posDef b hb n).inv.isHermitian.apply j i)

theorem source_conjecture_all_orders (b : ℝ) (hb : 1 < b) (n : ℕ) (hn : 0 < n) :
    ∃ i : Fin n, i.val ≤ cutoff b ∧ ∀ j k : Fin n,
      |(geometric b n)⁻¹ j k| ≤ |(geometric b n)⁻¹ i i| := by
  obtain ⟨i, hi⟩ := diagonal_maximum b hb n hn
  by_cases hic : i.val ≤ cutoff b
  · exact ⟨i, hic, hi⟩
  · have hc : cutoff b < n := lt_trans (by omega) i.isLt
    let c : Fin n := ⟨cutoff b, hc⟩
    have hbound : |(geometric b n)⁻¹ i i| ≤ |(geometric b n)⁻¹ c c| := by
      calc
        |(geometric b n)⁻¹ i i| ≤ |(geometric b n)⁻¹ i c| :=
          inverse_column_localization b hb i c i rfl (by omega)
        _ = |(geometric b n)⁻¹ c i| := by rw [geometric_inverse_symm b hb n i c]
        _ ≤ |(geometric b n)⁻¹ c c| :=
          inverse_column_localization b hb c c i rfl (by omega)
    exact ⟨c, le_rfl, fun j k => (hi j k).trans hbound⟩

end VandermondeDiagonal
