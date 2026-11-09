import BergmanSource

open Finset Polynomial
namespace BergmanUnitCircle

def exponent (m n r q : ℕ) : ℤ :=
  (((m:ℤ)-n)*r+q-n+1)/(m:ℤ)

lemma exponent_mul {m n r q : ℕ}
    (hd : (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*r-n+1) :
    exponent m n r q * (m:ℤ) = ((m:ℤ)-n)*r+q-n+1 := by
  apply Int.ediv_mul_cancel
  convert dvd_add (dvd_mul_right (m:ℤ) (r:ℤ)) hd using 1; ring

lemma exponent_bounds {m n r q : ℕ} (hn : 0 < n) (hmn : n < m)
    (hr : r < 2*m-1) (hq : q < 2*m-1)
    (hd : (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*r-n+1) :
    0 ≤ exponent m n r q ∧ exponent m n r q ≤ 2*((m:ℤ)-n) := by
  have hm : (0:ℤ) < m := by exact_mod_cast (by omega : 0 < m)
  have hn' : (0:ℤ) < n := by exact_mod_cast hn
  have hmn' : (n:ℤ) < m := by exact_mod_cast hmn
  have hr' : (r:ℤ) ≤ 2*(m:ℤ)-2 := by omega
  have hq' : (q:ℤ) ≤ 2*(m:ℤ)-2 := by omega
  have he := exponent_mul hd
  constructor
  · by_contra hh
    have ha : exponent m n r q ≤ -1 := by omega
    have h1 := mul_nonneg hm.le (by omega : 0 ≤ -exponent m n r q-1)
    have h2 := mul_nonneg (by omega : 0 ≤ (m:ℤ)-n) (Int.natCast_nonneg r)
    nlinarith
  · by_contra hh
    have ha : 2*((m:ℤ)-n)+1 ≤ exponent m n r q := by omega
    have h1 := mul_nonneg hm.le (by omega : 0 ≤ exponent m n r q-2*((m:ℤ)-n)-1)
    have h2 := mul_nonneg (by omega : 0 ≤ (m:ℤ)-n) (by omega : 0 ≤ 2*(m:ℤ)-2-r)
    nlinarith

/-- The exact source diagonal as an ordinary polynomial with natural coefficients. -/
noncomputable def naturalQ (m n : ℕ) : ℕ[X] :=
  ∑ r ∈ range (2*m-1), ∑ q ∈ range (2*m-1),
    if (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*r-n+1 then
      C (D m r * D m q) * X^(exponent m n r q).toNat else 0

noncomputable def polynomialQ (m n : ℕ) : ℂ[X] :=
  (naturalQ m n).map (Nat.castRingHom ℂ)

lemma polynomialQ_eval {m n : ℕ} (hn : 0 < n) (hmn : n < m)
    {z : ℂ} : (polynomialQ m n).eval z = compressedQ m n z := by
  rw [polynomialQ,Polynomial.eval_map]
  unfold naturalQ compressedQ
  simp only [Polynomial.eval₂_finsetSum]
  apply sum_congr rfl
  intro r hr
  apply sum_congr rfl
  intro q hq
  split_ifs with hd
  · have hb := (exponent_bounds hn hmn (mem_range.mp hr) (mem_range.mp hq) hd).1
    simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_pow,
      Polynomial.eval₂_X]
    rw [← zpow_natCast,Int.toNat_of_nonneg hb]
    rfl
  · simp

lemma polynomialQ_eval_source {m n : ℕ} (hn : 0 < n) (hmn : n < m)
    {z : ℂ} (hz : z ≠ 0) : (polynomialQ m n).eval z = sourceQ m n z := by
  rw [polynomialQ_eval hn hmn,sourceQ_eq_compressedQ hn hmn hz]

lemma naturalQ_degree_le {m n : ℕ} (hn : 0 < n) (hmn : n < m) :
    (naturalQ m n).natDegree ≤ 2*(m-n) := by
  unfold naturalQ
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro r hr
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro q hq
  split_ifs with hd
  · apply le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _)
    have hb := exponent_bounds hn hmn (mem_range.mp hr) (mem_range.mp hq) hd
    omega
  · simp

lemma naturalQ_term_coeff_le {m n r q : ℕ} (hr : r < 2*m-1) (hq : q < 2*m-1)
    (hd : (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*r-n+1) (i : ℕ) :
    (C (D m r * D m q) * X^(exponent m n r q).toNat : ℕ[X]).coeff i ≤
      (naturalQ m n).coeff i := by
  unfold naturalQ
  simp only [Polynomial.finsetSum_coeff]
  have h1 := Finset.single_le_sum (s:=range (2*m-1))
    (fun j _ => Nat.zero_le ((if (m:ℤ) ∣ (j:ℤ)-(n:ℤ)*r-n+1 then
      C (D m r * D m j) * X^(exponent m n r j).toNat else (0:ℕ[X])).coeff i))
    (mem_range.mpr hq)
  rw [ite_eq_left hd] at h1
  have h2 := Finset.single_le_sum (s:=range (2*m-1))
    (f:=fun (j:ℕ) => ∑ q ∈ range (2*m-1),
      (if (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*j-n+1 then
        C (D m j * D m q) * X^(exponent m n j q).toNat else (0:ℕ[X])).coeff i)
    (fun j _ => Nat.zero_le _) (mem_range.mpr hr)
  exact h1.trans h2

lemma naturalQ_coeff_pos {m n r q i : ℕ} (hr : r < 2*m-1) (hq : q < 2*m-1)
    (hd : (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*r-n+1) (he : (exponent m n r q).toNat=i)
    (hDr : 0 < D m r) (hDq : 0 < D m q) : 0 < (naturalQ m n).coeff i := by
  have h := naturalQ_term_coeff_le hr hq hd i
  rw [Polynomial.coeff_C_mul_X_pow,he,ite_eq_left rfl] at h
  exact lt_of_lt_of_le (Nat.mul_pos hDr hDq) h

lemma naturalQ_constant_pos {m n : ℕ} (hn : 0 < n) (hmn : n < m) :
    0 < (naturalQ m n).coeff 0 := by
  have hq : ((n-1:ℕ):ℤ)=(n:ℤ)-1 := by omega
  have hd : (m:ℤ) ∣ ((n-1:ℕ):ℤ)-(n:ℤ)*0-n+1 := by
    rw [hq]
    simp
  apply naturalQ_coeff_pos (r:=0) (q:=n-1) (by omega) (by omega) hd
  · simp [exponent,hq]
  · have hm : 0 < m := by omega
    simp [D,hm]
  · unfold D
    split_ifs <;> omega

lemma naturalQ_leading_pos {m n : ℕ} (hn : 0 < n) (hmn : n < m) :
    0 < (naturalQ m n).coeff (2*(m-n)) := by
  have hr : ((2*m-2:ℕ):ℤ)=2*(m:ℤ)-2 := by omega
  have hq : ((2*m-n-1:ℕ):ℤ)=2*(m:ℤ)-n-1 := by omega
  have hk : ((2*(m-n):ℕ):ℤ)=2*((m:ℤ)-n) := by omega
  have hd : (m:ℤ) ∣ ((2*m-n-1:ℕ):ℤ)-(n:ℤ)*(2*m-2:ℕ)-n+1 := by
    refine ⟨2-2*(n:ℤ),?_⟩
    rw [hr,hq]
    ring
  have he : exponent m n (2*m-2) (2*m-n-1)=((2*(m-n):ℕ):ℤ) := by
    unfold exponent
    apply Int.ediv_eq_of_eq_mul_left (by exact_mod_cast (by omega : m ≠ 0))
    rw [hr,hq,hk]
    ring
  apply naturalQ_coeff_pos (r:=2*m-2) (q:=2*m-n-1) (by omega) (by omega) hd
  · rw [he]
    exact Int.toNat_natCast _
  · unfold D
    split_ifs <;> omega
  · unfold D
    split_ifs <;> omega

lemma naturalQ_degree {m n : ℕ} (hn : 0 < n) (hmn : n < m) :
    (naturalQ m n).natDegree=2*(m-n) :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (naturalQ_degree_le hn hmn)
    (Nat.ne_of_gt (naturalQ_leading_pos hn hmn))

lemma polynomialQ_degree {m n : ℕ} (hn : 0 < n) (hmn : n < m) :
    (polynomialQ m n).natDegree=2*(m-n) := by
  rw [polynomialQ,Polynomial.natDegree_map_eq_of_injective (by exact Nat.cast_injective),
    naturalQ_degree hn hmn]

lemma polynomialQ_constant_ne_zero {m n : ℕ} (hn : 0 < n) (hmn : n < m) :
    (polynomialQ m n).coeff 0 ≠ 0 := by
  simp only [polynomialQ,Polynomial.coeff_map]
  change ((naturalQ m n).coeff 0:ℂ) ≠ 0
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (naturalQ_constant_pos hn hmn))

def mirror (m r : ℕ) : ℕ := 2*m-2-r

lemma mirror_cast {m r : ℕ} (hr : r < 2*m-1) :
    (mirror m r:ℤ)=2*(m:ℤ)-2-r := by
  unfold mirror
  omega

lemma D_mirror {m r : ℕ} (hr : r < 2*m-1) : D m (mirror m r)=D m r := by
  rw [D_nat_cast,D_nat_cast]
  unfold BergmanConvolution.triangle mirror
  split_ifs <;> omega

lemma mirror_condition {m n r q : ℕ} (hr : r < 2*m-1) (hq : q < 2*m-1) :
    (m:ℤ) ∣ (mirror m q:ℤ)-(n:ℤ)*mirror m r-n+1 ↔
      (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*r-n+1 := by
  have hs : (m:ℤ) ∣ ((mirror m q:ℤ)-(n:ℤ)*mirror m r-n+1)+
      ((q:ℤ)-(n:ℤ)*r-n+1) := by
    refine ⟨2-2*(n:ℤ),?_⟩
    rw [mirror_cast hr,mirror_cast hq]
    ring
  constructor
  · intro hd
    convert dvd_sub hs hd using 1; ring
  · intro hd
    convert dvd_sub hs hd using 1; ring

lemma exponent_mirror {m n r q : ℕ} (hn : 0 < n) (hmn : n < m)
    (hr : r < 2*m-1) (hq : q < 2*m-1)
    (hd : (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*r-n+1) :
    exponent m n (mirror m r) (mirror m q)=2*((m:ℤ)-n)-exponent m n r q := by
  unfold exponent at ⊢
  apply Int.ediv_eq_of_eq_mul_left (by exact_mod_cast (by omega : m ≠ 0))
  have he := exponent_mul hd
  rw [mirror_cast hr,mirror_cast hq]
  unfold exponent at he
  nlinarith

lemma reflect_sum {R I : Type*} [Semiring R] (s : Finset I) (F : I→R[X]) (N : ℕ) :
    Polynomial.reflect N (∑ i ∈ s,F i)=∑ i ∈ s,Polynomial.reflect N (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.reflect_zero]
  | @insert a s ha ih => simp only [sum_insert ha,Polynomial.reflect_add,ih]

lemma naturalQ_reflect {m n : ℕ} (hn : 0 < n) (hmn : n < m) :
    Polynomial.reflect (2*(m-n)) (naturalQ m n)=naturalQ m n := by
  unfold naturalQ
  rw [reflect_sum]
  simp_rw [reflect_sum]
  calc
    _ = ∑ r ∈ range (2*m-1), ∑ q ∈ range (2*m-1),
        if (m:ℤ) ∣ (mirror m q:ℤ)-(n:ℤ)*mirror m r-n+1 then
          C (D m (mirror m r)*D m (mirror m q)) *
            X^(exponent m n (mirror m r) (mirror m q)).toNat else (0:ℕ[X]) := by
      apply sum_congr rfl
      intro r hr
      apply sum_congr rfl
      intro q hq
      have hr' := mem_range.mp hr
      have hq' := mem_range.mp hq
      by_cases hd : (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*r-n+1
      · have hdm := (mirror_condition hr' hq').mpr hd
        rw [ite_eq_left hd,ite_eq_left hdm,Polynomial.reflect_C_mul_X_pow,
          D_mirror hr',D_mirror hq',exponent_mirror hn hmn hr' hq' hd]
        have hb := exponent_bounds hn hmn hr' hq' hd
        have he : (exponent m n r q).toNat ≤ 2*(m-n) := by omega
        rw [Polynomial.revAt_le he]
        congr 2
        omega
      · have hdm := mt (mirror_condition hr' hq').mp hd
        rw [ite_eq_right hd,ite_eq_right hdm,Polynomial.reflect_zero]
    _ = _ := by
      let F : ℕ→ℕ→ℕ[X] := fun r q =>
        if (m:ℤ) ∣ (q:ℤ)-(n:ℤ)*r-n+1 then
          C (D m r * D m q) * X^(exponent m n r q).toNat else 0
      have hm (r : ℕ) : mirror m r=(2*m-1)-1-r := by unfold mirror; omega
      change (∑ r ∈ range (2*m-1), ∑ q ∈ range (2*m-1), F (mirror m r) (mirror m q)) =
        ∑ r ∈ range (2*m-1), ∑ q ∈ range (2*m-1), F r q
      simp_rw [hm]
      calc
        _ = ∑ r ∈ range (2*m-1), ∑ q ∈ range (2*m-1), F ((2*m-1)-1-r) q := by
          apply sum_congr rfl
          intro r _
          exact Finset.sum_range_reflect (fun q => F ((2*m-1)-1-r) q) (2*m-1)
        _ = _ := Finset.sum_range_reflect (fun r => ∑ q ∈ range (2*m-1), F r q) (2*m-1)

lemma polynomialQ_reverse {m n : ℕ} (hn : 0 < n) (hmn : n < m) :
    (polynomialQ m n).reverse=polynomialQ m n := by
  change Polynomial.reflect (polynomialQ m n).natDegree (polynomialQ m n)=polynomialQ m n
  rw [polynomialQ_degree hn hmn]
  unfold polynomialQ
  rw [Polynomial.reflect_map,naturalQ_reflect hn hmn]

end BergmanUnitCircle
