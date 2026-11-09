import BergmanGram

open Finset
namespace BergmanUnitCircle

noncomputable def coefficientWeight (m n r q : ℕ) (z : ℂ) : ℂ :=
  if (m:ℤ) ∣ ((q:ℤ)-(n:ℤ)*r-n+1) then
    z^(((((m:ℤ)-n)*r+q-n+1)/(m:ℤ))) else 0

lemma reflected_condition {m n p p' q q' : ℕ} (hmn : n < m)
    (hp' : p' < m) (hq' : q' < m) :
    (m:ℤ) ∣ (((q+(m-1-q'):ℕ):ℤ)-(n:ℤ)*((p+(m-1-p'):ℕ):ℤ)-n+1) ↔
    (((m-n)*p+q)%m=((m-n)*p'+q')%m) := by
  rw [Int.dvd_iff_emod_eq_zero]
  have hpp : p' ≤ m-1 := by omega
  have hqq : q' ≤ m-1 := by omega
  have hm1 : 1 ≤ m := by omega
  push_cast [Nat.cast_sub hpp,Nat.cast_sub hqq,Nat.cast_sub hm1]
  have he : (q:ℤ)+((m:ℤ)-1-q')-(n:ℤ)*(p+((m:ℤ)-1-p'))-n+1 =
      (q-(n:ℤ)*p)-(q'-(n:ℤ)*p')+(m:ℤ)*(1-n) := by ring
  rw [he]
  simp only [Int.add_emod, Int.mul_emod, Int.emod_self, zero_mul, Int.zero_emod,
    add_zero, Int.emod_emod]
  rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero]
  have hmod (a b : ℕ) : ((b:ℤ)-(n:ℤ)*a)%(m:ℤ) =
      (((m:ℤ)-n)*a+b)%(m:ℤ) := by
    have hh : ((m:ℤ)-n)*a+b=(b-(n:ℤ)*a)+(m:ℤ)*a := by ring
    rw [hh]
    simp [Int.add_emod]
  rw [hmod,hmod]
  rw [← Nat.cast_sub (le_of_lt hmn)]
  exact_mod_cast (Iff.rfl : ((m-n)*p+q)%m=((m-n)*p'+q')%m ↔ _)

lemma reflected_exponent {m n p p' q q' : ℕ} (hmn : n < m)
    (hp' : p' < m) (hq' : q' < m)
    (he : ((m-n)*p+q)%m=((m-n)*p'+q')%m) :
    (((m:ℤ)-n)*((p+(m-1-p'):ℕ):ℤ)+(q+(m-1-q'):ℕ)-n+1)/(m:ℤ) =
    ((m-n:ℕ):ℤ)+(((m-n)*p+q)/m:ℕ)-(((m-n)*p'+q')/m:ℕ) := by
  have hm : 0 < m := by omega
  have hpp : p' ≤ m-1 := by omega
  have hqq : q' ≤ m-1 := by omega
  have hm1 : 1 ≤ m := by omega
  have hnm : n ≤ m := le_of_lt hmn
  have hd := Nat.mod_add_div ((m-n)*p+q) m
  have hd' := Nat.mod_add_div ((m-n)*p'+q') m
  have hdI : (↑(((m-n)*p+q)%m):ℤ)+(m:ℤ)*(((m-n)*p+q)/m:ℕ) =
      ((m:ℤ)-n)*p+q := by exact_mod_cast hd
  have hdI' : (↑(((m-n)*p'+q')%m):ℤ)+(m:ℤ)*(((m-n)*p'+q')/m:ℕ) =
      ((m:ℤ)-n)*p'+q' := by exact_mod_cast hd'
  rw [he] at hdI
  push_cast [Nat.cast_sub hnm] at hdI hdI'
  have htarget : (((m:ℤ)-n)*((p+(m-1-p'):ℕ):ℤ)+(q+(m-1-q'):ℕ)-n+1) =
      (m:ℤ)*(((m-n:ℕ):ℤ)+(((m-n)*p+q)/m:ℕ)-(((m-n)*p'+q')/m:ℕ)) := by
    push_cast [Nat.cast_sub hpp,Nat.cast_sub hqq,Nat.cast_sub hm1,Nat.cast_sub hnm]
    nlinarith [hdI,hdI']
  rw [htarget,Int.mul_ediv_cancel_left _ (by exact_mod_cast (Nat.ne_of_gt hm))]

lemma unit_power_difference {z : ℂ} (hz : ‖z‖=1) (k a b : ℕ) :
    z^((k:ℤ)+a-b) = z^k*(z^a*star (z^b)) := by
  have hn : z≠0 := by intro he; simp [he] at hz
  rw [sub_eq_add_neg,zpow_add₀ hn,zpow_add₀ hn]
  simp only [zpow_natCast,zpow_neg]
  rw [← inv_pow,Complex.inv_eq_conj hz]
  simp [mul_assoc]

lemma reflected_weight {m n p p' q q' : ℕ} (hmn : n < m)
    (hp' : p' < m) (hq' : q' < m) {z : ℂ} (hz : ‖z‖=1) :
    coefficientWeight m n (p+(m-1-p')) (q+(m-1-q')) z =
    z^(m-n)*(if ((m-n)*p+q)%m=((m-n)*p'+q')%m then
      z^(((m-n)*p+q)/m)*star (z^(((m-n)*p'+q')/m)) else 0) := by
  unfold coefficientWeight
  by_cases he : ((m-n)*p+q)%m=((m-n)*p'+q')%m
  · have hc := (reflected_condition hmn hp' hq').mpr he
    rw [ite_eq_left hc,ite_eq_left he,reflected_exponent hmn hp' hq' he,
      unit_power_difference hz]
  · have hc := mt (reflected_condition hmn hp' hq').mp he
    rw [ite_eq_right hc,ite_eq_right he,mul_zero]

end BergmanUnitCircle
