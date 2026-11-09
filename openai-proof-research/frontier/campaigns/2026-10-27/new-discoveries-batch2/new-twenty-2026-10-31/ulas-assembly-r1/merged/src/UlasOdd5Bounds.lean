import UlasOdd5LowIdentification
set_option linter.unusedSimpArgs false
open PowerSeries Polynomial
namespace Ulas.Round5Odd
open Round4

theorem constant_three_dvd (k : ℕ) (R : Polynomial ℤ)
    (hR : Round2.transferDiff (4*k+3) 0 = y*(1+y)*ev R) : (2:ℤ)^6 ∣ R.coeff 0 := by
  have hp := initial_constant_polynomial (4*k+3) R hR
  have hc : IsCoprime ((2:ℤ)^6) 3 := by rw [Int.isCoprime_iff_gcd_eq_one]; norm_num
  apply hc.dvd_of_dvd_mul_left
  rw [hp]
  have hd : (2:ℤ) ∣ ((k:ℤ)+1)*((k:ℤ)+2) := by
    have he : (2:ℤ) ∣ (k:ℤ)+1 ∨ (2:ℤ) ∣ (k:ℤ)+2 := by omega
    rcases he with he|he
    · exact dvd_mul_of_dvd_left he _
    · exact dvd_mul_of_dvd_right he _
  obtain ⟨z,hz⟩ := hd
  refine ⟨((4*k+3:ℕ):ℤ)^2*z,?_⟩
  push_cast
  linear_combination 32*(4*(k:ℤ)+3)^2*hz

theorem constant_fifteen_dvd (t : ℕ) (R : Polynomial ℤ)
    (hR : Round2.transferDiff (16*t+15) 0 = y*(1+y)*ev R) : (2:ℤ)^7 ∣ R.coeff 0 := by
  have hp := initial_constant_polynomial (16*t+15) R hR
  have hc : IsCoprime ((2:ℤ)^7) 3 := by rw [Int.isCoprime_iff_gcd_eq_one]; norm_num
  apply hc.dvd_of_dvd_mul_left
  rw [hp]
  refine ⟨((16*t+15:ℕ):ℤ)^2*((t:ℤ)+1)*(4*(t:ℤ)+5),?_⟩
  push_cast
  ring

theorem weighted_five (R : Polynomial ℤ)
    (hc : ∀ E, (2:ℤ)^(2*E+3) ∣ R.coeff E)
    (h0 : (2:ℤ)^6 ∣ R.coeff 0) (h1 : (2:ℤ)^7 ∣ R.coeff 1)
    (h2 : (2:ℤ)^7 ∣ R.coeff 2) : Round3.Weighted 5 R := by
  intro E
  by_cases he0 : E=0
  · subst E; norm_num; exact dvd_trans (by norm_num) h0
  by_cases he1 : E=1
  · subst E; norm_num; exact dvd_trans (by norm_num) h1
  by_cases he2 : E=2
  · subst E; exact h2
  exact dvd_trans (pow_dvd_pow _ (by have := Round3.size_le_self E; omega)) (hc E)

theorem initial_coeff_dvd (R : Polynomial ℤ) (v : ℕ) (hv : v ≤ 7)
    (hc : ∀ E, (2:ℤ)^(2*E+3) ∣ R.coeff E)
    (h0 : (2:ℤ)^v ∣ R.coeff 0) (h1 : (2:ℤ)^7 ∣ R.coeff 1)
    (h2 : (2:ℤ)^7 ∣ R.coeff 2) : ∀ E, (2:ℤ)^v ∣ R.coeff E := by
  intro E
  by_cases he0 : E=0
  · simpa [he0] using h0
  by_cases he1 : E=1
  · subst E; exact dvd_trans (pow_dvd_pow _ hv) h1
  by_cases he2 : E=2
  · subst E; exact dvd_trans (pow_dvd_pow _ hv) h2
  exact dvd_trans (pow_dvd_pow _ (by omega)) (hc E)

theorem reduced_weight_seven (m : ℕ) (R : Polynomial ℤ)
    (hc : ∀ E, (2:ℤ)^(2*E+3) ∣ R.coeff E)
    (h0 : (2:ℤ)^6 ∣ R.coeff 0) (h1 : (2:ℤ)^7 ∣ R.coeff 1)
    (h2 : (2:ℤ)^7 ∣ R.coeff 2) : Round3.Weighted 7 (Round3.reduced m R) := by
  rw [Round3.reduced_main_tail]
  apply Round3.weighted_add
  · intro E
    rw [coeff_reducedMain]
    apply dvd_add
    · split_ifs with he
      · subst E
        norm_num only [Nat.size_zero,Nat.add_zero]
        have hd := mul_dvd_mul_left (2:ℤ) h0
        convert dvd_mul_of_dvd_left hd ((m:ℤ)+1) using 1 <;> ring
      · exact dvd_zero _
    · by_cases he : E=0
      · simpa [he] using h1
      · exact dvd_trans (pow_dvd_pow _ (by have := Round3.size_le_self E; omega)) (hc (2*E+1))
  · exact Round3.weighted_reducedTail m 5 R (weighted_five R hc h0 h1 h2)
end Ulas.Round5Odd
namespace Ulas.Round5Odd
open Round4

theorem reducedIter_shift (m j : ℕ) (R : Polynomial ℤ) :
    Round3.reducedIter m R (j+1) = Round3.reducedIter m (Round3.reduced m R) j := by
  induction j with
  | zero => rfl
  | succ j ih => simpa only [Round3.reducedIter] using congrArg (Round3.reduced m) ih

theorem bound_from_first_step (m v : ℕ) (hm : 1 ≤ m) (R : Polynomial ℤ)
    (hR : Round2.transferDiff m 0 = y*(1+y)*ev R)
    (hc : ∀ E, (2:ℤ)^v ∣ R.coeff E)
    (hw : Round3.Weighted (v+1) (Round3.reduced m R))
    (n : ℕ) (hn : 1 ≤ n) : padicValNat 2 n+v ≤ val m n := by
  obtain ⟨o,ho⟩ := pow_padicValNat_dvd (p:=2) (n:=n)
  have hd : (2:ℤ)^(v+padicValNat 2 n) ∣ diff m n := by
    conv_rhs => rw [ho,diff_reduced_readout m (padicValNat 2 n) o R hR,← mul_assoc]
    apply coeff_dvd_mul_right
    apply coeff_dvd_ev
    cases hj : padicValNat 2 n with
    | zero => simpa [Round3.reducedIter] using hc
    | succ j =>
      rw [reducedIter_shift]
      intro E
      have ht := Round3.weighted_coeff_dvd (Round3.weighted_reducedIter m (v+1) j _ hw) E
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht
  have hv := ((padicValInt_dvd_iff (p:=2) (v+padicValNat 2 n) _).mp hd).resolve_left
    (diff_ne_zero m n hm hn)
  exact Nat.add_comm v (padicValNat 2 n) ▸ hv

theorem oddThreeBound : OddThreeBound := by
  intro k n hn
  obtain ⟨R,hR,hc⟩ := odd_initialization (2*k+1)
  have hm : 2*(2*k+1)+1=4*k+3 := by omega
  rw [hm] at hR
  have h0 := constant_three_dvd k R hR
  have h1 := low1_residue_4_3 (k:ℤ) (R.coeff 1) (by simpa using initial_low1 (4*k+3) R hR)
  have h2 := low2_residue_4_3 (k:ℤ) (R.coeff 2) (by simpa using initial_low2 (4*k+3) R hR)
  refine ⟨diff_ne_zero _ _ (by omega) hn,?_⟩
  exact bound_from_first_step (4*k+3) 6 (by omega) R hR
    (initial_coeff_dvd R 6 (by omega) hc h0 h1 h2)
    (reduced_weight_seven (4*k+3) R hc h0 h1 h2) n hn

theorem fifteenBound : FifteenBound := by
  intro t n hn
  obtain ⟨R,hR,hc⟩ := odd_initialization (8*t+7)
  have hm : 2*(8*t+7)+1=16*t+15 := by omega
  rw [hm] at hR
  have h0 := constant_fifteen_dvd t R hR
  have h1 := low1_residue_16_15 (t:ℤ) (R.coeff 1) (by simpa using initial_low1 (16*t+15) R hR)
  have h2 := low2_residue_16_15 (t:ℤ) (R.coeff 2) (by simpa using initial_low2 (16*t+15) R hR)
  have hw : Round3.Weighted 7 R := by
    intro E
    by_cases he0 : E=0
    · subst E; exact h0
    by_cases he1 : E=1
    · subst E; exact dvd_trans (by norm_num) h1
    by_cases he2 : E=2
    · subst E; exact dvd_trans (by decide : (2:ℤ)^(7+Nat.size 2) ∣ (2:ℤ)^11) h2
    by_cases he3 : E=3
    · subst E; exact hc 3
    exact dvd_trans (pow_dvd_pow _ (by have := Round3.size_le_self E; omega)) (hc E)
  obtain ⟨o,ho⟩ := pow_padicValNat_dvd (p:=2) (n:=n)
  refine ⟨diff_ne_zero _ _ (by omega) hn,?_⟩
  have hd := diff_dvd_of_weighted (16*t+15) 7 (padicValNat 2 n) o R hR hw
  rw [← ho] at hd
  have hv := ((padicValInt_dvd_iff (p:=2) (7+padicValNat 2 n) _).mp hd).resolve_left
    (diff_ne_zero _ _ (by omega) hn)
  exact Nat.add_comm 7 (padicValNat 2 n) ▸ hv
end Ulas.Round5Odd
