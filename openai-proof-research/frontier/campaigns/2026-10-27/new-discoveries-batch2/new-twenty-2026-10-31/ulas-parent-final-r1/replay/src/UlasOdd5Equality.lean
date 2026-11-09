import UlasOdd5Bounds
set_option linter.unusedSimpArgs false
open PowerSeries Polynomial
namespace Ulas.Round5Odd
open Round4
theorem constant_residue_3 (t : ℤ) : ∃ z : ℤ,
    2*(16*t+3)^2*((16*t+3)+1)*((16*t+3)+5) = 128*z+64 := by
  refine ⟨(4)*t^0 + (75)*t^1 + (452)*t^2 + (1152)*t^3 + (1024)*t^4,?_⟩
  ring
theorem constant_residue_7 (t : ℤ) : ∃ z : ℤ,
    2*(16*t+7)^2*((16*t+7)+1)*((16*t+7)+5) = 128*z+64 := by
  refine ⟨(73)*t^0 + (581)*t^1 + (1700)*t^2 + (2176)*t^3 + (1024)*t^4,?_⟩
  ring
theorem constant_three_exact (k : ℕ) (R : Polynomial ℤ)
    (hR : Round2.transferDiff (4*k+3) 0 = y*(1+y)*ev R)
    (hm : (4*k+3)%16=3 ∨ (4*k+3)%16=7) : ¬ (2:ℤ)^7 ∣ R.coeff 0 := by
  have hp := initial_constant_polynomial (4*k+3) R hR
  have he : ∃ t : ℕ, 4*k+3=16*t+3 ∨ 4*k+3=16*t+7 := by
    refine ⟨k/4,?_⟩; omega
  obtain ⟨t,ht|ht⟩ := he
  · rw [ht] at hp
    obtain ⟨z,hz⟩ := constant_residue_3 (t:ℤ)
    push_cast at hp
    intro hd
    obtain ⟨b,hb⟩ := hd
    norm_num at hb
    rw [hb] at hp
    omega
  · rw [ht] at hp
    obtain ⟨z,hz⟩ := constant_residue_7 (t:ℤ)
    push_cast at hp
    intro hd
    obtain ⟨b,hb⟩ := hd
    norm_num at hb
    rw [hb] at hp
    omega

theorem oddThreeEquality : OddThreeEquality := by
  intro k n hn heq
  obtain ⟨R,hR,hc⟩ := odd_initialization (2*k+1)
  have hm : 2*(2*k+1)+1=4*k+3 := by omega
  rw [hm] at hR
  have h0 := constant_three_dvd k R hR
  have h1 := low1_residue_4_3 (k:ℤ) (R.coeff 1) (by simpa using initial_low1 (4*k+3) R hR)
  have h2 := low2_residue_4_3 (k:ℤ) (R.coeff 2) (by simpa using initial_low2 (4*k+3) R hR)
  rcases heq with ⟨hm16,hodd⟩|⟨hm16,hn4⟩
  · have hh : ∀ E, E≠0 → (2:ℤ)^7 ∣ R.coeff E := by
      intro E hE
      by_cases he1 : E=1
      · simpa [he1] using h1
      by_cases he2 : E=2
      · simpa [he2] using h2
      exact dvd_trans (pow_dvd_pow _ (by omega)) (hc E)
    have hv := exact_readout (4*k+3) 6 n R hodd h0 (constant_three_exact k R hR hm16) hh
    have hr := diff_reduced_readout (4*k+3) 0 n R hR
    simp only [pow_zero,one_mul,Round3.reducedIter] at hr
    rw [← hr] at hv
    have hz : padicValNat 2 n=0 := padicValNat.eq_zero_of_not_dvd (by omega)
    simpa [val,hz] using hv
  · have ht : 4*k+3=16*(k/4)+11 := by omega
    have hl := initial_low1 (4*k+3) R hR
    rw [ht] at hl
    have hlow := low1_residue_16_11 ((k/4):ℤ) (R.coeff 1) (by simpa using hl)
    have hw := reduced_weight_seven (4*k+3) R hc h0 h1 h2
    have hc0 : (2:ℤ)^8 ∣ 2*(((4*k+3:ℕ):ℤ)+1)*R.coeff 0 := by
      obtain ⟨z,hz⟩ := h0
      refine ⟨2*((k:ℤ)+1)*z,?_⟩
      rw [hz]
      push_cast
      ring
    have hnd : ¬ (2:ℤ)^8 ∣ (Round3.reduced (4*k+3) R).coeff 0 := by
      rw [Round3.coeff_reduced_zero]
      intro hd
      exact hlow.2 (by simpa using dvd_sub hd hc0)
    have hhigh : ∀ E, E≠0 → (2:ℤ)^8 ∣ (Round3.reduced (4*k+3) R).coeff E := by
      intro E hE
      exact dvd_trans (pow_dvd_pow _ (by have := Nat.size_pos.mpr (Nat.pos_of_ne_zero hE); omega)) (hw E)
    have hodd : (n/2)%2=1 := by omega
    have hv := exact_readout (4*k+3) 7 (n/2) (Round3.reduced (4*k+3) R) hodd
      (by simpa using hw 0) hnd hhigh
    have hr := diff_reduced_readout (4*k+3) 1 (n/2) R hR
    have hnn : 2^1*(n/2)=n := by omega
    rw [hnn] at hr
    change diff (4*k+3) n = coeff (n/2) (C^(4*k+3)*(y*(1+y)*ev (Round3.reduced (4*k+3) R))) at hr
    rw [← hr] at hv
    have hz : padicValNat 2 n = 1 := by
      have hq : padicValNat 2 (n/2)=0 := padicValNat.eq_zero_of_not_dvd (by omega)
      have he : n=2*(n/2) := by omega
      rw [he,padicValNat.mul (by decide : (2:ℕ)≠0) (by omega : n/2≠0),hq]
      norm_num
    simpa [val,hz] using hv
end Ulas.Round5Odd
