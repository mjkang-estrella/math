import UlasOdd5Representative
set_option linter.unusedSimpArgs false
open PowerSeries Polynomial
namespace Ulas.Round5Odd
open Round4

theorem crude_weighted (R : Polynomial ℤ)
    (hR : ∀ F, (2:ℤ)^(2*F+3) ∣ R.coeff F) : Round3.Weighted 3 R := by
  intro E
  exact dvd_trans (pow_dvd_pow _ (by have := Round3.size_le_self E; omega)) (hR E)

theorem oddOneBound : OddOneBound := by
  intro k n hn
  obtain ⟨R,hR,hc⟩ := odd_initialization (2*k)
  have hm : 2*(2*k)+1 = 4*k+1 := by omega
  rw [hm] at hR
  obtain ⟨o,ho⟩ := pow_padicValNat_dvd (p:=2) (n:=n)
  refine ⟨diff_ne_zero _ _ (by omega) hn,?_⟩
  have hd := diff_dvd_of_weighted (4*k+1) 3 (padicValNat 2 n) o R hR (crude_weighted R hc)
  rw [← ho] at hd
  have hv := ((padicValInt_dvd_iff (p:=2) (3+padicValNat 2 n) _).mp hd).resolve_left
    (diff_ne_zero _ _ (by omega) hn)
  exact Nat.add_comm 3 (padicValNat 2 n) ▸ hv

theorem one_constant_not_dvd (k : ℕ) (R : Polynomial ℤ)
    (hR : Round2.transferDiff (4*k+1) 0 = y*(1+y)*ev R) : ¬ (2:ℤ)^4 ∣ R.coeff 0 := by
  have hp := initial_constant_polynomial (4*k+1) R hR
  intro hd
  have hh : (16:ℤ) ∣ 2*((4*k+1:ℕ):ℤ)^2*(((4*k+1:ℕ):ℤ)+1)*(((4*k+1:ℕ):ℤ)+5) := by
    rw [← hp]
    exact dvd_mul_of_dvd_right hd 3
  have he : 2*((4*k+1:ℕ):ℤ)^2*(((4*k+1:ℕ):ℤ)+1)*(((4*k+1:ℕ):ℤ)+5) =
      16*(32*(k:ℤ)^4+80*(k:ℤ)^3+58*(k:ℤ)^2+16*(k:ℤ)+1)+8 := by
    push_cast
    ring
  rw [he] at hh
  obtain ⟨z,hz⟩ := hh
  omega

theorem oddOneEquality : OddOneEquality := by
  intro k n hn hodd
  obtain ⟨R,hR,hc⟩ := odd_initialization (2*k)
  have hm : 2*(2*k)+1=4*k+1 := by omega
  rw [hm] at hR
  have hex := exact_readout (4*k+1) 3 n R hodd
    (by simpa using hc 0) (one_constant_not_dvd k R hR)
    (fun E hE => dvd_trans (pow_dvd_pow _ (by omega : 3+1 ≤ 2*E+3)) (hc E))
  have hr := diff_reduced_readout (4*k+1) 0 n R hR
  simp only [pow_zero,one_mul,Round3.reducedIter] at hr
  rw [← hr] at hex
  have hv : padicValNat 2 n = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  simpa [val,hv] using hex
end Ulas.Round5Odd
