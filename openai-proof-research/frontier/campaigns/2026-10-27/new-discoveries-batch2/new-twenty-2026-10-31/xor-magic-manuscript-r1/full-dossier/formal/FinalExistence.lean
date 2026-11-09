import MainRanges
import BaseEndpoints
import Complements
namespace XorMagic
theorem ClosedExists.complement {n d : ℕ} (h : ClosedExists n d) (hn : 2 ≤ n)
    (high : 2^n ≤ 2*(2^n-1-d)) : OpenExists n (2^n-1-d) := by
  obtain ⟨V,_,_,G,_,hr,hm⟩ := h
  have hc : Fintype.card V = 2^n := by obtain ⟨_,l,_⟩ := hm; exact card_of_label l
  refine ⟨V,inferInstance,inferInstance,Gᶜ,inferInstance,?_,?_⟩
  · simpa [hc] using hr.compl
  · exact closed_to_open_compl hn G hr hm (by simpa [hc] using high)

theorem OpenExists.complement {n d : ℕ} (h : OpenExists n d) (hn : 2 ≤ n)
    (high : 2^n ≤ 2*(2^n-1-d)) : ClosedExists n (2^n-1-d) := by
  obtain ⟨V,_,_,G,_,hr,hm⟩ := h
  have hc : Fintype.card V = 2^n := by obtain ⟨_,l,_⟩ := hm; exact card_of_label l
  refine ⟨V,inferInstance,inferInstance,Gᶜ,inferInstance,?_,?_⟩
  · simpa [hc] using hr.compl
  · exact open_to_closed_compl hn G hr hm (by simpa [hc] using high)

/-- Every degree in both corrected ranges, with no construction hypotheses. -/
theorem corrected_all : ∀ n : ℕ, 4 ≤ n → CorrectedAt n := by
  intro n hn
  by_cases h4 : n = 4
  · subst n; exact corrected_at_4
  by_cases h5 : n = 5
  · subst n; exact corrected_at_5
  have h6 : 6 ≤ n := by omega
  have h64 : 64 ≤ 2^n := calc
    64 = 2^6 := by norm_num
    _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) h6
  have he : 2^n = 2*2^(n-1) := by
    rw [← pow_succ']; congr 1; omega
  obtain ⟨ho,hc⟩ := main_ranges n h6
  constructor
  · intro q hq hl hu
    by_cases hb : q ≤ 2^n-9
    · exact ho q hq hl hb
    have alternatives : q = 2^n-7 ∨ q = 2^n-5 := by
      obtain ⟨k,hk⟩ := hq
      omega
    rcases alternatives with rfl | rfl
    · have hh := (hc 6 (by decide) (by decide) (by omega)).complement (by omega) (by omega)
      simpa only [Nat.sub_sub] using hh
    · have hh := (hc 4 (by decide) (by decide) (by omega)).complement (by omega) (by omega)
      simpa only [Nat.sub_sub] using hh
  · intro q hq hl hu
    by_cases hb : q ≤ 2^n-8
    · exact hc q hq hl hb
    have eq : q = 2^n-6 := by obtain ⟨k,hk⟩ := hq; omega
    subst q
    have hh := (ho 5 (by decide) (by decide) (by omega)).complement (by omega) (by omega)
    simpa only [Nat.sub_sub] using hh
end XorMagic
#print axioms XorMagic.corrected_all
