import Antimagic5ARowSums
namespace Antimagic.Round5A
open Round4A

abbrev InternalVertex (t n : ℕ) := {v : Nonroot t n // v.val.1.val < n}

theorem internal_range (t n h i : ℕ) (ht : 4 ≤ t) (he : Even t) (hn : 3 ≤ n)
    (hh : 1 ≤ h) (hhn : h < n) (hi : i < t ^ h) :
    1 ≤ internalLabel t n h i ∧ internalLabel t n h i ≤ internalEdges t n := by
  by_cases h1 : h = 1
  · subst h
    have hs := internalEdges_split t n (by omega)
    have hz := shell_size t n he hn
    have hZ : 1 ≤ center t n := by simp [center]
    simp only [pow_one] at hi
    simp only [internalLabel, ite_true]
    split_ifs <;> omega
  · have hr := internal_shell_range t n h i ht he (by omega) hhn hi
    have hs := internalEdges_split t n (by omega)
    omega

def internalMap (t n : ℕ) (ht : 4 ≤ t) (he : Even t) (hn : 3 ≤ n)
    (v : InternalVertex t n) : Fin (internalEdges t n) :=
  ⟨internalLabel t n v.val.val.1.val v.val.val.2.val - 1, by
    have := internal_range t n _ _ ht he hn v.val.property v.property v.val.val.2.isLt
    simp only [depth] at this
    omega⟩

/-- Internal labels give a literal permutation on actual nonroot model vertices. -/
theorem internalMap_bijective (t n : ℕ) (ht : 4 ≤ t) (he : Even t) (hn : 3 ≤ n) :
    Function.Bijective (internalMap t n ht he hn) := by
  constructor
  · intro v w eq
    have hv := internal_range t n _ _ ht he hn v.val.property v.property v.val.val.2.isLt
    have hw := internal_range t n _ _ ht he hn w.val.property w.property w.val.val.2.isLt
    simp only [depth] at hv hw
    have eqv := congrArg Fin.val eq
    change internalLabel t n v.val.val.1.val v.val.val.2.val - 1 =
      internalLabel t n w.val.val.1.val w.val.val.2.val - 1 at eqv
    have hc := internalLabel_injective t n _ _ _ _ ht he hn v.val.property w.val.property
      v.property w.property v.val.val.2.isLt w.val.val.2.isLt (by simp only [depth]; omega)
    exact Subtype.ext (vertex_ext hc.1 hc.2)
  · intro x
    obtain ⟨h,i,hh,hhn,hi,heq⟩ := internalLabel_exists t n (x.val+1) ht he hn (by have := x.isLt; omega)
    refine ⟨⟨⟨⟨⟨h,by omega⟩,⟨i,hi⟩⟩,hh⟩,hhn⟩,?_⟩
    apply Fin.ext
    change internalLabel t n h i - 1 = x.val
    omega

/-- Positive global range for the exact inherited formula, on actual vertices. -/
theorem formula_range_rows (s n h i : ℕ) (hs : 2 ≤ s) (hn : 3 ≤ n) (hh : 1 ≤ h) (hhn : h ≤ n) (hi : i < (2*s)^h) :
    1 ≤ label (2*s) n h i ∧
    label (2*s) n h i ≤ internalEdges (2*s) n + (2*s)^n := by
  have he : Even (2*s) := ⟨s,by omega⟩
  simp only [label,show n ≠ 1 by omega,show n ≠ 2 by omega,ite_false]
  by_cases hlast : h < n
  · rw [largeLabel,ite_eq_left hlast]
    have := internal_range (2*s) n _ _ (by omega) he hn hh hlast hi
    omega
  · have hdepth : h = n := by omega
    have hidx : i < (2*s)^n := by simpa only [hdepth] using hi
    have hparent : i / (2*s) < (2*s)^(n-1) := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2*s)).mpr
      rw [show n = (n-1)+1 by omega,pow_succ] at hidx
      exact hidx
    have ha := parentParameter_range (2*s) n _ (by omega) he hn hparent
    have hp := even_power (2*s) (n-1) he (by omega)
    have hj := Nat.mod_lt i (by omega : 0 < 2*s)
    have hr := leafEntry_range s ((2*s)^(n-1)/2) (parentParameter (2*s) n (i/(2*s)))
      (i%(2*s)) (by omega) (by omega) hj
    rw [hdepth,show i = (2*s)*(i/(2*s))+i%(2*s) from (Nat.div_add_mod _ _).symm,
      leaf_formula s n _ _ hs hn hj]
    have hexp : (2*s)^n = (2*s)*(2*((2*s)^(n-1)/2)) := by
      conv_lhs => rw [show n = (n-1)+1 by omega,pow_succ]
      rw [← hp]; exact Nat.mul_comm _ _
    omega

#print axioms internalMap_bijective
#print axioms formula_range_rows
end Antimagic.Round5A
