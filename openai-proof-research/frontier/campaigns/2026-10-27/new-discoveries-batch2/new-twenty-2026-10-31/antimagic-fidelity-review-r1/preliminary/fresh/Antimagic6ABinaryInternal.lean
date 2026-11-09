import Antimagic6APatch
namespace Antimagic.Round6A
open Round4A Round5A

theorem binary_internal_range (n h i : ℕ) (hn : 3 ≤ n)
    (hh : 2 ≤ h) (hhn : h<n) (hi : i<2^h) :
    1 ≤ internalLabel 2 n h i ∧ internalLabel 2 n h i ≤ internalEdges 2 n-1 ∧
    internalLabel 2 n h i ≠ center 2 n := by
  have hc := coordinate_bound 2 n h (patchedIndex 2 h i) hh hhn (patchedIndex_row_bound h i hi)
  have hs := internalEdges_split 2 n (by omega)
  have hz := shell_size 2 n (by decide) hn
  have hZ : center 2 n-1<center 2 n := by simp [center]
  rw [binary_internal_shell n h i (by omega)]
  have hr := shellEntry_range (center 2 n) (center 2 n-1)
    (offset 2 n h+patchedIndex 2 h i) hZ (by omega)
  omega

theorem binary_internal_injective (n h g i j : ℕ) (hn : 3 ≤ n)
    (hh : 1 ≤ h) (hg : 1 ≤ g) (hhn : h<n) (hgn : g<n)
    (hi : i<2^h) (hj : j<2^g)
    (heq : internalLabel 2 n h i=internalLabel 2 n g j) : h=g ∧ i=j := by
  have hc := binary_center n hn
  have hZ : 3 ≤ center 2 n := by have := internalEdges_lower 2 n hn; norm_num only at this; omega
  by_cases h1 : h=1
  · subst h
    by_cases g1 : g=1
    · subst g
      norm_num only at hi hj
      simp only [internalLabel,ite_true] at heq
      split_ifs at heq <;> omega
    · have hr := binary_internal_range n g j hn (by omega) hgn hj
      norm_num only at hi
      rw [show internalLabel 2 n 1 i=(if i=0 then center 2 n else internalEdges 2 n-2+1+i) from rfl] at heq
      split_ifs at heq <;> omega
  · by_cases g1 : g=1
    · subst g
      have hr := binary_internal_range n h i hn (by omega) hhn hi
      norm_num only at hj
      rw [show internalLabel 2 n 1 j=(if j=0 then center 2 n else internalEdges 2 n-2+1+j) from rfl] at heq
      split_ifs at heq <;> omega
    · rw [binary_internal_shell n h i h1,binary_internal_shell n g j g1] at heq
      have hpi := patchedIndex_row_bound h i hi
      have hpj := patchedIndex_row_bound g j hj
      have hci := coordinate_bound 2 n h _ (by omega) hhn hpi
      have hcj := coordinate_bound 2 n g _ (by omega) hgn hpj
      have hs := internalEdges_split 2 n (by omega)
      have hz := shell_size 2 n (by decide) hn
      have hr := shellEntry_injective (center 2 n) (center 2 n-1) (by omega)
        (a₁ := ⟨offset 2 n h+patchedIndex 2 h i,by omega⟩)
        (a₂ := ⟨offset 2 n g+patchedIndex 2 g j,by omega⟩) heq
      have he := shell_coordinate_injective 2 n h g _ _ (by omega) (by omega) hhn hgn hpi hpj
        (congrArg Fin.val hr)
      refine ⟨he.1,?_⟩
      have hpatch : patchedIndex 2 h i=patchedIndex 2 h j := by simpa only [he.1] using he.2
      exact patchedIndex_row_injective h hpatch

theorem binary_internal_exists (n x : ℕ) (hn : 3 ≤ n)
    (hx : 1 ≤ x ∧ x ≤ internalEdges 2 n) :
    ∃ h i, 1 ≤ h ∧ h<n ∧ i<2^h ∧ internalLabel 2 n h i=x := by
  have hc := binary_center n hn
  have hZ : 3 ≤ center 2 n := by have := internalEdges_lower 2 n hn; norm_num only at this; omega
  by_cases hxZ : x=center 2 n
  · exact ⟨1,0,by omega,by omega,by decide,by simp [internalLabel,hxZ]⟩
  by_cases hxN : x=internalEdges 2 n
  · refine ⟨1,1,by omega,by omega,by decide,?_⟩
    simp only [internalLabel,ite_true,Nat.one_ne_zero,ite_false]
    omega
  · obtain ⟨r,hr,_⟩ := shellEntry_unique (center 2 n) (center 2 n-1) x (by omega) (by omega)
    have hs := internalEdges_split 2 n (by omega)
    have hz := shell_size 2 n (by decide) hn
    obtain ⟨h,i,hh,hhn,hi,he⟩ := shell_coordinate_exists 2 n 1 r.val (by omega) (by have := r.isLt; omega)
    refine ⟨h,patchedIndex 2 h i,by omega,hhn,patchedIndex_row_bound h i hi,?_⟩
    rw [binary_internal_shell n h _ (by omega),patchedIndex_row_involutive,he]
    exact hr

#print axioms binary_internal_injective
#print axioms binary_internal_exists
end Antimagic.Round6A
