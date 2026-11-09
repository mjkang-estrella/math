import StackSortSeeds3

namespace StackSort.Round4
open Seeds2

def NonemptyWords (F : List (List ℕ)) : Prop := ∀ w ∈ F, w ≠ []

theorem output_length (F : List (List ℕ)) : (output F).length = F.flatten.length :=
  (output_perm F).length_eq

theorem output_length_pos {F : List (List ℕ)} (hF : NonemptyWords F) (hne : F ≠ []) :
    0 < (output F).length := by
  cases F with
  | nil => exact False.elim (hne rfl)
  | cons w F =>
    have hw := List.length_pos_iff.mpr (hF w (by simp))
    simp only [output_length, List.flatten_cons, List.length_append]
    omega

theorem output_eq_nil_iff {F : List (List ℕ)} (hF : NonemptyWords F) :
    output F = [] ↔ F = [] := by
  constructor
  · intro h
    by_contra hn
    have := output_length_pos hF hn
    simp [h] at this
  · rintro rfl; rfl

theorem nonemptyWords_append {A B : List (List ℕ)} :
    NonemptyWords (A ++ B) ↔ NonemptyWords A ∧ NonemptyWords B := by
  simp [NonemptyWords, List.mem_append, or_imp, forall_and]

/-- A tuple boundary determines its prefix and suffix uniquely when words are nonempty. -/
theorem split_unique {A B C D : List (List ℕ)}
    (hn : NonemptyWords (A ++ B)) (he : A ++ B = C ++ D)
    (hl : (output A).length = (output C).length) : A = C ∧ B = D := by
  rcases List.append_eq_append_iff.mp he with ⟨E,hC,hB⟩ | ⟨E,hA,hD⟩
  · have hE : NonemptyWords E := by
      have : NonemptyWords (C ++ D) := he ▸ hn
      rw [hC] at this
      exact (nonemptyWords_append.mp (nonemptyWords_append.mp this).1).2
    have hz : (output E).length = 0 := by rw [hC, output_append, List.length_append] at hl; omega
    have hnil : E = [] := (output_eq_nil_iff hE).mp (List.length_eq_zero_iff.mp hz)
    simpa [hnil] using And.intro hC.symm hB
  · have hE : NonemptyWords E := by
      rw [hA] at hn
      exact (nonemptyWords_append.mp (nonemptyWords_append.mp hn).1).2
    have hz : (output E).length = 0 := by rw [hA, output_append, List.length_append] at hl; omega
    have hnil : E = [] := (output_eq_nil_iff hE).mp (List.length_eq_zero_iff.mp hz)
    simpa [hnil] using And.intro hA hD.symm

theorem boundary_append_right {A B : List (List ℕ)} {k : ℕ} (hk : Boundary B k) :
    Boundary (A ++ B) ((output A).length + k) := by
  obtain ⟨U,V,rfl,hk⟩ := hk
  exact ⟨A ++ U,V,by simp [List.append_assoc], by simp [output_append,hk]⟩

theorem boundary_le_length {F : List (List ℕ)} {k : ℕ} (h : Boundary F k) :
    k ≤ (output F).length := by
  obtain ⟨A,B,rfl,rfl⟩ := h
  simp [output_append]

/-- Boundaries strictly beyond a concatenation point are boundaries of its suffix. -/
theorem boundary_suffix {A B : List (List ℕ)} {k : ℕ}
    (h : Boundary (A ++ B) k) (hlt : (output A).length < k) :
    Boundary B (k - (output A).length) := by
  obtain ⟨C,D,he,hk⟩ := h
  rcases List.append_eq_append_iff.mp he with ⟨E,hC,hB⟩ | ⟨E,hA,hD⟩
  · refine ⟨E,D,hB,?_⟩
    rw [hC, output_append, List.length_append] at hk
    omega
  · rw [hA, output_append, List.length_append] at hlt
    omega

/-- A last proper common boundary exists, allowing the exterior boundary zero. -/
theorem exists_last_common_cut (F G : List (List ℕ)) (hpos : 0 < (output F).length) :
    ∃ k, k < (output F).length ∧ Boundary F k ∧ Boundary G k ∧
      ∀ j, j < (output F).length → Boundary F j → Boundary G j → j ≤ k := by
  classical
  let C := (Finset.range (output F).length).filter (fun k => Boundary F k ∧ Boundary G k)
  have hz : 0 ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_range]
    exact ⟨hpos, ⟨[],F,by simp, rfl⟩, ⟨[],G,by simp,rfl⟩⟩
  have hn : C.Nonempty := ⟨0,hz⟩
  have hm := Finset.mem_filter.mp (Finset.max'_mem C hn)
  exact ⟨C.max' hn, Finset.mem_range.mp hm.1, hm.2.1, hm.2.2,
    fun j hj hF hG => Finset.le_max' C j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hF,hG⟩)⟩

/-- Splitting a collision at a common output position gives two collisions. -/
theorem collision_split {A B C D : List (List ℕ)}
    (he : output (A ++ B) = output (C ++ D))
    (hl : (output A).length = (output C).length) :
    output A = output C ∧ output B = output D := by
  rw [output_append, output_append] at he
  exact List.append_eq_append_iff_of_size_eq_left hl |>.mp he

/-- The suffix at the last proper common cut is irreducible. -/
theorem last_cut_irreducible {F G A B C D : List (List ℕ)} {k : ℕ}
    (hF : F = A ++ B) (hG : G = C ++ D)
    (hA : (output A).length = k) (hC : (output C).length = k)
    (hmax : ∀ j, j < (output F).length → Boundary F j → Boundary G j → j ≤ k) :
    Irreducible B D := by
  intro j hjB hjD hj0 hjlen
  have hbF : Boundary F (k+j) := by simpa [hF,hA] using (boundary_append_right (A := A) hjB)
  have hbG : Boundary G (k+j) := by simpa [hG,hC] using (boundary_append_right (A := C) hjD)
  have hlen : k+j < (output F).length := by rw [hF,output_append,List.length_append,hA]; omega
  have := hmax (k+j) hlen hbF hbG
  omega

/-- Every nonempty collision has an irreducible final block after its last common cut. -/
theorem exists_irreducible_suffix {F G : List (List ℕ)}
    (he : output F = output G) (hpos : 0 < (output F).length) :
    ∃ A B C D, F = A ++ B ∧ G = C ++ D ∧
      output A = output C ∧ output B = output D ∧
      0 < (output B).length ∧ Irreducible B D ∧
      ∀ j, j < (output F).length → Boundary F j → Boundary G j →
        j ≤ (output A).length := by
  obtain ⟨k,hk,⟨A,B,hF,hA⟩,⟨C,D,hG,hC⟩,hmax⟩ := exists_last_common_cut F G hpos
  have hc := collision_split (A := A) (B := B) (C := C) (D := D) (by simpa only [hF,hG] using he) (hA.trans hC.symm)
  refine ⟨A,B,C,D,hF,hG,hc.1,hc.2,?_,last_cut_irreducible hF hG hA hC hmax,?_⟩
  · rw [hF,output_append,List.length_append,hA] at hk; omega
  · simpa only [hA] using hmax

/-- An irreducible suffix makes its starting boundary the last proper common cut. -/
theorem irreducible_suffix_is_last {F G A B C D : List (List ℕ)}
    (hF : F = A ++ B) (hG : G = C ++ D)
    (hl : (output A).length = (output C).length) (hi : Irreducible B D) :
    ∀ j, j < (output F).length → Boundary F j → Boundary G j →
      j ≤ (output A).length := by
  intro j hj hbj hgj
  by_contra hnot
  have hlt : (output A).length < j := by omega
  have hB := boundary_suffix (hF ▸ hbj) hlt
  have hD := boundary_suffix (hG ▸ hgj) (by omega)
  have hsmall : j - (output A).length < (output B).length := by
    rw [hF,output_append,List.length_append] at hj
    omega
  exact hi (j - (output A).length) hB (by simpa only [← hl] using hD) (by omega) hsmall

/-- Uniqueness of the full prefix/final-irreducible-block decomposition. -/
theorem irreducible_suffix_unique {F G A B C D A' B' C' D' : List (List ℕ)}
    (hnF : NonemptyWords F) (hnG : NonemptyWords G)
    (hF : F = A ++ B) (hG : G = C ++ D)
    (hc : output A = output C) (hb : 0 < (output B).length) (hi : Irreducible B D)
    (hF' : F = A' ++ B') (hG' : G = C' ++ D')
    (hc' : output A' = output C') (hb' : 0 < (output B').length) (hi' : Irreducible B' D') :
    A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  have hl := congrArg List.length hc
  have hl' := congrArg List.length hc'
  have hcut : Boundary F (output A).length := ⟨A,B,hF,rfl⟩
  have hgcut : Boundary G (output A).length := ⟨C,D,hG,hl.symm⟩
  have hcut' : Boundary F (output A').length := ⟨A',B',hF',rfl⟩
  have hgcut' : Boundary G (output A').length := ⟨C',D',hG',hl'.symm⟩
  have hlt : (output A).length < (output F).length := by
    rw [hF,output_append,List.length_append]; omega
  have hlt' : (output A').length < (output F).length := by
    rw [hF',output_append,List.length_append]; omega
  have hk := Nat.le_antisymm
    (irreducible_suffix_is_last hF' hG' hl' hi' _ hlt hcut hgcut)
    (irreducible_suffix_is_last hF hG hl hi _ hlt' hcut' hgcut')
  have hAB := split_unique (hF ▸ hnF) (hF.symm.trans hF') hk
  have hCD := split_unique (hG ▸ hnG) (hG.symm.trans hG') (hl.symm.trans (hk.trans hl'))
  exact ⟨hAB.1,hAB.2,hCD.1,hCD.2⟩

/-- Finite-word data of the unique final-block decomposition; all labels are retained. -/
structure FinalBlock (F G : List (List ℕ)) where
  leftPrefix : List (List ℕ)
  leftBlock : List (List ℕ)
  rightPrefix : List (List ℕ)
  rightBlock : List (List ℕ)
  left_eq : F = leftPrefix ++ leftBlock
  right_eq : G = rightPrefix ++ rightBlock
  prefix_collision : output leftPrefix = output rightPrefix
  block_collision : output leftBlock = output rightBlock
  block_pos : 0 < (output leftBlock).length
  block_irreducible : Irreducible leftBlock rightBlock

theorem finalBlock_exists {F G : List (List ℕ)}
    (he : output F = output G) (hpos : 0 < (output F).length) :
    Nonempty (FinalBlock F G) := by
  obtain ⟨A,B,C,D,hF,hG,hc,hb,hpos,hi,_⟩ := exists_irreducible_suffix he hpos
  exact ⟨⟨A,B,C,D,hF,hG,hc,hb,hpos,hi⟩⟩

theorem finalBlock_subsingleton {F G : List (List ℕ)}
    (hnF : NonemptyWords F) (hnG : NonemptyWords G) :
    Subsingleton (FinalBlock F G) := by
  constructor
  intro p q
  have h := irreducible_suffix_unique hnF hnG p.left_eq p.right_eq p.prefix_collision
    p.block_pos p.block_irreducible q.left_eq q.right_eq q.prefix_collision q.block_pos q.block_irreducible
  cases p
  cases q
  simp_all

/-- The full pair is irreducible precisely when the unique remainder is empty. -/
theorem finalBlock_irreducible_iff {F G : List (List ℕ)}
    (hnF : NonemptyWords F) (hnG : NonemptyWords G) (p : FinalBlock F G) :
    Irreducible F G ↔ p.leftPrefix = [] ∧ p.rightPrefix = [] := by
  have hnA := (nonemptyWords_append.mp (p.left_eq ▸ hnF)).1
  have hnC := (nonemptyWords_append.mp (p.right_eq ▸ hnG)).1
  constructor
  · intro hi
    have hlen : (output p.leftPrefix).length < (output F).length := by
      have hp := p.block_pos
      have he := congrArg (fun T => (output T).length) p.left_eq
      simp only [output_append,List.length_append] at he
      omega
    have hz : (output p.leftPrefix).length = 0 := by
      by_contra hn
      exact hi _ ⟨_,_,p.left_eq,rfl⟩
        ⟨_,_,p.right_eq,congrArg List.length p.prefix_collision.symm⟩ (by omega) hlen
    refine ⟨(output_eq_nil_iff hnA).mp (List.length_eq_zero_iff.mp hz),?_⟩
    apply (output_eq_nil_iff hnC).mp
    rw [← p.prefix_collision]
    exact List.length_eq_zero_iff.mp hz
  · rintro ⟨hA,hC⟩
    have hF : F = p.leftBlock := by simpa only [hA,List.nil_append] using p.left_eq
    have hG : G = p.rightBlock := by simpa only [hC,List.nil_append] using p.right_eq
    simpa only [hF,hG] using p.block_irreducible

end StackSort.Round4
