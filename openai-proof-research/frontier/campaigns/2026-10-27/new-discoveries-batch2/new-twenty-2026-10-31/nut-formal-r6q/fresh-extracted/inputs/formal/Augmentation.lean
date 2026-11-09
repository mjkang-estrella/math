import NutInterface
namespace Nut8

/-- The unordered edge is represented by its increasing endpoint pair. -/
def edgeKey (i j : Fin 8) : Fin 8 × Fin 8 := if i < j then (i,j) else (j,i)

def supportEdges (code : Nat) : Finset (Fin 8 × Fin 8) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ graphBit 8 code p.1.val p.2.val = true

/-- A subset specifies which existing edges have multiplicity two. -/
def edgeWeight (code : Nat) (D : Finset (Fin 8 × Fin 8)) (i j : Fin 8) : ℤ :=
  if i = j then 0 else if graphBit 8 code i.val j.val then
    if edgeKey i j ∈ D then 2 else 1 else 0

def offSum (code : Nat) (D : Finset (Fin 8 × Fin 8)) (i : Fin 8) : ℤ :=
  ∑ j, edgeWeight code D i j

def augmentation (code : Nat) (D : Finset (Fin 8 × Fin 8)) : QuotientMatrix :=
  fun i j => if i = j then 3 - offSum code D i else edgeWeight code D i j

/-- All unsigned augmentations, excluding negative or oversized diagonal fills. -/
def unsignedPatterns (code : Nat) : Finset QuotientMatrix :=
  ((supportEdges code).powerset.filter fun D =>
    ∀ i : Fin 8, 1 ≤ offSum code D i ∧ offSum code D i ≤ 3).image (augmentation code)

/-- Recover the doubled-edge subset from an arbitrary structural matrix. -/
def doubledEdges (C : QuotientMatrix) (code : Nat) : Finset (Fin 8 × Fin 8) :=
  (supportEdges code).filter fun p => |C p.1 p.2| = 2

lemma structural_abs_edge (C : QuotientMatrix) (s : ℤ) (h : Structural C s)
    (i j : Fin 8) (hn : C i j ≠ 0) : |C i j| = 1 ∨ |C i j| = 2 := by
  have hb := h.2.2.2.2.1 i j
  have hp : 0 < |C i j| := abs_pos.mpr hn
  omega

lemma structural_abs_diag (C : QuotientMatrix) (s : ℤ) (h : Structural C s)
    (i : Fin 8) : |C i i| = 0 ∨ |C i i| = 1 ∨ |C i i| = 2 := by
  have hb := h.2.2.2.2.1 i i
  have hp := abs_nonneg (C i i)
  omega

lemma structural_diagonal_cases (C : QuotientMatrix) (s : ℤ) (h : Structural C s)
    (i : Fin 8) :
    (C i i = 0 ∧ |C i i| = 0) ∨
    (C i i = s ∧ |C i i| = 1) ∨
    ((C i i = 2 ∨ C i i = -2) ∧ |C i i| = 2) := by
  rcases h.2.2.2.2.2.1 i with hz | hp | hn | hs
  · simp [hz]
  · simp [hp]
  · simp [hn]
  · rcases h.2.1 with hpos | hneg
    · simp [hs, hpos]
    · simp [hs, hneg]

lemma edgeWeight_recover (C : QuotientMatrix) (s : ℤ) (code : Nat)
    (h : Structural C s) (hc : SupportCode C code) (i j : Fin 8) (hne : i ≠ j) :
    edgeWeight code (doubledEdges C code) i j = |C i j| := by
  have hsym := h.2.2.1
  by_cases hn : C i j = 0
  · have hb : graphBit 8 code i.val j.val = false := by
      cases he : graphBit 8 code i.val j.val with
      | false => rfl
      | true => exact False.elim ((hc i j hne).mpr he hn)
    simp [edgeWeight, hne, hb, hn]
  · have hb := (hc i j hne).mp hn
    have hk : edgeKey i j ∈ supportEdges code := by
      by_cases hij : i < j
      · simp [edgeKey, hij, supportEdges, hb]
      · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) hne.symm
        have hn' : C j i ≠ 0 := by rwa [hsym j i]
        have hb' := (hc j i hne.symm).mp hn'
        simp [edgeKey, hij, supportEdges, hji, hb']
    have he : |C (edgeKey i j).1 (edgeKey i j).2| = |C i j| := by
      by_cases hij : i < j <;> simp [edgeKey, hij, hsym j i]
    have hd : edgeKey i j ∈ doubledEdges C code ↔ |C i j| = 2 := by
      simp [doubledEdges, hk, he]
    rcases structural_abs_edge C s h i j hn with hv | hv <;>
      simp [edgeWeight, hne, hb, hd, hv]

lemma offSum_recover (C : QuotientMatrix) (s : ℤ) (code : Nat)
    (h : Structural C s) (hc : SupportCode C code) (i : Fin 8) :
    offSum code (doubledEdges C code) i = 3 - |C i i| := by
  have hr := h.2.2.2.1 i
  have he : offSum code (doubledEdges C code) i =
      ∑ j ∈ Finset.univ.erase i, |C i j| := by
    unfold offSum
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [edgeWeight, ↓reduceIte, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    exact edgeWeight_recover C s code h hc i j (Finset.ne_of_mem_erase hj).symm
  rw [he]
  have hs := Finset.sum_erase_add (s := Finset.univ) (fun j => |C i j|) (Finset.mem_univ i)
  omega

/-- Every structural matrix with the specified support has an enumerated unsigned
pattern. The diagonal fill is forced by the absolute row sum. -/
theorem unsignedPatterns_complete (C : QuotientMatrix) (s : ℤ) (code : Nat)
    (h : Structural C s) (hc : SupportCode C code) :
    unsignedQuotient C ∈ unsignedPatterns code := by
  apply Finset.mem_image.mpr
  refine ⟨doubledEdges C code, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
    intro i
    rw [offSum_recover C s code h hc i]
    have hb := h.2.2.2.2.1 i i
    have hp := abs_nonneg (C i i)
    omega
  · funext i j
    unfold augmentation unsignedQuotient
    split_ifs with hij
    · subst j
      rw [offSum_recover C s code h hc i]
      omega
    · exact edgeWeight_recover C s code h hc i j hij
end Nut8
