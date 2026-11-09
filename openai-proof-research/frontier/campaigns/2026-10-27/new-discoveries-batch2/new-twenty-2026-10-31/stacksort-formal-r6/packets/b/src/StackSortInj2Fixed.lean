import StackSortInj2Ends
namespace StackSort
/-- A fixed choice of complementary label sets. -/
def shiftLabels (a : ℕ) : ℕ ↪o ℕ := OrderEmbedding.ofStrictMono (a + ·) (by intro x y h; change a+x<a+y; omega)

theorem fixed_root_mem {a b : ℕ} {L R : List ℕ}
    (hL : L ∈ words a) (hR : R ∈ words b) :
    rootGlue (a+b) (L, R.map (shiftLabels a)) ∈ words (a+b+1) := by
  apply mem_words.mpr
  unfold rootGlue
  rw [List.range_succ, List.range_add]
  have hp : (L ++ R.map (shiftLabels a)).Perm
      (List.range a ++ (List.range b).map (a+·)) :=
    (mem_words.mp hL).append ((mem_words.mp hR).map (a+·))
  have hr : (L ++ (a+b) :: R.map (shiftLabels a)).Perm ((L ++ R.map (shiftLabels a)) ++ [a+b]) := by
    simpa [List.append_assoc] using
    (List.Perm.refl L).append (List.perm_append_comm (l₁ := [a+b]) (l₂ := R.map (shiftLabels a)))
  exact hr.trans (hp.append_right [a+b])

/-- The source injection for a fixed label subset. The choose factor still needs the
    disjoint union over all subsets; it is not asserted here. -/
theorem fixed_split_bound (a b : ℕ) : P a * P b ≤ P (a+b+1) := by
  let pa := ((words a ×ˢ words a).filter (fun p => s p.1 = s p.2))
  let pb := ((words b ×ˢ words b).filter (fun p => s p.1 = s p.2))
  let f := fun p : (List ℕ × List ℕ) × (List ℕ × List ℕ) =>
    (rootGlue (a+b) (p.1.1, p.2.1.map (shiftLabels a)),
     rootGlue (a+b) (p.1.2, p.2.2.map (shiftLabels a)))
  have hb : (pa ×ˢ pb).card ≤ P (a+b+1) := by
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
      obtain ⟨hw1,hs1⟩ := Finset.mem_filter.mp hp1
      obtain ⟨hw2,hs2⟩ := Finset.mem_filter.mp hp2
      obtain ⟨hL,hL'⟩ := Finset.mem_product.mp hw1
      obtain ⟨hR,hR'⟩ := Finset.mem_product.mp hw2
      have leftBound : ∀ w ∈ words a, ∀ x ∈ w, x < a+b := by
        intro w hw x hx
        have := List.mem_range.mp ((mem_words.mp hw).mem_iff.mp hx)
        omega
      have rightBound : ∀ w ∈ words b, ∀ x ∈ w.map (shiftLabels a), x ≤ a+b := by
        intro w hw x hx
        obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
        have := List.mem_range.mp ((mem_words.mp hw).mem_iff.mp hy)
        change a+y ≤ a+b
        omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨fixed_root_mem hL hR, fixed_root_mem hL' hR'⟩, ?_⟩
      dsimp [f, rootGlue]
      rw [s_split _ _ _ (leftBound _ hL) (rightBound _ hR),
        s_split _ _ _ (leftBound _ hL') (rightBound _ hR'),
        s_map_orderEmbedding, s_map_orderEmbedding, hs1, hs2]
    · intro p hp q hq he
      obtain ⟨hp1,_⟩ := Finset.mem_product.mp hp
      obtain ⟨hq1,_⟩ := Finset.mem_product.mp hq
      have hpw := Finset.mem_product.mp (Finset.mem_filter.mp hp1).1
      have hqw := Finset.mem_product.mp (Finset.mem_filter.mp hq1).1
      have bound : ∀ w ∈ words a, ∀ x ∈ w, x < a+b := by
        intro w hw x hx
        have := List.mem_range.mp ((mem_words.mp hw).mem_iff.mp hx)
        omega
      have h1 := rootGlue_injective (a+b) (bound _ hpw.1) (bound _ hqw.1) (congrArg Prod.fst he)
      have h2 := rootGlue_injective (a+b) (bound _ hpw.2) (bound _ hqw.2) (congrArg Prod.snd he)
      exact Prod.ext (Prod.ext h1.1 h2.1)
        (Prod.ext ((List.map_inj_right (shiftLabels a).injective).mp h1.2)
          ((List.map_inj_right (shiftLabels a).injective).mp h2.2))
  simpa [Finset.card_product, pa, pb, P] using hb
end StackSort
