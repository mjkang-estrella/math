from pathlib import Path
D=Path(__file__).resolve().parents[1];p=D/'lean/SimplicialCandidate.lean';s=p.read_text();a=s.index('-- Diagnostic finite');b=s.index('/-- An abstract',a)
s=s[:a]+'''def parentRidge (i : Fin 9) : Finset ℕ :=
 match i.val with
 | 0 | 1 => {1,2,3}
 | 2 => {1,3,5}
 | 3 => {1,5,6}
 | 4 => {1,4,5}
 | 5 => {1,4,7}
 | 6 => {0,4,7}
 | _ => ∅

theorem parent_card : ∀ i : Fin 9, (parentRidge i).card ≤ 3 := by decide

theorem intersections : ∀ i j : Fin 9, i < j →
 (facet i ∩ facet j).card ≤ 2 ∨ facet i ∩ facet j = parentRidge i := by decide

theorem ridge_parent (i j : Fin 9) (hij : i < j) (a : Finset ℕ)
 (ha : a ∈ (facet i).powersetCard 3) (hj : a ⊆ facet j) : a = parentRidge i := by
 rw [Finset.mem_powersetCard] at ha
 have hsub : a ⊆ facet i ∩ facet j := Finset.subset_inter ha.1 hj
 rcases intersections i j hij with hsmall | heq
 · have hcard := Finset.card_le_card hsub
   omega
 · rw [heq] at hsub
   exact Finset.eq_of_subset_of_card_le hsub (by simpa [ha.2] using parent_card i)

theorem laterRidgeUnique : LaterRidgeUnique := by
 intro i j k hij hik a ha b hb haj hbk
 exact (ridge_parent i j hij a ha haj).trans (ridge_parent i k hik b hb hbk).symm

'''+s[b:]
s=s.replace('theorem step_side : ∀ a b : Ridge, step a b → side a = side b := by decide','''theorem facet_side : ∀ i : Fin 9, ∀ a ∈ (facet i).powersetCard 3,
 decide ((a ∩ Finset.range 8).Nonempty) = decide (i.val < 8) := by decide

theorem step_side : ∀ a b : Ridge, step a b → side a = side b := by
 intro a b ⟨i, ha, hb⟩
 have hac : a.val.card = 3 := (Finset.mem_filter.mp a.property).2
 have hbc : b.val.card = 3 := (Finset.mem_filter.mp b.property).2
 exact (facet_side i a.val (by simpa only [Finset.mem_powersetCard] using And.intro ha hac)).trans
  (facet_side i b.val (by simpa only [Finset.mem_powersetCard] using And.intro hb hbc)).symm''')
p.write_text(s)
