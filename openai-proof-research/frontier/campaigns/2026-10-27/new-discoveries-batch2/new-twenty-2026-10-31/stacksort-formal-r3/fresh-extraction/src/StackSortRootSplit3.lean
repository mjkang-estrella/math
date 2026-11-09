import StackSortShuffle3Root
noncomputable section
open BigOperators
namespace StackSort.Shuffle3
 theorem rootPair_left_length {n i : ℕ} {p} (hp : p ∈ shuffleDomain n i) :
    ((rootPair n p).1.takeWhile (· != n)).length = i := by
  have hA := Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hp).1
  have hL := (Finset.mem_product.mp (Finset.mem_filter.mp
    (Finset.mem_product.mp (Finset.mem_sigma.mp hp).2).1).1).1
  rw [rootPair, rootGlue_take n _ _ (labelWords_below hA.1 hL)]
  exact (mem_labelWords.mp hL).length_eq.trans ((Finset.length_sort _).trans hA.2)

 def interior (n : ℕ) : Finset (List ℕ × List ℕ) :=
  (Finset.Icc 1 (n-1)).biUnion fun i => (shuffleDomain n i).image (rootPair n)

 theorem interior_card (n : ℕ) : (interior n).card =
    ∑ i ∈ Finset.Icc 1 (n-1), Nat.choose n i * P i * P (n-i) := by
  rw [interior, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_image_of_injOn (rootPair_injOn n i), shuffleDomain_card]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hq
    have h := congrArg (fun p : List ℕ × List ℕ => (p.1.takeWhile (· != n)).length) he
    rw [rootPair_left_length hv, rootPair_left_length hu] at h
    exact hij h.symm

 def endDomain (n : ℕ) := (Finset.univ : Finset (Bool × Bool)) ×ˢ
    ((words n ×ˢ words n).filter (fun p => s p.1 = s p.2))
 def endPair (n : ℕ) (p : (Bool × Bool) × (List ℕ × List ℕ)) :=
    (endInsert n p.1.1 p.2.1, endInsert n p.1.2 p.2.2)
 def ends (n : ℕ) := (endDomain n).image (endPair n)
 theorem ends_card (n : ℕ) (hn : 0 < n) : (ends n).card = 4 * P n := by
  rw [ends, Finset.card_image_of_injOn]
  · simp [endDomain,Finset.card_product,P]
  · intro p hp q hq he
    have hpw := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).1
    have hqw := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).1
    have h1 := endInsert_injective hn hpw.1 hqw.1 (congrArg Prod.fst he)
    have h2 := endInsert_injective hn hpw.2 hqw.2 (congrArg Prod.snd he)
    exact Prod.ext (Prod.ext h1.1 h2.1) (Prod.ext h1.2 h2.2)

 theorem end_left_length {n : ℕ} {w : List ℕ} (hw : w ∈ words n) (b : Bool) :
    ((endInsert n b w).takeWhile (· != n)).length = if b then 0 else n := by
  have hb : ∀ x ∈ w, x < n := fun x hx =>
    List.mem_range.mp ((mem_words.mp hw).mem_iff.mp hx)
  cases b with
  | false =>
    have h := rootGlue_take n w [] hb
    simpa [endInsert,rootGlue] using congrArg List.length h |>.trans (mem_words.mp hw).length_eq
  | true => simp [endInsert]

 theorem interior_disjoint_ends (n : ℕ) : Disjoint (interior n) (ends n) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨i,hi,u,hu,rfl⟩ := (by simpa [interior] using hp :
    ∃ i ∈ Finset.Icc 1 (n-1), ∃ u ∈ shuffleDomain n i, rootPair n u = p)
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hq
  have hw := (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hv).2).1).1
  have h := congrArg (fun p : List ℕ × List ℕ => (p.1.takeWhile (· != n)).length) he
  change ((endInsert n v.1.1 v.2.1).takeWhile (· != n)).length = _ at h
  rw [end_left_length hw, rootPair_left_length hu] at h
  have hi := Finset.mem_Icc.mp hi
  split_ifs at h <;> omega

 theorem root_sum_bound (n : ℕ) (hn : 0 < n) :
    4 * P n + ∑ i ∈ Finset.Icc 1 (n-1), Nat.choose n i * P i * P (n-i) ≤ P (n+1) := by
  rw [← ends_card n hn, ← interior_card, Nat.add_comm, ← Finset.card_union_of_disjoint (interior_disjoint_ends n)]
  apply Finset.card_le_card
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨i,_,u,hu,rfl⟩ := (by simpa [interior] using hp :
      ∃ i ∈ Finset.Icc 1 (n-1), ∃ u ∈ shuffleDomain n i, rootPair n u = p)
    exact rootPair_mem hu
  · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
    have hw := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hu).2).1
    have hs := (Finset.mem_filter.mp (Finset.mem_product.mp hu).2).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨endInsert_mem hw.1 _,endInsert_mem hw.2 _⟩, by
        dsimp [endPair]; rw [endInsert_sort hw.1,endInsert_sort hw.2,hs]⟩
end StackSort.Shuffle3
namespace StackSort.Round3
 theorem rootSplit_proved : StackSort.RootSplit := by
  intro n hn
  have h := Shuffle3.root_sum_bound (n-1) (by omega)
  have he : n-1+1 = n := by omega
  have he' : n-1-1 = n-2 := by omega
  simpa only [he, he'] using h
end StackSort.Round3
