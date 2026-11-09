import TransportedNeighbors
namespace Nut8
attribute [local instance] Classical.propDecidable
lemma filter_range_card (n : ℕ) (p : ℕ → Bool) :
    ((List.range n).filter p).length = Fintype.card {i : Fin n // p i.val = true} := by
  rw [Fintype.card_subtype]
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter p), List.toFinset_filter]
  apply Finset.card_bij (fun a ha => (⟨a, List.mem_range.mp (List.mem_toFinset.mp (Finset.mem_filter.mp ha).1)⟩ : Fin n))
  · intro a ha
    simpa using (Finset.mem_filter.mp ha).2
  · intro a ha b hb he
    exact congrArg Fin.val he
  · intro b hb
    refine ⟨b.val, ?_, ?_⟩
    · simp only [Finset.mem_filter, List.mem_toFinset, List.mem_range]
      exact ⟨b.isLt, by simpa using hb⟩
    · rfl

lemma graphDegree_eq_delete {n a : ℕ} (G : SimpleGraph (Fin (n+1)))
    (v : Fin (n+1)) (e : Equiv.Perm (Fin n))
    (ha : ∀ i j : Fin n, G.Adj (v.succAbove (e i)) (v.succAbove (e j)) ↔
      graphBit n a i.val j.val = true) (i : Fin n) :
    graphDegree n a i.val = (deleteFin G v).degree (e i) := by
  rw [graphDegree, filter_range_card, ← SimpleGraph.card_neighborSet_eq_degree]
  let f : {j : Fin n // graphBit n a i.val j.val = true} →
      (deleteFin G v).neighborSet (e i) := fun j => ⟨e j.val, (ha i j.val).mpr j.property⟩
  apply Fintype.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro x y he
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val he)
  · intro j
    refine ⟨⟨e.symm j.val, ?_⟩, ?_⟩
    · exact (ha i _).mp (by simpa only [Equiv.apply_symm_apply, SimpleGraph.mem_neighborSet, deleteFin, SimpleGraph.comap_adj] using j.property)
    · apply Subtype.ext
      exact e.apply_symm_apply _

lemma mask_length_eq_degree {n : ℕ} (G : SimpleGraph (Fin (n+1)))
    (v : Fin (n+1)) (e : Equiv.Perm (Fin n)) :
    ((List.range n).filter (fun i => (transportedMask G v e).testBit i)).length = G.degree v := by
  rw [filter_range_card, ← SimpleGraph.card_neighborSet_eq_degree]
  let f : {i : Fin n // (transportedMask G v e).testBit i.val = true} → G.neighborSet v :=
    fun i => ⟨v.succAbove (e i.val), (transportedMask_bit G v e i.val).mp i.property⟩
  apply Fintype.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro x y he
    apply Subtype.ext
    exact e.injective (v.succAbove_right_injective (congrArg Subtype.val he))
  · intro j
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (G.ne_of_adj j.property).symm
    refine ⟨⟨e.symm k, ?_⟩, ?_⟩
    · apply (transportedMask_bit G v e _).mpr
      simpa only [Equiv.apply_symm_apply, hk, SimpleGraph.mem_neighborSet] using j.property
    · apply Subtype.ext
      simpa only [f, Equiv.apply_symm_apply] using hk

lemma deleteFin_degree_lt {n : ℕ} (G : SimpleGraph (Fin (n+1)))
    (v : Fin (n+1)) (i : Fin n) (hi : G.Adj v (v.succAbove i)) :
    (deleteFin G v).degree i < G.degree (v.succAbove i) := by
  let f : (deleteFin G v).neighborSet i → G.neighborSet (v.succAbove i) :=
    fun j => ⟨v.succAbove j.val, j.property⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact v.succAbove_right_injective (congrArg Subtype.val he)
  have hn : ¬ Function.Surjective f := by
    intro hs
    obtain ⟨j, hj⟩ := hs ⟨v, hi.symm⟩
    exact Fin.succAbove_ne v j.val (congrArg Subtype.val hj)
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_lt_of_injective_not_surjective f hf hn
theorem transportedMask_eligible {n a : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin (n+1))) (hc : G.Connected) (hd : ∀ i, G.degree i ≤ 3)
    (v : Fin (n+1)) (e : Equiv.Perm (Fin n))
    (ha : ∀ i j : Fin n, G.Adj (v.succAbove (e i)) (v.succAbove (e j)) ↔
      graphBit n a i.val j.val = true) :
    eligibleNeighbors n a (transportedMask G v e) = true := by
  have : Nontrivial (Fin (n+1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hp := hc.preconnected.degree_pos_of_nontrivial v
  simp only [eligibleNeighbors, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨?_, ?_⟩
  · rw [mask_length_eq_degree]
    exact ⟨hp, hd v⟩
  · intro i hi
    obtain ⟨hir, hib⟩ := List.mem_filter.mp hi
    have hilt := List.mem_range.mp hir
    rw [graphDegree_eq_delete G v e ha ⟨i, hilt⟩]
    exact lt_of_lt_of_le (deleteFin_degree_lt G v (e ⟨i, hilt⟩)
      ((transportedMask_bit G v e ⟨i, hilt⟩).mp hib)) (hd _)
end Nut8
