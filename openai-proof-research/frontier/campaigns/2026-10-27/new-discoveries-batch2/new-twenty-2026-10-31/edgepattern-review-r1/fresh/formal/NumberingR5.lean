import CoordinatesR5
namespace EdgePattern.TreeModelsR5
open TreeModelsR3 TreeModelsR4
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000
universe u
variable {W : Type u} [Fintype W] (T : Rooted W)

abbrev Slots (B : Branches T) := Fin 2 ⊕ Fin 4 ⊕
  ((B.leaves T 0) ⊕ (B.leaves T 1) ⊕ (B.leaves T 2) ⊕ (B.leaves T 3))

def slotValue (B : Branches T) : Slots T B → W
  | .inl i => if i.val = 0 then T.left else T.right
  | .inr (.inl i) => B.vertex i
  | .inr (.inr (.inl z)) => z.val
  | .inr (.inr (.inr (.inl z))) => z.val
  | .inr (.inr (.inr (.inr (.inl z)))) => z.val
  | .inr (.inr (.inr (.inr (.inr z)))) => z.val

theorem slotValue_bijective (B : Branches T) (hT : TreeFamily T 3 2) :
    Function.Bijective (slotValue T B) := by
  classical
  constructor
  · intro s t he
    have roots := T.root_edge.ne
    have bn0 := B.ne_left T
    have bn1 := B.ne_right T
    have ln := B.leaf_ne_roots T hT.2
    have lb := B.leaf_ne_branch T hT.2
    have ld := B.leaves_disjoint T hT.2
    rcases s with s | s | s | s | s | s <;>
      rcases t with t | t | t | t | t | t
    all_goals dsimp [slotValue] at he
    all_goals try { fin_cases s <;> fin_cases t <;> simp_all [slotValue] }
    all_goals try { split_ifs at he <;> first | exact (bn0 _ he.symm).elim | exact (bn1 _ he.symm).elim | exact ((ln _ t.property).1 he.symm).elim | exact ((ln _ t.property).2 he.symm).elim }
    all_goals try { split_ifs at he <;> first | exact (bn0 _ he).elim | exact (bn1 _ he).elim | exact ((ln _ s.property).1 he).elim | exact ((ln _ s.property).2 he).elim }
    all_goals try { exact congrArg Sum.inl (Fin.ext (by omega)) }
    all_goals try { simp_all }
    all_goals try { simp only [Sum.inr.injEq, Sum.inl.injEq]; exact B.injective he }
    all_goals try { simp only [Sum.inr.injEq, Sum.inl.injEq]; exact Subtype.ext he }
    all_goals try { exact (bn0 _ he).elim }
    all_goals try { exact (bn0 _ he.symm).elim }
    all_goals try { exact (bn1 _ he).elim }
    all_goals try { exact (bn1 _ he.symm).elim }
    all_goals try { exact ((ln _ s.property).1 he).elim }
    all_goals try { exact ((ln _ s.property).2 he).elim }
    all_goals try { exact ((ln _ t.property).1 he.symm).elim }
    all_goals try { exact ((ln _ t.property).2 he.symm).elim }
    all_goals try { exact (lb _ _ s.property he).elim }
    all_goals try { exact (lb _ _ t.property he.symm).elim }
    all_goals try { exact (Finset.disjoint_left.mp (ld _ _ (by decide)) s.property (he.symm ▸ t.property)).elim }
  · intro z
    rcases B.coverage T hT z with h | h | ⟨i,h⟩ | ⟨i,h⟩
    · exact ⟨.inl 0,by simpa [slotValue] using h.symm⟩
    · exact ⟨.inl 1,by simpa [slotValue] using h.symm⟩
    · exact ⟨.inr (.inl i),h.symm⟩
    · fin_cases i
      · exact ⟨.inr (.inr (.inl ⟨z,h⟩)),rfl⟩
      · exact ⟨.inr (.inr (.inr (.inl ⟨z,h⟩))),rfl⟩
      · exact ⟨.inr (.inr (.inr (.inr (.inl ⟨z,h⟩)))),rfl⟩
      · exact ⟨.inr (.inr (.inr (.inr (.inr ⟨z,h⟩)))),rfl⟩
end EdgePattern.TreeModelsR5

namespace EdgePattern.TreeModelsR5
open TreeModelsR3
universe u
variable {W : Type u} [Fintype W] (T : Rooted W)

noncomputable def branchCounts (B : Branches T) (hT : TreeFamily T 3 2) : Counts :=
  ⟨⟨(B.leaves T 0).card,by have := B.leaves_card_le T hT 0; omega⟩,
   ⟨(B.leaves T 1).card,by have := B.leaves_card_le T hT 1; omega⟩,
   ⟨(B.leaves T 2).card,by have := B.leaves_card_le T hT 2; omega⟩,
   ⟨(B.leaves T 3).card,by have := B.leaves_card_le T hT 3; omega⟩⟩

noncomputable def leafNumber (B : Branches T) (i : Fin 4) :
    (B.leaves T i) ≃ Fin (B.leaves T i).card :=
  Fintype.equivFinOfCardEq (by simp)

noncomputable def number (B : Branches T) (hT : TreeFamily T 3 2) :
    Slots T B ≃ V (branchCounts T B hT) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 2))
    ((Equiv.sumCongr (Equiv.refl (Fin 4))
      ((Equiv.sumCongr (leafNumber T B 0)
        ((Equiv.sumCongr (leafNumber T B 1)
          ((Equiv.sumCongr (leafNumber T B 2) (leafNumber T B 3)).trans
            finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans
      finSumFinEquiv)).trans finSumFinEquiv).trans
    (finCongr (by simp [order,branchCounts]; omega))

noncomputable def vertexEquiv (B : Branches T) (hT : TreeFamily T 3 2) :
    V (branchCounts T B hT) ≃ W :=
  (number T B hT).symm.trans (Equiv.ofBijective (slotValue T B) (slotValue_bijective T B hT))
end EdgePattern.TreeModelsR5
