import NumberingR5
namespace EdgePattern.TreeModelsR5
open TreeModelsR3 TreeModelsR4
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
universe u
variable {W : Type u} [Fintype W] (T : Rooted W)
@[simp] theorem number_val_0 (B : Branches T) (hT : TreeFamily T 3 2) (z : Fin 2) :
    (number T B hT (Sum.inl z)).val = z.val := by
  rfl
@[simp] theorem number_val_1 (B : Branches T) (hT : TreeFamily T 3 2) (z : Fin 4) :
    (number T B hT (Sum.inr (Sum.inl z))).val = 2 + z.val := by
  rfl
@[simp] theorem number_val_2 (B : Branches T) (hT : TreeFamily T 3 2) (z : (B.leaves T 0)) :
    (number T B hT (.inr (.inr (.inl z)))).val = 6 + (leafNumber T B 0 z).val := by
  change 2 + (4 + ((leafNumber T B 0 z).val)) = _
  omega
@[simp] theorem number_val_3 (B : Branches T) (hT : TreeFamily T 3 2) (z : (B.leaves T 1)) :
    (number T B hT (.inr (.inr (.inr (.inl z))))).val = 6 + (B.leaves T 0).card + (leafNumber T B 1 z).val := by
  change 2 + (4 + ((B.leaves T 0).card + ((leafNumber T B 1 z).val))) = _
  omega
@[simp] theorem number_val_4 (B : Branches T) (hT : TreeFamily T 3 2) (z : (B.leaves T 2)) :
    (number T B hT (.inr (.inr (.inr (.inr (.inl z)))))).val = 6 + (B.leaves T 0).card + (B.leaves T 1).card + (leafNumber T B 2 z).val := by
  change 2 + (4 + ((B.leaves T 0).card + ((B.leaves T 1).card + ((leafNumber T B 2 z).val)))) = _
  omega
@[simp] theorem number_val_5 (B : Branches T) (hT : TreeFamily T 3 2) (z : (B.leaves T 3)) :
    (number T B hT (.inr (.inr (.inr (.inr (.inr z)))))).val = 6 + (B.leaves T 0).card + (B.leaves T 1).card + (B.leaves T 2).card + (leafNumber T B 3 z).val := by
  change 2 + (4 + ((B.leaves T 0).card + ((B.leaves T 1).card + ((B.leaves T 2).card + ((leafNumber T B 3 z).val))))) = _
  omega
theorem forward_slots (B : Branches T) (hT : TreeFamily T 3 2)
    (s t : Slots T B) (h : forward (branchCounts T B hT)
      (number T B hT s) (number T B hT t)) :
    T.graph.Adj (slotValue T B s) (slotValue T B t) := by
  rcases s with s | s | s | s | s | s
  · fin_cases s
    · rcases t with t | t | t | t | t | t
      · fin_cases t
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exact T.root_edge
      · fin_cases t
        ·
          simpa [slotValue, parent] using B.adj T 0
        ·
          simpa [slotValue, parent] using B.adj T 1
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · rcases t with t | t | t | t | t | t
      · fin_cases t
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · fin_cases t
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          simpa [slotValue, parent] using B.adj T 2
        ·
          simpa [slotValue, parent] using B.adj T 3
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
  · fin_cases s
    · rcases t with t | t | t | t | t | t
      · fin_cases t
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · fin_cases t
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exact (mem_children T _ _ _ |>.mp t.property).1
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · rcases t with t | t | t | t | t | t
      · fin_cases t
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · fin_cases t
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exact (mem_children T _ _ _ |>.mp t.property).1
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · rcases t with t | t | t | t | t | t
      · fin_cases t
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · fin_cases t
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exact (mem_children T _ _ _ |>.mp t.property).1
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · rcases t with t | t | t | t | t | t
      · fin_cases t
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · fin_cases t
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
        ·
          exfalso
          simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      · 
        exact (mem_children T _ _ _ |>.mp t.property).1
  · rcases t with t | t | t | t | t | t
    · fin_cases t
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · fin_cases t
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
  · rcases t with t | t | t | t | t | t
    · fin_cases t
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · fin_cases t
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
  · rcases t with t | t | t | t | t | t
    · fin_cases t
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · fin_cases t
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
  · rcases t with t | t | t | t | t | t
    · fin_cases t
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · fin_cases t
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
      ·
        exfalso
        simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
    · 
      exfalso
      simp only [forward] at h; simp only [number_val_0, number_val_1, number_val_2, number_val_3, number_val_4, number_val_5] at h; dsimp [branchCounts] at h; omega
end EdgePattern.TreeModelsR5
