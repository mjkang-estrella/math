module
public import GridFiniteCodes
@[expose] public section
set_option linter.unusedSimpArgs false
namespace Grid343536
open Finset
theorem equitable_degree {V : Type*} [Fintype V] (F : SimpleGraph V)
    [DecidableRel F.Adj] (r : Setoid V) (hr : IsEquitable F r) {u v : V}
    (h : r u v) :
    (univ.filter (F.Adj u)).card = (univ.filter (F.Adj v)).card := by
  have := congrArg Multiset.card ((equitable_iff_neighborCells F r).mp hr u v h)
  simp only [neighborCells, Multiset.card_map, Finset.card_val] at this
  convert this using 1 <;> apply congrArg Finset.card <;> ext x <;> simp only [mem_filter, mem_univ, true_and]

def corner3 : Fin 4 → Fin 3 × Fin 3 := ![(0,0),(0,2),(2,0),(2,2)]
def edge3 : Fin 4 → Fin 3 × Fin 3 := ![(0,1),(1,0),(1,2),(2,1)]
def loc3 (x : Fin 3 × Fin 3) : Fin 3 × Fin 4 :=
  (![![(0,0),(1,0),(0,1)], ![(1,1),(2,0),(1,2)], ![(0,2),(1,3),(0,3)]]
    : Fin 3 → Fin 3 → Fin 3 × Fin 4) x.1 x.2
def code3 (a b : Fin 15) (x : Fin 3 × Fin 3) : ℕ × ℕ :=
  let z := loc3 x
  (z.1.val, if z.1 = 0 then codes4 a z.2 else if z.1 = 1 then codes4 b z.2 else 0)
def block3 (a b : Fin 15) : Setoid (Fin 3 × Fin 3) := Setoid.ker (code3 a b)

theorem degree3 (x : Fin 3 × Fin 3) :
    (univ.filter ((G 3 3).Adj x)).card = (loc3 x).1.val + 2 := by
  obtain ⟨i,j⟩ := x
  fin_cases i <;> fin_cases j <;> decide

theorem equitable3_complete (r : Setoid (Fin 3 × Fin 3)) (hr : IsEquitable (G 3 3) r) :
    ∃ a b, r = block3 a b := by
  obtain ⟨a, ha⟩ := setoid4_complete (Setoid.comap corner3 r)
  obtain ⟨b, hb⟩ := setoid4_complete (Setoid.comap edge3 r)
  have hc : ∀ i j, r (corner3 i) (corner3 j) ↔ codes4 a i = codes4 a j := by
    intro i j
    exact Iff.of_eq (congrArg (fun s : Setoid (Fin 4) => s i j) ha)
  have he : ∀ i j, r (edge3 i) (edge3 j) ↔ codes4 b i = codes4 b j := by
    intro i j
    exact Iff.of_eq (congrArg (fun s : Setoid (Fin 4) => s i j) hb)
  have hd : ∀ u v, r u v → (loc3 u).1 = (loc3 v).1 := by
    intro u v h
    apply Fin.ext
    have h := equitable_degree (G 3 3) r hr h
    rw [degree3, degree3] at h
    omega
  refine ⟨a,b, ?_⟩
  ext u v
  obtain ⟨i,j⟩ := u
  obtain ⟨k,l⟩ := v
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
  · change r (0,0) (0,0) ↔ ((0, codes4 a 0) : ℕ × ℕ) = (0, codes4 a 0)
    exact (hc 0 0).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,0)).1 = (loc3 (0,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,0) = code3 a b (0,1) at h
      exact False.elim ((by decide : ¬ (loc3 (0,0)).1.val = (loc3 (0,1)).1.val) (congrArg Prod.fst h))
  · change r (0,0) (0,2) ↔ ((0, codes4 a 0) : ℕ × ℕ) = (0, codes4 a 1)
    exact (hc 0 1).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,0)).1 = (loc3 (1,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,0) = code3 a b (1,0) at h
      exact False.elim ((by decide : ¬ (loc3 (0,0)).1.val = (loc3 (1,0)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,0)).1 = (loc3 (1,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,0) = code3 a b (1,1) at h
      exact False.elim ((by decide : ¬ (loc3 (0,0)).1.val = (loc3 (1,1)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,0)).1 = (loc3 (1,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,0) = code3 a b (1,2) at h
      exact False.elim ((by decide : ¬ (loc3 (0,0)).1.val = (loc3 (1,2)).1.val) (congrArg Prod.fst h))
  · change r (0,0) (2,0) ↔ ((0, codes4 a 0) : ℕ × ℕ) = (0, codes4 a 2)
    exact (hc 0 2).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,0)).1 = (loc3 (2,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,0) = code3 a b (2,1) at h
      exact False.elim ((by decide : ¬ (loc3 (0,0)).1.val = (loc3 (2,1)).1.val) (congrArg Prod.fst h))
  · change r (0,0) (2,2) ↔ ((0, codes4 a 0) : ℕ × ℕ) = (0, codes4 a 3)
    exact (hc 0 3).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,1)).1 = (loc3 (0,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,1) = code3 a b (0,0) at h
      exact False.elim ((by decide : ¬ (loc3 (0,1)).1.val = (loc3 (0,0)).1.val) (congrArg Prod.fst h))
  · change r (0,1) (0,1) ↔ ((1, codes4 b 0) : ℕ × ℕ) = (1, codes4 b 0)
    exact (he 0 0).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,1)).1 = (loc3 (0,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,1) = code3 a b (0,2) at h
      exact False.elim ((by decide : ¬ (loc3 (0,1)).1.val = (loc3 (0,2)).1.val) (congrArg Prod.fst h))
  · change r (0,1) (1,0) ↔ ((1, codes4 b 0) : ℕ × ℕ) = (1, codes4 b 1)
    exact (he 0 1).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,1)).1 = (loc3 (1,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,1) = code3 a b (1,1) at h
      exact False.elim ((by decide : ¬ (loc3 (0,1)).1.val = (loc3 (1,1)).1.val) (congrArg Prod.fst h))
  · change r (0,1) (1,2) ↔ ((1, codes4 b 0) : ℕ × ℕ) = (1, codes4 b 2)
    exact (he 0 2).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,1)).1 = (loc3 (2,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,1) = code3 a b (2,0) at h
      exact False.elim ((by decide : ¬ (loc3 (0,1)).1.val = (loc3 (2,0)).1.val) (congrArg Prod.fst h))
  · change r (0,1) (2,1) ↔ ((1, codes4 b 0) : ℕ × ℕ) = (1, codes4 b 3)
    exact (he 0 3).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,1)).1 = (loc3 (2,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,1) = code3 a b (2,2) at h
      exact False.elim ((by decide : ¬ (loc3 (0,1)).1.val = (loc3 (2,2)).1.val) (congrArg Prod.fst h))
  · change r (0,2) (0,0) ↔ ((0, codes4 a 1) : ℕ × ℕ) = (0, codes4 a 0)
    exact (hc 1 0).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,2)).1 = (loc3 (0,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,2) = code3 a b (0,1) at h
      exact False.elim ((by decide : ¬ (loc3 (0,2)).1.val = (loc3 (0,1)).1.val) (congrArg Prod.fst h))
  · change r (0,2) (0,2) ↔ ((0, codes4 a 1) : ℕ × ℕ) = (0, codes4 a 1)
    exact (hc 1 1).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,2)).1 = (loc3 (1,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,2) = code3 a b (1,0) at h
      exact False.elim ((by decide : ¬ (loc3 (0,2)).1.val = (loc3 (1,0)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,2)).1 = (loc3 (1,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,2) = code3 a b (1,1) at h
      exact False.elim ((by decide : ¬ (loc3 (0,2)).1.val = (loc3 (1,1)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,2)).1 = (loc3 (1,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,2) = code3 a b (1,2) at h
      exact False.elim ((by decide : ¬ (loc3 (0,2)).1.val = (loc3 (1,2)).1.val) (congrArg Prod.fst h))
  · change r (0,2) (2,0) ↔ ((0, codes4 a 1) : ℕ × ℕ) = (0, codes4 a 2)
    exact (hc 1 2).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (0,2)).1 = (loc3 (2,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (0,2) = code3 a b (2,1) at h
      exact False.elim ((by decide : ¬ (loc3 (0,2)).1.val = (loc3 (2,1)).1.val) (congrArg Prod.fst h))
  · change r (0,2) (2,2) ↔ ((0, codes4 a 1) : ℕ × ℕ) = (0, codes4 a 3)
    exact (hc 1 3).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,0)).1 = (loc3 (0,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,0) = code3 a b (0,0) at h
      exact False.elim ((by decide : ¬ (loc3 (1,0)).1.val = (loc3 (0,0)).1.val) (congrArg Prod.fst h))
  · change r (1,0) (0,1) ↔ ((1, codes4 b 1) : ℕ × ℕ) = (1, codes4 b 0)
    exact (he 1 0).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,0)).1 = (loc3 (0,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,0) = code3 a b (0,2) at h
      exact False.elim ((by decide : ¬ (loc3 (1,0)).1.val = (loc3 (0,2)).1.val) (congrArg Prod.fst h))
  · change r (1,0) (1,0) ↔ ((1, codes4 b 1) : ℕ × ℕ) = (1, codes4 b 1)
    exact (he 1 1).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,0)).1 = (loc3 (1,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,0) = code3 a b (1,1) at h
      exact False.elim ((by decide : ¬ (loc3 (1,0)).1.val = (loc3 (1,1)).1.val) (congrArg Prod.fst h))
  · change r (1,0) (1,2) ↔ ((1, codes4 b 1) : ℕ × ℕ) = (1, codes4 b 2)
    exact (he 1 2).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,0)).1 = (loc3 (2,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,0) = code3 a b (2,0) at h
      exact False.elim ((by decide : ¬ (loc3 (1,0)).1.val = (loc3 (2,0)).1.val) (congrArg Prod.fst h))
  · change r (1,0) (2,1) ↔ ((1, codes4 b 1) : ℕ × ℕ) = (1, codes4 b 3)
    exact (he 1 3).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,0)).1 = (loc3 (2,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,0) = code3 a b (2,2) at h
      exact False.elim ((by decide : ¬ (loc3 (1,0)).1.val = (loc3 (2,2)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1 = (loc3 (0,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,1) = code3 a b (0,0) at h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1.val = (loc3 (0,0)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1 = (loc3 (0,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,1) = code3 a b (0,1) at h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1.val = (loc3 (0,1)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1 = (loc3 (0,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,1) = code3 a b (0,2) at h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1.val = (loc3 (0,2)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1 = (loc3 (1,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,1) = code3 a b (1,0) at h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1.val = (loc3 (1,0)).1.val) (congrArg Prod.fst h))
  · exact iff_of_true (r.refl _) rfl
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1 = (loc3 (1,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,1) = code3 a b (1,2) at h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1.val = (loc3 (1,2)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1 = (loc3 (2,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,1) = code3 a b (2,0) at h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1.val = (loc3 (2,0)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1 = (loc3 (2,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,1) = code3 a b (2,1) at h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1.val = (loc3 (2,1)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1 = (loc3 (2,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,1) = code3 a b (2,2) at h
      exact False.elim ((by decide : ¬ (loc3 (1,1)).1.val = (loc3 (2,2)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,2)).1 = (loc3 (0,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,2) = code3 a b (0,0) at h
      exact False.elim ((by decide : ¬ (loc3 (1,2)).1.val = (loc3 (0,0)).1.val) (congrArg Prod.fst h))
  · change r (1,2) (0,1) ↔ ((1, codes4 b 2) : ℕ × ℕ) = (1, codes4 b 0)
    exact (he 2 0).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,2)).1 = (loc3 (0,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,2) = code3 a b (0,2) at h
      exact False.elim ((by decide : ¬ (loc3 (1,2)).1.val = (loc3 (0,2)).1.val) (congrArg Prod.fst h))
  · change r (1,2) (1,0) ↔ ((1, codes4 b 2) : ℕ × ℕ) = (1, codes4 b 1)
    exact (he 2 1).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,2)).1 = (loc3 (1,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,2) = code3 a b (1,1) at h
      exact False.elim ((by decide : ¬ (loc3 (1,2)).1.val = (loc3 (1,1)).1.val) (congrArg Prod.fst h))
  · change r (1,2) (1,2) ↔ ((1, codes4 b 2) : ℕ × ℕ) = (1, codes4 b 2)
    exact (he 2 2).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,2)).1 = (loc3 (2,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,2) = code3 a b (2,0) at h
      exact False.elim ((by decide : ¬ (loc3 (1,2)).1.val = (loc3 (2,0)).1.val) (congrArg Prod.fst h))
  · change r (1,2) (2,1) ↔ ((1, codes4 b 2) : ℕ × ℕ) = (1, codes4 b 3)
    exact (he 2 3).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (1,2)).1 = (loc3 (2,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (1,2) = code3 a b (2,2) at h
      exact False.elim ((by decide : ¬ (loc3 (1,2)).1.val = (loc3 (2,2)).1.val) (congrArg Prod.fst h))
  · change r (2,0) (0,0) ↔ ((0, codes4 a 2) : ℕ × ℕ) = (0, codes4 a 0)
    exact (hc 2 0).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,0)).1 = (loc3 (0,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,0) = code3 a b (0,1) at h
      exact False.elim ((by decide : ¬ (loc3 (2,0)).1.val = (loc3 (0,1)).1.val) (congrArg Prod.fst h))
  · change r (2,0) (0,2) ↔ ((0, codes4 a 2) : ℕ × ℕ) = (0, codes4 a 1)
    exact (hc 2 1).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,0)).1 = (loc3 (1,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,0) = code3 a b (1,0) at h
      exact False.elim ((by decide : ¬ (loc3 (2,0)).1.val = (loc3 (1,0)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,0)).1 = (loc3 (1,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,0) = code3 a b (1,1) at h
      exact False.elim ((by decide : ¬ (loc3 (2,0)).1.val = (loc3 (1,1)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,0)).1 = (loc3 (1,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,0) = code3 a b (1,2) at h
      exact False.elim ((by decide : ¬ (loc3 (2,0)).1.val = (loc3 (1,2)).1.val) (congrArg Prod.fst h))
  · change r (2,0) (2,0) ↔ ((0, codes4 a 2) : ℕ × ℕ) = (0, codes4 a 2)
    exact (hc 2 2).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,0)).1 = (loc3 (2,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,0) = code3 a b (2,1) at h
      exact False.elim ((by decide : ¬ (loc3 (2,0)).1.val = (loc3 (2,1)).1.val) (congrArg Prod.fst h))
  · change r (2,0) (2,2) ↔ ((0, codes4 a 2) : ℕ × ℕ) = (0, codes4 a 3)
    exact (hc 2 3).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,1)).1 = (loc3 (0,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,1) = code3 a b (0,0) at h
      exact False.elim ((by decide : ¬ (loc3 (2,1)).1.val = (loc3 (0,0)).1.val) (congrArg Prod.fst h))
  · change r (2,1) (0,1) ↔ ((1, codes4 b 3) : ℕ × ℕ) = (1, codes4 b 0)
    exact (he 3 0).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,1)).1 = (loc3 (0,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,1) = code3 a b (0,2) at h
      exact False.elim ((by decide : ¬ (loc3 (2,1)).1.val = (loc3 (0,2)).1.val) (congrArg Prod.fst h))
  · change r (2,1) (1,0) ↔ ((1, codes4 b 3) : ℕ × ℕ) = (1, codes4 b 1)
    exact (he 3 1).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,1)).1 = (loc3 (1,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,1) = code3 a b (1,1) at h
      exact False.elim ((by decide : ¬ (loc3 (2,1)).1.val = (loc3 (1,1)).1.val) (congrArg Prod.fst h))
  · change r (2,1) (1,2) ↔ ((1, codes4 b 3) : ℕ × ℕ) = (1, codes4 b 2)
    exact (he 3 2).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,1)).1 = (loc3 (2,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,1) = code3 a b (2,0) at h
      exact False.elim ((by decide : ¬ (loc3 (2,1)).1.val = (loc3 (2,0)).1.val) (congrArg Prod.fst h))
  · change r (2,1) (2,1) ↔ ((1, codes4 b 3) : ℕ × ℕ) = (1, codes4 b 3)
    exact (he 3 3).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,1)).1 = (loc3 (2,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,1) = code3 a b (2,2) at h
      exact False.elim ((by decide : ¬ (loc3 (2,1)).1.val = (loc3 (2,2)).1.val) (congrArg Prod.fst h))
  · change r (2,2) (0,0) ↔ ((0, codes4 a 3) : ℕ × ℕ) = (0, codes4 a 0)
    exact (hc 3 0).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,2)).1 = (loc3 (0,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,2) = code3 a b (0,1) at h
      exact False.elim ((by decide : ¬ (loc3 (2,2)).1.val = (loc3 (0,1)).1.val) (congrArg Prod.fst h))
  · change r (2,2) (0,2) ↔ ((0, codes4 a 3) : ℕ × ℕ) = (0, codes4 a 1)
    exact (hc 3 1).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,2)).1 = (loc3 (1,0)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,2) = code3 a b (1,0) at h
      exact False.elim ((by decide : ¬ (loc3 (2,2)).1.val = (loc3 (1,0)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,2)).1 = (loc3 (1,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,2) = code3 a b (1,1) at h
      exact False.elim ((by decide : ¬ (loc3 (2,2)).1.val = (loc3 (1,1)).1.val) (congrArg Prod.fst h))
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,2)).1 = (loc3 (1,2)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,2) = code3 a b (1,2) at h
      exact False.elim ((by decide : ¬ (loc3 (2,2)).1.val = (loc3 (1,2)).1.val) (congrArg Prod.fst h))
  · change r (2,2) (2,0) ↔ ((0, codes4 a 3) : ℕ × ℕ) = (0, codes4 a 2)
    exact (hc 3 2).trans (by simp only [Prod.mk.injEq, true_and])
  · constructor
    · intro h
      exact False.elim ((by decide : ¬ (loc3 (2,2)).1 = (loc3 (2,1)).1) (hd _ _ h))
    · intro h
      change code3 a b (2,2) = code3 a b (2,1) at h
      exact False.elim ((by decide : ¬ (loc3 (2,2)).1.val = (loc3 (2,1)).1.val) (congrArg Prod.fst h))
  · change r (2,2) (2,2) ↔ ((0, codes4 a 3) : ℕ × ℕ) = (0, codes4 a 3)
    exact (hc 3 3).trans (by simp only [Prod.mk.injEq, true_and])
end Grid343536
