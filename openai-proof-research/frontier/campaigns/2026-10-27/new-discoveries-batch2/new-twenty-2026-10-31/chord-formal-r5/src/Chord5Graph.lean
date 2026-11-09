import ChordComb4Final
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
namespace Chord.Round5
open SimpleGraph

/-- A shortest odd closed walk has no repeated vertex before its closing step. -/
theorem odd_loop_injective {V : Type*} (G : SimpleGraph V)
    (hex : ∃ u, ∃ w : G.Walk u u, Odd w.length) :
    ∃ u, ∃ w : G.Walk u u, Odd w.length ∧
      Set.InjOn w.getVert {i | i < w.length} := by
  classical
  let P : Nat → Prop := fun k => ∃ u, ∃ w : G.Walk u u, Odd w.length ∧ w.length = k
  have hp : ∃ k, P k := by
    obtain ⟨u,w,hw⟩ := hex
    exact ⟨w.length,u,w,hw,rfl⟩
  obtain ⟨u,w,ho,hw⟩ := Nat.find_spec hp
  have hmin : ∀ v (p : G.Walk v v), Odd p.length → w.length ≤ p.length := by
    intro v p h
    rw [hw]
    exact Nat.find_min' hp ⟨v,p,h,rfl⟩
  refine ⟨u,w,ho,?_⟩
  suffices hh : ∀ i j, i < j → j < w.length → w.getVert i ≠ w.getVert j by
    intro i hi j hj he
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact hh i j h hj he
    · exact hh j i h hi he.symm
  intro i j hij hj he
  let mid := ((w.drop i).take (j-i)).copy rfl (by
    simpa only [Walk.drop_getVert, Nat.add_sub_of_le (Nat.le_of_lt hij)] using he.symm)
  have hm : mid.length = j-i := by
    dsimp [mid]
    simp only [Walk.length_copy, Walk.take_length, Walk.drop_length]
    omega
  let outside := (w.take i).append ((w.drop j).copy he.symm rfl)
  have hout : outside.length = i + (w.length-j) := by simp [outside]; omega
  have heq : w.length = mid.length + outside.length := by omega
  have hmshort : mid.length < w.length := by omega
  have hoshort : outside.length < w.length := by omega
  have hop : Odd mid.length ∨ Odd outside.length := by
    rw [Nat.odd_iff] at ho ⊢
    rw [Nat.odd_iff]
    omega
  rcases hop with hm' | ho'
  · exact (not_le_of_gt hmshort) (hmin _ mid hm')
  · exact (not_le_of_gt hoshort) (hmin _ outside ho')

/-- Use precisely the lower endpoint of each chord as the crossing-graph vertex. -/
abbrev ChordVertex {n} (D : Diagram n) := {a : Fin (2*n) // a < D.partner a}

def crossingGraph {n} (D : Diagram n) : SimpleGraph (ChordVertex D) where
  Adj a b := Crosses D a.val b.val
  symm := ⟨fun _ _ h => Comb4.crosses_symm h⟩
  loopless := ⟨fun a => Comb4.crosses_irrefl D a.val⟩

theorem bipartite_of_colorable {n} (D : Diagram n) (hc : (crossingGraph D).Colorable 2) :
    Bipartite D := by
  classical
  obtain ⟨col⟩ := hc
  let lower : Fin (2*n) → ChordVertex D := fun i =>
    if h : i < D.partner i then ⟨i,h⟩ else
      ⟨D.partner i, by have := D.noFixed i; rw [D.involutive]; exact lt_of_le_of_ne (le_of_not_gt h) this⟩
  have hl : ∀ i, lower (D.partner i) = lower i := by
    intro i
    dsimp [lower]
    by_cases h : i < D.partner i
    · rw [dite_eq_left h, dite_eq_right (by simpa only [D.involutive] using (not_lt_of_gt h))]
      apply Subtype.ext
      exact D.involutive i
    · rw [dite_eq_right h, dite_eq_left (by
        rw [D.involutive]
        exact lt_of_le_of_ne (le_of_not_gt h) (D.noFixed i))]
  let color : Fin (2*n) → Bool := fun i => decide ((col (lower i)).val = 1)
  refine ⟨color, fun i => congrArg (fun a => decide ((col a).val = 1)) (hl i), ?_⟩
  intro a b hab he
  have hec : col (lower a) = col (lower b) := by
    apply Fin.ext
    have ha := (col (lower a)).isLt
    have hb := (col (lower b)).isLt
    change decide ((col (lower a)).val = 1) = decide ((col (lower b)).val = 1) at he
    have hh : ((col (lower a)).val = 1 ↔ (col (lower b)).val = 1) := by simpa only [decide_eq_decide] using he
    omega
  apply col.valid _ hec
  change Crosses D (lower a).val (lower b).val
  simpa only [lower, dite_eq_left hab.1, dite_eq_left hab.2.1] using hab

/-- The full graph-window obligation; extra edges in the window are harmless. -/
theorem oddCycleWindow_proved : Comb4.OddCycleWindow := by
  classical
  intro n D hnb
  have hnc : ¬ (crossingGraph D).Colorable 2 := fun hc => hnb (bipartite_of_colorable D hc)
  have hex : ∃ u, ∃ w : (crossingGraph D).Walk u u, Odd w.length := by
    by_contra h
    apply hnc
    rw [two_colorable_iff_forall_loop_even]
    intro u w
    exact Nat.not_odd_iff_even.mp (fun ho => h ⟨u,w,ho⟩)
  obtain ⟨u,w,ho,hi⟩ := odd_loop_injective (crossingGraph D) hex
  have hpos : 0 < w.length := by rw [Nat.odd_iff] at ho; omega
  have hn1 : w.length ≠ 1 := by
    intro h
    have hh := w.adj_getVert_succ hpos
    have he : w.getVert 1 = u := by rw [← h]; exact w.getVert_length
    rw [w.getVert_zero, he] at hh
    exact (crossingGraph D).loopless.irrefl u hh
  have hthree : 3 ≤ w.length := by
    rw [Nat.odd_iff] at ho
    omega
  by_cases h3 : w.length = 3
  · left
    refine ⟨(w.getVert 0).val, (w.getVert 1).val, (w.getVert 2).val,
      w.adj_getVert_succ (by omega), ?_, w.adj_getVert_succ (by omega)⟩
    have hh := w.adj_getVert_succ (show 2 < w.length by omega)
    have he : w.getVert 3 = w.getVert 0 := by rw [← h3, w.getVert_length, w.getVert_zero]
    rw [he] at hh
    exact Comb4.crosses_symm hh
  · right
    have h5 : 5 ≤ w.length := by rw [Nat.odd_iff] at ho; omega
    let a : Fin 5 → Fin (2*n) := fun i => (w.getVert i.val).val
    refine ⟨a, ?_, fun i => (w.getVert i.val).property,
      w.adj_getVert_succ (by omega), w.adj_getVert_succ (by omega),
      w.adj_getVert_succ (by omega), w.adj_getVert_succ (by omega)⟩
    intro i j he
    apply Fin.ext
    apply hi (show i.val < w.length by omega) (show j.val < w.length by omega)
    exact Subtype.ext he

theorem triangleReduction_of_split (split : Comb4.MonochromaticSplit) : TriangleReduction :=
  Comb4.reduction_of_window (Comb4.planarity_of_split split) oddCycleWindow_proved

#print axioms oddCycleWindow_proved
#print axioms triangleReduction_of_split
end Chord.Round5
