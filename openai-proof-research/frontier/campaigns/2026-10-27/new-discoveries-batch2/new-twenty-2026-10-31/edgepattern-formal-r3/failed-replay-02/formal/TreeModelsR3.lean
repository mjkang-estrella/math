import MaskR3
import ConcreteR2
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxHeartbeats 400000
structure Counts where
  a : Fin 3
  b : Fin 3
  c : Fin 3
  d : Fin 3
  deriving DecidableEq, Fintype

def order (k : Counts) : ℕ := 6 + k.a + k.b + k.c + k.d
abbrev V (k : Counts) := Fin (order k)
def forward (k : Counts) (x y : V k) : Prop :=
  (x.val = 0 ∧ (y.val = 1 ∨ y.val = 2 ∨ y.val = 3)) ∨
  (x.val = 1 ∧ (y.val = 4 ∨ y.val = 5)) ∨
  (x.val = 2 ∧ 6 ≤ y.val ∧ y.val < 6 + k.a) ∨
  (x.val = 3 ∧ 6 + k.a ≤ y.val ∧ y.val < 6 + k.a + k.b) ∨
  (x.val = 4 ∧ 6 + k.a + k.b ≤ y.val ∧ y.val < 6 + k.a + k.b + k.c) ∨
  (x.val = 5 ∧ 6 + k.a + k.b + k.c ≤ y.val)
instance (k : Counts) (x y : V k) : Decidable (forward k x y) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

def graph (k : Counts) : SimpleGraph (V k) where
  Adj x y := forward k x y ∨ forward k y x
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro x h
    simp only [forward] at h
    have ha := k.a.isLt
    have hb := k.b.isLt
    have hc := k.c.isLt
    have hd := k.d.isLt
    have hn : 6 ≤ order k := by unfold order; omega
    omega⟩
instance (k : Counts) : DecidableRel (graph k).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))
def pattern (k : Counts) : Rooted (V k) where
  graph := graph k
  left := ⟨0,by unfold order; omega⟩
  right := ⟨1,by unfold order; omega⟩
  root_edge := by left; simp [forward]
def level {k : Counts} (x : V k) : ℕ := if x.val < 2 then 0 else if x.val < 6 then 1 else 2

theorem order_le (k : Counts) : order k ≤ 14 := by
  have := k.a.isLt; have := k.b.isLt; have := k.c.isLt; have := k.d.isLt
  unfold order; omega

private theorem lower_two {k : Counts} (v w : V k) (h : v ≠ w)
    (ha : ¬ (graph k).Adj v w) : 2 ≤ (graph k).edist v w := by
  have hn : ¬ (graph k).edist v w ≤ 1 := by
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    exact not_or.mpr ⟨ha,h⟩
  exact (ENat.natCast_add_one_le_iff (m := 1)).mpr (lt_of_not_ge hn)

theorem distance_eq (k : Counts) (x : V k) : rootDistance (pattern k) x = level x := by
  have hn : 6 ≤ order k := by unfold order; omega
  let z : V k := ⟨0,by omega⟩
  let o : V k := ⟨1,by omega⟩
  have hz : z = (pattern k).left := rfl
  have ho : o = (pattern k).right := rfl
  by_cases h0 : x.val = 0
  · have hx : x = z := Fin.ext h0
    subst x
    simp [rootDistance, pattern, level, z]
  by_cases h1 : x.val = 1
  · have hx : x = o := Fin.ext h1
    subst x
    simp [rootDistance, pattern, level, o]
  have hxz : x ≠ z := by intro h; exact h0 (congrArg Fin.val h)
  have hxo : x ≠ o := by intro h; exact h1 (congrArg Fin.val h)
  change min ((graph k).edist x z) ((graph k).edist x o) = _
  by_cases h6 : x.val < 6
  · have hl : level x = 1 := by unfold level; split_ifs <;> omega
    rw [hl]
    apply le_antisymm
    · have hadj : (graph k).Adj x z ∨ (graph k).Adj x o := by
        simp [graph, forward, z, o]; omega
      rcases hadj with h | h
      · exact (min_le_left _ _).trans (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr h))
      · exact (min_le_right _ _).trans (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr h))
    · exact le_min (Order.one_le_iff_pos.mpr (SimpleGraph.edist_pos_of_ne hxz))
        (Order.one_le_iff_pos.mpr (SimpleGraph.edist_pos_of_ne hxo))
  · have hl : level x = 2 := by unfold level; split_ifs <;> omega
    rw [hl]
    have naz : ¬ (graph k).Adj x z := by simp [graph, forward, z]; omega
    have nao : ¬ (graph k).Adj x o := by simp [graph, forward, o]; omega
    apply le_antisymm
    · by_cases hab : x.val < 6 + k.a + k.b
      · apply (min_le_left _ _).trans
        apply le_of_eq
        apply SimpleGraph.edist_eq_two_iff.mpr
        refine ⟨hxz,naz,?_⟩
        let p : V k := ⟨if x.val < 6 + k.a then 2 else 3, by split_ifs <;> omega⟩
        exact ⟨p, by change (graph k).Adj x p ∧ (graph k).Adj z p; dsimp [graph, forward, z, p]; split_ifs <;> simp_all⟩
      · apply (min_le_right _ _).trans
        apply le_of_eq
        apply SimpleGraph.edist_eq_two_iff.mpr
        refine ⟨hxo,nao,?_⟩
        let p : V k := ⟨if x.val < 6 + k.a + k.b + k.c then 4 else 5, by split_ifs <;> omega⟩
        exact ⟨p, by change (graph k).Adj x p ∧ (graph k).Adj o p; dsimp [graph, forward, o, p]; split_ifs <;> simp_all⟩
    · exact le_min (lower_two x z hxz naz) (lower_two x o hxo nao)

def layers (k : Counts) (i : ℕ) : Finset (V k) := Finset.univ.filter (fun x => level x = i)
theorem layer_eq (k : Counts) (i : ℕ) : layer (pattern k) i = layers k i := by
  classical
  ext x
  simp [layer, layers, distance_eq]

def totals (k : Counts) (i : ℕ) : ℕ :=
  ∑ s ∈ (MaskR3.best (graph k)).image (MaskR3.decode (order k)), (s ∩ layers k i).card

def count (k : Counts) : ℕ := ((MaskR3.best (graph k)).image (MaskR3.decode (order k))).card

def occupancy (k : Counts) (i : ℕ) : ℚ := (totals k i : ℚ) / count k

theorem expectation_eq (k : Counts) (i : ℕ) : expectation (pattern k) i = occupancy k i := by
  classical
  unfold expectation occupancy totals count
  rw [layer_eq, show (pattern k).graph = graph k from rfl, MaskR3.maxima_eq]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  congr 2
  ext v
  simp
end EdgePattern.TreeModelsR3
