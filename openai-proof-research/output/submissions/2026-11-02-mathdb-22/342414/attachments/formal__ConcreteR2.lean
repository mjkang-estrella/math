import Concrete
namespace EdgePattern.Concrete
open scoped BigOperators

def distanceTable : V → ℕ := ![0,0,1,1,2,1,2,1]

private theorem lower_one (v w : V) (h : v ≠ w) : 1 ≤ graph.edist v w :=
  Order.one_le_iff_pos.mpr (SimpleGraph.edist_pos_of_ne h)

private theorem lower_two (v w : V) (h : v ≠ w) (ha : ¬ graph.Adj v w) :
    2 ≤ graph.edist v w := by
  have hn : ¬ graph.edist v w ≤ 1 := by
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    exact not_or.mpr ⟨ha,h⟩
  exact (ENat.natCast_add_one_le_iff (m := 1)).mpr (lt_of_not_ge hn)

private theorem root_one (v : V) (h0 : v ≠ 0) (h1 : v ≠ 1)
    (h : graph.Adj v 0 ∨ graph.Adj v 1) : rootDistance pattern v = 1 := by
  change min (graph.edist v 0) (graph.edist v 1) = 1
  apply le_antisymm
  · rcases h with h | h
    · exact (min_le_left _ _).trans (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr h))
    · exact (min_le_right _ _).trans (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr h))
  · exact le_min (lower_one v 0 h0) (lower_one v 1 h1)

private theorem root_two (v : V) (h0 : v ≠ 0) (h1 : v ≠ 1)
    (ha0 : ¬ graph.Adj v 0) (ha1 : ¬ graph.Adj v 1)
    (h : graph.edist v 0 = 2 ∨ graph.edist v 1 = 2) : rootDistance pattern v = 2 := by
  change min (graph.edist v 0) (graph.edist v 1) = 2
  apply le_antisymm
  · rcases h with h | h
    · exact (min_le_left _ _).trans (le_of_eq h)
    · exact (min_le_right _ _).trans (le_of_eq h)
  · exact le_min (lower_two v 0 h0 ha0) (lower_two v 1 h1 ha1)

theorem distance_values (v : V) : rootDistance pattern v = distanceTable v := by
  fin_cases v
  · simp [rootDistance, pattern, distanceTable]
  · simp [rootDistance, pattern, distanceTable]
  · exact root_one 2 (by decide) (by decide) (by decide)
  · exact root_one 3 (by decide) (by decide) (by decide)
  · apply root_two 4 (by decide) (by decide) (by decide) (by decide)
    left
    apply SimpleGraph.edist_eq_two_iff.mpr
    exact ⟨by decide, by decide, ⟨3, by decide⟩⟩
  · exact root_one 5 (by decide) (by decide) (by decide)
  · apply root_two 6 (by decide) (by decide) (by decide) (by decide)
    right
    apply SimpleGraph.edist_eq_two_iff.mpr
    exact ⟨by decide, by decide, ⟨5, by decide⟩⟩
  · exact root_one 7 (by decide) (by decide) (by decide)

theorem layer_eq (i : Fin 3) : layer pattern i = layers i := by
  classical
  ext v
  simp only [layer, Finset.mem_filter, Finset.mem_univ, true_and, distance_values]
  fin_cases i <;> fin_cases v <;> decide

theorem regular : RegularPattern pattern 3 2 := by
  constructor
  · constructor
    · intro v
      rw [distance_values]
      fin_cases v <;> decide
    · exact ⟨4, distance_values 4⟩
  · intro v
    rw [distance_values]
    have hc : (graph.neighborSet v).ncard = (graph.neighborFinset v).card := by
      rw [← Set.ncard_coe_finset (graph.neighborFinset v)]
      simp
    change (graph.neighborSet v).ncard ≤ 3 ∧ (_ → (graph.neighborSet v).ncard = 3)
    rw [hc]
    fin_cases v <;> norm_num [distanceTable] <;> decide

theorem expectation_eq (i : Fin 3) : expectation pattern i = occupancy i := by
  classical
  unfold expectation occupancy totals
  rw [show pattern.graph = graph from rfl, maxima_eq, layer_eq]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  congr 2
  ext v
  simp

theorem expectation_values : expectation pattern 0 = 2/5 ∧
    expectation pattern 1 = 14/5 ∧ expectation pattern 2 = 4/5 := by
  change expectation pattern ((0 : Fin 3) : ℕ) = 2/5 ∧
    expectation pattern ((1 : Fin 3) : ℕ) = 14/5 ∧
    expectation pattern ((2 : Fin 3) : ℕ) = 4/5
  rw [expectation_eq, expectation_eq, expectation_eq]
  exact occupancy_values

theorem expectation_separating_value :
    (∑ i : Fin 3, alpha i * expectation pattern i) = 67027/67500 := by
  simp_rw [expectation_eq]
  exact separating_value

theorem expectation_separating_lt_one :
    (∑ i : Fin 3, alpha i * expectation pattern i) < 1 := by
  rw [expectation_separating_value]
  norm_num
end EdgePattern.Concrete
