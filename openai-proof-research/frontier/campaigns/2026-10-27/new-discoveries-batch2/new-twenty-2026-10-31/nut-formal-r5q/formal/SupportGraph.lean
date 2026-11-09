import Invariances
import Mathlib.Combinatorics.SimpleGraph.Acyclic
namespace Nut8
/-- The ordinary, off-diagonal support of a structural quotient. -/
def supportGraph (C : QuotientMatrix) (s : ℤ) (h : Structural C s) :
    SimpleGraph (Fin 8) where
  Adj i j := i ≠ j ∧ C i j ≠ 0
  symm := ⟨by
    intro i j hij
    exact ⟨hij.1.symm, by simpa only [h.2.2.1 j i] using hij.2⟩⟩
  loopless := ⟨by simp⟩

instance (C : QuotientMatrix) (s : ℤ) (h : Structural C s) :
    DecidableRel (supportGraph C s h).Adj := fun i j => show Decidable (i ≠ j ∧ C i j ≠ 0) from inferInstance

theorem supportGraph_connected (C : QuotientMatrix) (s : ℤ) (h : Structural C s) :
    (supportGraph C s h).Connected := by
  classical
  let G := supportGraph C s h
  refine ⟨?_⟩
  intro u v
  by_contra hn
  let S : Finset (Fin 8) := Finset.univ.filter (G.Reachable u)
  have hu : u ∈ S := by simp [S]
  have hv : v ∉ S := by simpa [S] using hn
  have hp : S ≠ Finset.univ := by intro he; simp [he] at hv
  obtain ⟨i, hi, j, hj, hc⟩ := h.2.2.2.2.2.2.2 S ⟨u, hu⟩ hp
  have hij : i ≠ j := by intro he; exact hj (he ▸ hi)
  have hr : G.Reachable u i := (Finset.mem_filter.mp hi).2
  have ha : G.Adj i j := ⟨hij, hc⟩
  exact hj (by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact hr.trans ha.reachable)

theorem supportGraph_degree_le (C : QuotientMatrix) (s : ℤ) (h : Structural C s)
    (i : Fin 8) : (supportGraph C s h).degree i ≤ 3 := by
  classical
  let G := supportGraph C s h
  have hn : ∀ j ∈ G.neighborFinset i, (1 : ℤ) ≤ |C i j| := by
    intro j hj
    have hc : C i j ≠ 0 := ((G.mem_neighborFinset i j).mp hj).2
    have := abs_pos.mpr hc
    omega
  have hsum : (G.degree i : ℤ) ≤ ∑ j, |C i j| := by
    calc
      (G.degree i : ℤ) = ∑ _j ∈ G.neighborFinset i, (1 : ℤ) := by simp
      _ ≤ ∑ j ∈ G.neighborFinset i, |C i j| := Finset.sum_le_sum hn
      _ ≤ ∑ j, |C i j| := Finset.sum_le_univ_sum_of_nonneg (fun _ => abs_nonneg _)
  have hr := h.2.2.2.1 i
  change G.degree i ≤ 3
  omega

/-- This is mathlib's spanning-tree-leaf argument, specialized to the induction domain. -/
theorem connected_removable_vertex (k : ℕ) (G : SimpleGraph (Fin (k+2)))
    (h : G.Connected) : ∃ v, (G.induce {v}ᶜ).Connected :=
  h.exists_connected_induce_compl_singleton_of_finite_nontrivial
end Nut8
