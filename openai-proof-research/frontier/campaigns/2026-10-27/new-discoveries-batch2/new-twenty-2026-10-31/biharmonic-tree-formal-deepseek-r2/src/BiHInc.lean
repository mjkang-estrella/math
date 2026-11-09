/-
BiHInc: the signed incidence matrix of a graph, built from a proper 2-colouring,
together with `B * Bᵀ = L`, `Bᵀ *ᵥ 1 = 0`, and full column rank for a tree.

MathDB 352303 (Z. Lin, arXiv:2110.09931).
-/
import BiHBase
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Matrix.Rank

open Matrix

namespace BiH

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sign attached to a vertex by a 2-colouring: `+1` on colour `0`, `-1` on colour `1`. -/
noncomputable def colSign {G : SimpleGraph V} (c : G.Coloring (Fin 2)) (v : V) : ℝ :=
  if c v = 0 then 1 else -1

omit [Fintype V] [DecidableEq V] in
theorem colSign_sq {G : SimpleGraph V} (c : G.Coloring (Fin 2)) (v : V) :
    colSign c v * colSign c v = 1 := by
  unfold colSign
  split_ifs <;> norm_num

omit [Fintype V] [DecidableEq V] in
theorem colSign_mul_of_adj {G : SimpleGraph V} (c : G.Coloring (Fin 2)) {v w : V}
    (h : G.Adj v w) : colSign c v * colSign c w = -1 := by
  have hne : c v ≠ c w := c.valid h
  unfold colSign
  have hv : c v = 0 ∨ c v = 1 := by have := (c v).isLt; omega
  have hw : c w = 0 ∨ c w = 1 := by have := (c w).isLt; omega
  rcases hv with h1 | h1 <;> rcases hw with h2 | h2 <;> simp_all

omit [Fintype V] [DecidableEq V] in
theorem colSign_add_of_adj {G : SimpleGraph V} (c : G.Coloring (Fin 2)) {v w : V}
    (h : G.Adj v w) : colSign c v + colSign c w = 0 := by
  have hne : c v ≠ c w := c.valid h
  unfold colSign
  have hv : c v = 0 ∨ c v = 1 := by have := (c v).isLt; omega
  have hw : c w = 0 ∨ c w = 1 := by have := (c w).isLt; omega
  rcases hv with h1 | h1 <;> rcases hw with h2 | h2 <;> simp_all

/-- The signed incidence matrix of `G`, indexed by the finite edge set `G.edgeFinset`. -/
noncomputable def sInc {G : SimpleGraph V} [DecidableRel G.Adj]
    [Fintype G.edgeSet] (c : G.Coloring (Fin 2)) : Matrix V ↥G.edgeFinset ℝ :=
  fun v e => colSign c v * G.incMatrix ℝ v (e : Sym2 V)

variable {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype G.edgeSet]

theorem inc_entry_eq_incMatrix (v w : V) :
    ∑ e : ↥G.edgeFinset, G.incMatrix ℝ v (e : Sym2 V) * G.incMatrix ℝ w (e : Sym2 V)
      = (G.incMatrix ℝ * (G.incMatrix ℝ)ᵀ) v w := by
  classical
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  have h1 : ∑ e : ↥G.edgeFinset,
      G.incMatrix ℝ v (e : Sym2 V) * G.incMatrix ℝ w (e : Sym2 V)
      = ∑ e ∈ G.edgeFinset, G.incMatrix ℝ v e * G.incMatrix ℝ w e :=
    Finset.sum_coe_sort G.edgeFinset
      (fun e => G.incMatrix ℝ v e * G.incMatrix ℝ w e)
  have h2 : ∑ e ∈ G.edgeFinset, G.incMatrix ℝ v e * G.incMatrix ℝ w e
      = ∑ e : Sym2 V, G.incMatrix ℝ v e * G.incMatrix ℝ w e := by
    refine Finset.sum_subset (Finset.subset_univ G.edgeFinset) ?_
    intro e _ he
    have hne : e ∉ G.edgeSet := by simpa using he
    have h0 : G.incMatrix ℝ v e = 0 :=
      G.incMatrix_of_notMem_incidenceSet (fun hh => hne (G.incidenceSet_subset v hh))
    simp [h0]
  rw [h1, h2]

theorem sInc_mul_transpose (c : G.Coloring (Fin 2)) :
    sInc c * (sInc c)ᵀ = G.lapMatrix ℝ := by
  classical
  ext v w
  have h1 : ∑ e : ↥G.edgeFinset, sInc c v e * sInc c w e
      = colSign c v * colSign c w *
        ∑ e : ↥G.edgeFinset, G.incMatrix ℝ v (e : Sym2 V) * G.incMatrix ℝ w (e : Sym2 V) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e _ => by simp only [sInc]; ring)
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [h1, inc_entry_eq_incMatrix, SimpleGraph.incMatrix_mul_transpose]
  simp only [Matrix.of_apply]
  rcases eq_or_ne v w with hvw | hvw
  · subst hvw
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      Matrix.sub_apply, colSign_sq, SimpleGraph.irrefl]
  · by_cases hadj : G.Adj v w
    · simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
        Matrix.sub_apply, hvw, hadj, colSign_mul_of_adj c hadj]
    · simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
        Matrix.sub_apply, hvw, hadj]

theorem sInc_transpose_mulVec_one (c : G.Coloring (Fin 2)) :
    (sInc c)ᵀ *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  classical
  funext e
  have hcol : ∑ v : V, colSign c v * G.incMatrix ℝ v (e : Sym2 V) = 0 := by
    refine Sym2.ind (f := fun z => z ∈ G.edgeSet →
      ∑ v : V, colSign c v * G.incMatrix ℝ v z = 0) ?_ (e : Sym2 V) (G.mem_edgeFinset.mp e.2)
    intro a b hab
    have hiff : ∀ v : V, G.incMatrix ℝ v s(a, b) = if v = a ∨ v = b then (1:ℝ) else 0 := by
      intro v
      rw [SimpleGraph.incMatrix_apply']
      by_cases h : v = a ∨ v = b
      · have hmem : s(a, b) ∈ G.incidenceSet v := ⟨hab, Sym2.mem_iff.mpr h⟩
        rw [ite_eq_left hmem, ite_eq_left h]
      · have hmem : s(a, b) ∉ G.incidenceSet v := fun hh => h (Sym2.mem_iff.mp hh.2)
        rw [ite_eq_right hmem, ite_eq_right h]
    have hstep : ∀ v : V, colSign c v * (if v = a ∨ v = b then (1:ℝ) else 0)
        = if v ∈ ({a, b} : Finset V) then colSign c v else 0 := by
      intro v; by_cases h : v = a ∨ v = b <;> simp [h]
    simp only [hiff, hstep]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair (G.ne_of_adj hab)]
    exact colSign_add_of_adj c hab
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Matrix.transpose_apply, mul_one, sInc]
  exact hcol

end BiH
