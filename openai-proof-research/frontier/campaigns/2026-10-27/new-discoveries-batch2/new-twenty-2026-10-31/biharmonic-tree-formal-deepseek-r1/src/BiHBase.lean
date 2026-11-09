/-
BiHBase: the literal definition of the biharmonic index through mathlib's Laplacian
and eigenvalues, the star and path graphs, and the fact that a connected graph has
exactly one zero Laplacian eigenvalue.

MathDB 352303 (Z. Lin, arXiv:2110.09931, Conjecture 5.3).
-/
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Matrix

namespace BiH

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The real Laplacian eigenvalues of a simple graph, indexed by the vertex type. -/
noncomputable abbrev lapEigs (G : SimpleGraph V) [DecidableRel G.Adj] : V → ℝ :=
  (G.isHermitian_lapMatrix ℝ).eigenvalues

/-- The biharmonic index `BH(G) = n * ∑_{λ ≠ 0} λ⁻²`, where `n = #V` and `λ` runs over
the Laplacian eigenvalues of `G`. -/
noncomputable def bh (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (Fintype.card V : ℝ) * ∑ i : V, if lapEigs G i = 0 then 0 else (lapEigs G i)⁻¹ ^ 2

theorem bh_eq_card_mul_sum_filter (G : SimpleGraph V) [DecidableRel G.Adj] :
    bh G = (Fintype.card V : ℝ) *
      ∑ i ∈ Finset.univ.filter (fun i => lapEigs G i ≠ 0), (lapEigs G i)⁻¹ ^ 2 := by
  classical
  unfold bh
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : lapEigs G i = 0
  · simp [h]
  · simp [h]

theorem bh_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] : 0 ≤ bh G := by
  classical
  unfold bh
  have : (0 : ℝ) ≤ ∑ i : V, if lapEigs G i = 0 then 0 else (lapEigs G i)⁻¹ ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs with h
    · exact le_refl 0
    · positivity
  exact mul_nonneg (Nat.cast_nonneg _) this

/-- The rank of the Laplacian equals the number of vertices minus the dimension of its kernel. -/
theorem rank_lapMatrix_eq_card_sub_finrank_ker (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.lapMatrix ℝ).rank =
      Fintype.card V - Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ))) := by
  classical
  have hrange : (G.lapMatrix ℝ).rank =
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' (G.lapMatrix ℝ))) := by
    rw [Matrix.range_toLin', ← Matrix.rank_eq_finrank_span_cols]
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (G.lapMatrix ℝ))
  rw [Module.finrank_pi] at hrn
  omega

/-- **Exactly one zero eigenvalue.** A connected graph has exactly one zero Laplacian
eigenvalue; equivalently the sum over non-zero eigenvalues has `n - 1` terms, matching the
source's range `i = 2, …, n`. -/
theorem card_zero_eigs_of_connected (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) :
    Fintype.card {i : V // lapEigs G i = 0} = 1 := by
  classical
  have hcard : Fintype.card G.ConnectedComponent = 1 := by
    have hsub : Subsingleton G.ConnectedComponent :=
      hG.preconnected.subsingleton_connectedComponent
    obtain ⟨v⟩ := hG.nonempty
    exact Fintype.card_eq_one_iff.mpr
      ⟨G.connectedComponentMk v, fun y => Subsingleton.elim y _⟩
  have hker : Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ))) = 1 := by
    rw [← SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix G, hcard]
  have hrank : (G.lapMatrix ℝ).rank =
      Fintype.card {i : V // lapEigs G i ≠ 0} :=
    (G.isHermitian_lapMatrix ℝ).rank_eq_card_non_zero_eigs
  have hrank' : (G.lapMatrix ℝ).rank = Fintype.card V - 1 := by
    rw [rank_lapMatrix_eq_card_sub_finrank_ker, hker]
  have hne : Fintype.card {i : V // lapEigs G i ≠ 0} = Fintype.card V - 1 := by
    rw [← hrank]
    exact hrank'
  have hcompl : Fintype.card {i : V // lapEigs G i ≠ 0} =
      Fintype.card V - Fintype.card {i : V // lapEigs G i = 0} :=
    Fintype.card_subtype_compl (fun i : V => lapEigs G i = 0)
  have hle : Fintype.card {i : V // lapEigs G i = 0} ≤ Fintype.card V :=
    Fintype.card_subtype_le _
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hG.nonempty
  omega

/-- The non-zero eigenvalues are exactly `n - 1` in number for a connected graph. -/
theorem card_nonzero_eigs_of_connected (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) :
    Fintype.card {i : V // lapEigs G i ≠ 0} = Fintype.card V - 1 := by
  classical
  have hcard : Fintype.card G.ConnectedComponent = 1 := by
    have hsub : Subsingleton G.ConnectedComponent :=
      hG.preconnected.subsingleton_connectedComponent
    obtain ⟨v⟩ := hG.nonempty
    exact Fintype.card_eq_one_iff.mpr
      ⟨G.connectedComponentMk v, fun y => Subsingleton.elim y _⟩
  have hker : Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ))) = 1 := by
    rw [← SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix G, hcard]
  have hrank : (G.lapMatrix ℝ).rank =
      Fintype.card {i : V // lapEigs G i ≠ 0} :=
    (G.isHermitian_lapMatrix ℝ).rank_eq_card_non_zero_eigs
  rw [← hrank, rank_lapMatrix_eq_card_sub_finrank_ker, hker]

/-- The star `K_{1,n-1}` on `Fin n`. -/
abbrev starGraphFin (n : ℕ) (hn : 0 < n) : SimpleGraph (Fin n) :=
  SimpleGraph.starGraph ⟨0, hn⟩

/-- The path `P_n` on `Fin n`. -/
abbrev pathGraphFin (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.pathGraph n

instance instDecidableRelPathGraphFin (n : ℕ) : DecidableRel (SimpleGraph.pathGraph n).Adj :=
  fun u v => decidable_of_iff (u.val + 1 = v.val ∨ v.val + 1 = u.val)
    SimpleGraph.pathGraph_adj.symm

/-- The biharmonic index of the star on `n` vertices, `n ≥ 1`. -/
noncomputable def bhStar (n : ℕ) (hn : 0 < n) : ℝ :=
  bh (starGraphFin n hn)

/-- The biharmonic index of the path on `n` vertices. -/
noncomputable def bhPath (n : ℕ) : ℝ :=
  bh (pathGraphFin n)

end BiH
