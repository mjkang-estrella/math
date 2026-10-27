import ConnectionLift
import IncidenceBlocks

open Finset Matrix
open scoped RealInnerProductSpace

namespace ConnectionGraph
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem topSet_contains_large (q : α → ℝ) {k : ℕ}
    (hk : k ≤ Fintype.card α) (hk0 : 0 < k) {a : ℝ} (ha : ∃ i, a ≤ q i) :
    ∃ j ∈ topSet q k, a ≤ q j := by
  obtain ⟨i, hi⟩ := ha
  by_cases his : i ∈ topSet q k
  · exact ⟨i, his, hi⟩
  · have hs : (topSet q k).Nonempty := card_pos.mp (by rw [topSet_card q hk]; exact hk0)
    obtain ⟨j, hj⟩ := hs
    exact ⟨j, hj, hi.trans (topSet_dominates q k his hj)⟩

omit [Fintype α] [DecidableEq α] in
theorem branch_sum_lower (q : α → ℝ) (s : Finset α)
    (hlarge : ∃ j ∈ s, 2 ≤ q j) :
    (s.card : ℝ) + (∑ i ∈ s, q i) / 2 + (Real.sqrt 2 - 1) ≤
      ∑ i ∈ s, positiveBranch (q i) := by
  obtain ⟨j, hj, hqj⟩ := hlarge
  have hsum : Real.sqrt 2 - 1 ≤ ∑ i ∈ s, branchExcess (q i) :=
    (branchExcess_ge_gap hqj).trans
      (single_le_sum (fun i _ => branchExcess_nonneg (q i)) hj)
  have he : (∑ i ∈ s, positiveBranch (q i)) =
      s.card + (∑ i ∈ s, q i) / 2 + ∑ i ∈ s, branchExcess (q i) := by
    simp_rw [positiveBranch_split]
    simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, sum_div]
  linarith

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem graph_has_large_signless_eigenvalue {E : Finset (V × V)}
    (hE : ValidEdges E) (hne : E.Nonempty) :
    ∃ i : V, 2 ≤ (gramHermitian (unsignedIncidence E)).eigenvalues i := by
  obtain ⟨ef, hef⟩ := hne
  let e : E := ⟨ef, hef⟩
  let : Nonempty V := ⟨e.val.1⟩
  let z : EuclideanSpace ℝ V :=
    EuclideanSpace.basisFun V ℝ e.val.1 + EuclideanSpace.basisFun V ℝ e.val.2
  have he := edge_ne hE e
  have hz : ‖z‖ ^ 2 = 2 := by
    rw [norm_add_sq_real]
    simp only [(EuclideanSpace.basisFun V ℝ).orthonormal.norm_eq_one,
      (EuclideanSpace.basisFun V ℝ).inner_eq_zero he, one_pow]
    norm_num
  have hze : z e.val.1 + z e.val.2 = 2 := by
    norm_num [z, EuclideanSpace.basisFun_apply, PiLp.add_apply, he, he.symm]
  have hq : 4 ≤ ⟪z, (signlessLaplacian E).toEuclideanLin z⟫ := by
    rw [matrix_inner_dot, unsigned_energy]
    calc
      4 = (z e.val.1 + z e.val.2) ^ 2 := by rw [hze]; norm_num
      _ ≤ _ := Finset.single_le_sum
        (f := fun i : E => (z i.val.1 + z i.val.2) ^ 2)
        (fun i _ => sq_nonneg _) (mem_univ e)
  obtain ⟨i, hi⟩ := exists_rayleigh_bound (gramHermitian (unsignedIncidence E)) z
  rw [hz] at hi
  refine ⟨i, ?_⟩
  change 4 ≤ ⟪z, (unsignedIncidence E * (unsignedIncidence E)ᵀ).toEuclideanLin z⟫ at hq
  linarith

theorem graph_low_connection_bound {E : Finset (V × V)} (hE : ValidEdges E)
    (hne : E.Nonempty) {k : ℕ} (hk0 : 0 < k) (hk : k ≤ Fintype.card V) :
    (k : ℝ) + sortedTopSum (degree E) k / 2 + (Real.sqrt 2 - 1) ≤
      spectralTopSum (connection_hermitian E) k := by
  let U := unsignedIncidence E
  let q := (gramHermitian U).eigenvalues
  let s := topSet q k
  have hs : s.card = k := topSet_card q hk
  have hl : ∃ j ∈ s, 2 ≤ q j :=
    topSet_contains_large q hk hk0 (graph_has_large_signless_eigenvalue hE hne)
  have hb := branch_sum_lower q s hl
  have hT : sortedTopSum (degree E) k ≤ ∑ i ∈ s, q i := by
    have hd := spectralTopSum_diagonal_le (gramHermitian U) hk
    have heq : (fun i => (U * Uᵀ) i i) = degree E := by
      funext i
      exact signless_diagonal hE i
    rw [heq] at hd
    exact hd.trans_eq (sortedTopSum_eq_sum_topSet q k)
  have hp := selected_positive_branches_le U s
  rw [hs] at hp
  have heq : liftedBlock U = connectionMatrix E := (connection_eq_blocks hE).symm
  have hp' : (∑ i ∈ s, positiveBranch (q i)) ≤
      spectralTopSum (connection_hermitian E) k := by
    simpa only [heq] using hp
  rw [hs] at hb
  linarith

end
end ConnectionGraph
