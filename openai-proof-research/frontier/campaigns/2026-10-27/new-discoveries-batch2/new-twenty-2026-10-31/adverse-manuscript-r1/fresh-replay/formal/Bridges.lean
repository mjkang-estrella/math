import Deletion0
import Deletion1
import Deletion2
import Deletion3
import Deletion4
import Deletion5
import Gram
import Mathlib.Algebra.BigOperators.Ring.Finset
import Independence
import Mathlib.Tactic.NormNum

open scoped BigOperators
namespace Adverse381433

set_option maxHeartbeats 4000000 in
theorem all_certificates (v : Cell) : CertificateAt v := by
  rcases v with ⟨a,b⟩
  fin_cases a <;> fin_cases b
  · exact certificate_0_0
  · exact certificate_0_1
  · exact certificate_0_2
  · exact certificate_0_3
  · exact certificate_0_4
  · exact certificate_0_5
  · exact certificate_1_0
  · exact certificate_1_1
  · exact certificate_1_2
  · exact certificate_1_3
  · exact certificate_1_4
  · exact certificate_1_5
  · exact certificate_2_0
  · exact certificate_2_1
  · exact certificate_2_2
  · exact certificate_2_3
  · exact certificate_2_4
  · exact certificate_2_5
  · exact certificate_3_0
  · exact certificate_3_1
  · exact certificate_3_2
  · exact certificate_3_3
  · exact certificate_3_4
  · exact certificate_3_5
  · exact certificate_4_0
  · exact certificate_4_1
  · exact certificate_4_2
  · exact certificate_4_3
  · exact certificate_4_4
  · exact certificate_4_5
  · exact certificate_5_0
  · exact certificate_5_1
  · exact certificate_5_2
  · exact certificate_5_3
  · exact certificate_5_4
  · exact certificate_5_5

@[norm_cast] theorem rat_sum_cast {I : Type} [Fintype I] (f : I → ℚ) :
    ((∑ i, f i : ℚ) : ℝ) = ∑ i, (f i : ℝ) := by
  exact map_sum (Rat.castHom ℝ) f Finset.univ

noncomputable def incidenceR (l : Line) (p : Cell) : ℝ := incidenceQ l p

theorem incidence_identityR (p q : Cell) :
    adjacency latinGraph p q = (∑ l : Line, incidenceR l p * incidenceR l q) - if p = q then 3 else 0 := by
  have h := incidence_identityQ p q
  have castAdj : (adjQ p q : ℝ) = adjacency latinGraph p q := by
    classical
    simp only [adjQ, adjacency, latinGraph, ne_eq]
    rw [apply_ite (fun r : ℚ => (r : ℝ))]
    norm_num
    congr 1
  have hh : (∑ l : Line, incidenceR l p * incidenceR l q) =
      (adjQ p q : ℝ) + if p = q then 3 else 0 := by
    have h' := congrArg (fun r : ℚ => (r : ℝ)) h
    simpa only [rat_sum_cast, Rat.cast_add, Rat.cast_mul, apply_ite, Rat.cast_ofNat, Rat.cast_zero, incidenceR] using h'
  rw [castAdj] at hh
  linarith

theorem kernel_eigen {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (B : Line → V → ℝ)
    (hg : ∀ i j, adjacency G i j = (∑ l, B l i * B l j) - if i = j then 3 else 0)
    (z : V → ℝ) (hk : ∀ l, ∑ p, B l p * z p = 0) :
    (adjacency G).mulVec z = (-3 : ℝ) • z := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  simp_rw [hg, sub_mul, Finset.sum_sub_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hex : (∑ j, (∑ l, B l i * B l j) * z j) = ∑ l, B l i * ∑ j, B l j * z j := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hex]
  simp [hk]

theorem global_least : leastEigenvalue latinGraph = -3 := by
  apply leastEigenvalue_eq_of_gram latinGraph incidenceR incidence_identityR
  refine ⟨fun p => (kernelBase p : ℝ), ?_, ?_⟩
  · intro he
    have h := congrFun he (1,2)
    change (kernelBase (1,2) : ℝ) = 0 at h
    exact base_certificates.2.2.2.2 (by exact_mod_cast h)
  · apply kernel_eigen latinGraph incidenceR incidence_identityR
    intro l
    have h := base_certificates.2.2.2.1 l
    unfold incidenceR
    exact_mod_cast h

theorem deletion_gram (v : Cell) (i j : deletionVertices latinGraph v) :
    adjacency (deleteOpen latinGraph v) i j =
      (∑ l : Line, incidenceR l i.val * incidenceR l j.val) - if i = j then 3 else 0 := by
  classical
  have h := incidence_identityR i.val j.val
  change adjacency latinGraph i.val j.val = _
  simpa only [Subtype.ext_iff] using h

theorem deletion_kernel_sum (v : Cell) (l : Line) :
    (∑ p : deletionVertices latinGraph v, incidenceR l p.val * (kernelAt v p.val : ℝ)) = 0 := by
  classical
  have hs : (∑ p : Cell, incidenceR l p * (kernelAt v p : ℝ)) = 0 := by
    unfold incidenceR
    exact_mod_cast (all_certificates v).2.2.2.1 l
  rw [← hs]
  symm
  apply Finset.sum_congr_set {p | ¬latinGraph.Adj v p}
  · intro p hp
    rfl
  · intro p hp
    have ha : latinGraph.Adj v p := Classical.not_not.mp hp
    rw [(all_certificates v).2.1 p ha |>.2]
    simp

theorem deletion_least (v : Cell) : leastEigenvalue (deleteOpen latinGraph v) = -3 := by
  classical
  apply leastEigenvalue_eq_of_gram (deleteOpen latinGraph v)
    (fun l p => incidenceR l p.val) (deletion_gram v)
  have hn := (all_certificates v).2.2.2.2
  have hp : ¬latinGraph.Adj v (translate v (1,2)) := by
    intro ha
    exact hn ((all_certificates v).2.1 _ ha).2
  refine ⟨fun p => (kernelAt v p.val : ℝ), ?_, ?_⟩
  · intro he
    have h := congrFun he ⟨translate v (1,2), hp⟩
    change (kernelAt v (translate v (1,2)) : ℝ) = 0 at h
    exact hn (by exact_mod_cast h)
  · exact kernel_eigen _ _ (deletion_gram v) _ (deletion_kernel_sum v)

end Adverse381433
