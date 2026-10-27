import Variational

open Finset Matrix

namespace ConnectionGraph
noncomputable section
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem spectral_values_multiset {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (((descendingIndices hA.eigenvalues).map hA.eigenvalues : List ℝ) : Multiset ℝ) =
      A.charpoly.roots := by
  rw [hA.roots_charpoly_eq_eigenvalues]
  have hp := (descendingIndices_perm hA.eigenvalues).map hA.eigenvalues
  have hm := Multiset.coe_eq_coe.mpr hp
  simpa only [← Multiset.map_coe, Finset.coe_toList, RCLike.ofReal_real_eq_id,
    Function.id_comp] using hm

theorem spectralTopSum_eq_of_charpoly {A : Matrix n n ℝ} {B : Matrix m m ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A.charpoly = B.charpoly) (k : ℕ) :
    spectralTopSum hA k = spectralTopSum hB k := by
  have hm :
      (((descendingIndices hA.eigenvalues).map hA.eigenvalues : List ℝ) : Multiset ℝ) =
        ((descendingIndices hB.eigenvalues).map hB.eigenvalues : List ℝ) := by
    rw [spectral_values_multiset hA, spectral_values_multiset hB, hAB]
  have hp := Multiset.coe_eq_coe.mp hm
  have hpa : ((descendingIndices hA.eigenvalues).map hA.eigenvalues).Pairwise
      (fun a b => b ≤ a) := by
    simpa only [List.pairwise_map] using descendingIndices_pairwise hA.eigenvalues
  have hpb : ((descendingIndices hB.eigenvalues).map hB.eigenvalues).Pairwise
      (fun a b => b ≤ a) := by
    simpa only [List.pairwise_map] using descendingIndices_pairwise hB.eigenvalues
  have heq := hp.eq_of_pairwise' hpa hpb
  unfold spectralTopSum sortedTopSum
  rw [List.map_take, List.map_take, heq]

theorem spectralTopSum_reindex {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (e : n ≃ m) (k : ℕ) :
    spectralTopSum (hA.reindex e) k = spectralTopSum hA k := by
  apply spectralTopSum_eq_of_charpoly
  exact Matrix.charpoly_reindex e A

end
end ConnectionGraph
