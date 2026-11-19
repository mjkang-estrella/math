import LinfBridge
import K8Sound
import K8Wlog
import K8Cert07

/-!
# Main theorem: `K₈` is not edge-redundantly rigid in `ℓ∞³`

Hence Conjecture 5.4 of Cruickshank, Dewar and Kitson fails at `d = 3`, `n = 8`.

Chain of the proof:
1. `CDK.good_of_edgeRedundant` (`LinfBridge`): an edge-redundantly rigid framework
   `(K₈, p)` in `ℓ∞³` is `K8.Good`.
2. `K8.exists_anchored` (`K8Wlog`): a good placement can be normalised by an
   isometry of `ℓ∞³` and a relabelling to an anchored good placement.
3. `K8.base_of_good` (`K8Sound`): the induced assignment satisfies every clause
   of the propositional instance `K8.Base`.
4. `K8.Cert.cert_unsat` (`K8Cert00`–`K8Cert07`): no assignment satisfies
   `K8.Base` (kernel-checked RUP certificate).
-/

namespace CDK

/-- No placement of eight points in `ℝ³` satisfies the combinatorial
consequences of edge-redundant rigidity. -/
theorem k8_no_good : ¬ ∃ p : Fin 8 → Fin 3 → ℝ, K8.Good p := by
  rintro ⟨p, hp⟩
  obtain ⟨q, hq, ha⟩ := K8.exists_anchored hp
  exact K8.Cert.cert_unsat _ (K8.base_of_good hq ha)

/-- **Main theorem.** The complete graph `K₈` is not edge-redundantly rigid in `ℓ∞³`. -/
theorem not_edgeRedundantlyRigid_K8 : ¬ EdgeRedundantlyRigid (completeGraph 8) 3 := by
  rintro ⟨p, hp⟩
  obtain ⟨h1, h2⟩ := good_of_edgeRedundant hp
  exact k8_no_good ⟨p, ⟨h1, h2⟩⟩

/-- Conjecture 5.4 of Cruickshank–Dewar–Kitson is false. -/
theorem not_conjecture : ¬ Conjecture := fun h =>
  not_edgeRedundantlyRigid_K8 (h 3 8 (by norm_num) (by norm_num))

end CDK
