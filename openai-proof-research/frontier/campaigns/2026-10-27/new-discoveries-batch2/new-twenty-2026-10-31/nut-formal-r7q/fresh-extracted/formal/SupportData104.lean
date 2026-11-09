import SignedCatalogue
import NewCertificates0151
import NewCertificates0152
import NewCertificates0153
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport104
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 4, 5, 6, 2, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0151.C4854, NewCertificates0151.C4855, NewCertificates0151.C4856, NewCertificates0151.C4857, NewCertificates0151.C4858, NewCertificates0151.C4859, NewCertificates0151.C4860, NewCertificates0151.C4861, NewCertificates0151.C4862, NewCertificates0151.C4863, NewCertificates0152.C4864, NewCertificates0152.C4865, NewCertificates0152.C4866, NewCertificates0152.C4867, NewCertificates0152.C4868, NewCertificates0152.C4869, NewCertificates0152.C4870, NewCertificates0152.C4871, NewCertificates0152.C4872, NewCertificates0152.C4873, NewCertificates0152.C4874, NewCertificates0152.C4875, NewCertificates0152.C4876, NewCertificates0152.C4877, NewCertificates0152.C4878, NewCertificates0152.C4879, NewCertificates0152.C4880, NewCertificates0152.C4881, NewCertificates0152.C4882, NewCertificates0152.C4883, NewCertificates0152.C4884, NewCertificates0152.C4885, NewCertificates0152.C4886, NewCertificates0152.C4887, NewCertificates0152.C4888, NewCertificates0152.C4889, NewCertificates0152.C4890, NewCertificates0152.C4891, NewCertificates0152.C4892, NewCertificates0152.C4893, NewCertificates0152.C4894, NewCertificates0152.C4895, NewCertificates0153.C4896, NewCertificates0153.C4897, NewCertificates0153.C4898, NewCertificates0153.C4899, NewCertificates0153.C4900, NewCertificates0153.C4901}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,2)}
theorem doubled_enumeration : ((supportEdges 1808789952501269632).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1808789952501269632 D i ∧ offSum 1808789952501269632 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1808789952501269632 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1808789952501269632 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1808789952501269632 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1808789952501269632 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport104
