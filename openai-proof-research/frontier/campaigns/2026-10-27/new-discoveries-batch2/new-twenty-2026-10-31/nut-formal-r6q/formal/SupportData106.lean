import SignedCatalogue
import NewCertificates0154
import NewCertificates0155
import NewCertificates0156
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport106
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 5, 4, 6, 2, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0154.C4950, NewCertificates0154.C4951, NewCertificates0154.C4952, NewCertificates0154.C4953, NewCertificates0154.C4954, NewCertificates0154.C4955, NewCertificates0154.C4956, NewCertificates0154.C4957, NewCertificates0154.C4958, NewCertificates0154.C4959, NewCertificates0155.C4960, NewCertificates0155.C4961, NewCertificates0155.C4962, NewCertificates0155.C4963, NewCertificates0155.C4964, NewCertificates0155.C4965, NewCertificates0155.C4966, NewCertificates0155.C4967, NewCertificates0155.C4968, NewCertificates0155.C4969, NewCertificates0155.C4970, NewCertificates0155.C4971, NewCertificates0155.C4972, NewCertificates0155.C4973, NewCertificates0155.C4974, NewCertificates0155.C4975, NewCertificates0155.C4976, NewCertificates0155.C4977, NewCertificates0155.C4978, NewCertificates0155.C4979, NewCertificates0155.C4980, NewCertificates0155.C4981, NewCertificates0155.C4982, NewCertificates0155.C4983, NewCertificates0155.C4984, NewCertificates0155.C4985, NewCertificates0155.C4986, NewCertificates0155.C4987, NewCertificates0155.C4988, NewCertificates0155.C4989, NewCertificates0155.C4990, NewCertificates0155.C4991, NewCertificates0156.C4992, NewCertificates0156.C4993, NewCertificates0156.C4994, NewCertificates0156.C4995, NewCertificates0156.C4996, NewCertificates0156.C4997}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,2)}
theorem doubled_enumeration : ((supportEdges 2961842882838938752).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2961842882838938752 D i ∧ offSum 2961842882838938752 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 2961842882838938752 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2961842882838938752 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2961842882838938752 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2961842882838938752 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport106
