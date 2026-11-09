import SignedCatalogue
import NewCertificates0195
import NewCertificates0196
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport132
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 3, 5, 1, 2, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0195.C6260, NewCertificates0195.C6261, NewCertificates0195.C6262, NewCertificates0195.C6263, NewCertificates0195.C6264, NewCertificates0195.C6265, NewCertificates0195.C6266, NewCertificates0195.C6267, NewCertificates0195.C6268, NewCertificates0195.C6269, NewCertificates0195.C6270, NewCertificates0195.C6271, NewCertificates0196.C6272, NewCertificates0196.C6273, NewCertificates0196.C6274, NewCertificates0196.C6275, NewCertificates0196.C6276, NewCertificates0196.C6277, NewCertificates0196.C6278, NewCertificates0196.C6279, NewCertificates0196.C6280, NewCertificates0196.C6281, NewCertificates0196.C6282, NewCertificates0196.C6283, NewCertificates0196.C6284, NewCertificates0196.C6285, NewCertificates0196.C6286, NewCertificates0196.C6287, NewCertificates0196.C6288, NewCertificates0196.C6289, NewCertificates0196.C6290, NewCertificates0196.C6291}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 1, 0, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 516033982661959872).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 516033982661959872 D i ∧ offSum 516033982661959872 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 516033982661959872 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 516033982661959872 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 516033982661959872 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport132
