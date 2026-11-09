import SignedCatalogue
import NewCertificates0230
import NewCertificates0231
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport156
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 7, 2, 4, 3, 6, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0230.C7368, NewCertificates0230.C7369, NewCertificates0230.C7370, NewCertificates0230.C7371, NewCertificates0230.C7372, NewCertificates0230.C7373, NewCertificates0230.C7374, NewCertificates0230.C7375, NewCertificates0230.C7376, NewCertificates0230.C7377, NewCertificates0230.C7378, NewCertificates0230.C7379, NewCertificates0230.C7380, NewCertificates0230.C7381, NewCertificates0230.C7382, NewCertificates0230.C7383, NewCertificates0230.C7384, NewCertificates0230.C7385, NewCertificates0230.C7386, NewCertificates0230.C7387, NewCertificates0230.C7388, NewCertificates0230.C7389, NewCertificates0230.C7390, NewCertificates0230.C7391, NewCertificates0231.C7392, NewCertificates0231.C7393, NewCertificates0231.C7394, NewCertificates0231.C7395, NewCertificates0231.C7396, NewCertificates0231.C7397, NewCertificates0231.C7398, NewCertificates0231.C7399}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 940712645804183712).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 940712645804183712 D i ∧ offSum 940712645804183712 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 940712645804183712 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 940712645804183712 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 940712645804183712 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport156
