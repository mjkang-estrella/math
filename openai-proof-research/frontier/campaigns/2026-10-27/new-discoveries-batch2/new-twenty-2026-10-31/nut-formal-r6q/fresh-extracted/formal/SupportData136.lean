import SignedCatalogue
import NewCertificates0199
import NewCertificates0200
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport136
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 3, 5, 2, 4, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0199.C6388, NewCertificates0199.C6389, NewCertificates0199.C6390, NewCertificates0199.C6391, NewCertificates0199.C6392, NewCertificates0199.C6393, NewCertificates0199.C6394, NewCertificates0199.C6395, NewCertificates0199.C6396, NewCertificates0199.C6397, NewCertificates0199.C6398, NewCertificates0199.C6399, NewCertificates0200.C6400, NewCertificates0200.C6401, NewCertificates0200.C6402, NewCertificates0200.C6403, NewCertificates0200.C6404, NewCertificates0200.C6405, NewCertificates0200.C6406, NewCertificates0200.C6407, NewCertificates0200.C6408, NewCertificates0200.C6409, NewCertificates0200.C6410, NewCertificates0200.C6411, NewCertificates0200.C6412, NewCertificates0200.C6413, NewCertificates0200.C6414, NewCertificates0200.C6415, NewCertificates0200.C6416, NewCertificates0200.C6417, NewCertificates0200.C6418, NewCertificates0200.C6419}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 1524840805729579200).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1524840805729579200 D i ∧ offSum 1524840805729579200 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1524840805729579200 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1524840805729579200 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1524840805729579200 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1524840805729579200 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport136
