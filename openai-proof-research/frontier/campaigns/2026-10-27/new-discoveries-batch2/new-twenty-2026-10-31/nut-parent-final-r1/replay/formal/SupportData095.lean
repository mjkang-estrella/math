import SignedCatalogue
import NewCertificates0137
import NewCertificates0138
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport095
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 4, 6, 5, 3, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 5, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0137.C4398, NewCertificates0137.C4399, NewCertificates0137.C4400, NewCertificates0137.C4401, NewCertificates0137.C4402, NewCertificates0137.C4403, NewCertificates0137.C4404, NewCertificates0137.C4405, NewCertificates0137.C4406, NewCertificates0137.C4407, NewCertificates0137.C4408, NewCertificates0137.C4409, NewCertificates0137.C4410, NewCertificates0137.C4411, NewCertificates0137.C4412, NewCertificates0137.C4413, NewCertificates0137.C4414, NewCertificates0137.C4415, NewCertificates0138.C4416, NewCertificates0138.C4417, NewCertificates0138.C4418, NewCertificates0138.C4419, NewCertificates0138.C4420, NewCertificates0138.C4421, NewCertificates0138.C4422, NewCertificates0138.C4423, NewCertificates0138.C4424, NewCertificates0138.C4425, NewCertificates0138.C4426, NewCertificates0138.C4427, NewCertificates0138.C4428, NewCertificates0138.C4429, NewCertificates0138.C4430, NewCertificates0138.C4431, NewCertificates0138.C4432, NewCertificates0138.C4433, NewCertificates0138.C4434, NewCertificates0138.C4435, NewCertificates0138.C4436, NewCertificates0138.C4437, NewCertificates0138.C4438, NewCertificates0138.C4439, NewCertificates0138.C4440, NewCertificates0138.C4441, NewCertificates0138.C4442, NewCertificates0138.C4443, NewCertificates0138.C4444, NewCertificates0138.C4445}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,3)}
theorem doubled_enumeration : ((supportEdges 1527943893264369792).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1527943893264369792 D i ∧ offSum 1527943893264369792 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1527943893264369792 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1527943893264369792 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1527943893264369792 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1527943893264369792 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport095
