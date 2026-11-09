import SignedCatalogue
import NewCertificates0267
import NewCertificates0268
import NewCertificates0269
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport182
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 3, 7, 2, 4, 5, 1, 6] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0267.C8548, NewCertificates0267.C8549, NewCertificates0267.C8550, NewCertificates0267.C8551, NewCertificates0267.C8552, NewCertificates0267.C8553, NewCertificates0267.C8554, NewCertificates0267.C8555, NewCertificates0267.C8556, NewCertificates0267.C8557, NewCertificates0267.C8558, NewCertificates0267.C8559, NewCertificates0267.C8560, NewCertificates0267.C8561, NewCertificates0267.C8562, NewCertificates0267.C8563, NewCertificates0267.C8564, NewCertificates0267.C8565, NewCertificates0267.C8566, NewCertificates0267.C8567, NewCertificates0267.C8568, NewCertificates0267.C8569, NewCertificates0267.C8570, NewCertificates0267.C8571, NewCertificates0267.C8572, NewCertificates0267.C8573, NewCertificates0267.C8574, NewCertificates0267.C8575, NewCertificates0268.C8576, NewCertificates0268.C8577, NewCertificates0268.C8578, NewCertificates0268.C8579, NewCertificates0268.C8580, NewCertificates0268.C8581, NewCertificates0268.C8582, NewCertificates0268.C8583, NewCertificates0268.C8584, NewCertificates0268.C8585, NewCertificates0268.C8586, NewCertificates0268.C8587, NewCertificates0268.C8588, NewCertificates0268.C8589, NewCertificates0268.C8590, NewCertificates0268.C8591, NewCertificates0268.C8592, NewCertificates0268.C8593, NewCertificates0268.C8594, NewCertificates0268.C8595, NewCertificates0268.C8596, NewCertificates0268.C8597, NewCertificates0268.C8598, NewCertificates0268.C8599, NewCertificates0268.C8600, NewCertificates0268.C8601, NewCertificates0268.C8602, NewCertificates0268.C8603, NewCertificates0268.C8604, NewCertificates0268.C8605, NewCertificates0268.C8606, NewCertificates0268.C8607, NewCertificates0269.C8608, NewCertificates0269.C8609, NewCertificates0269.C8610, NewCertificates0269.C8611, NewCertificates0269.C8612, NewCertificates0269.C8613, NewCertificates0269.C8614, NewCertificates0269.C8615, NewCertificates0269.C8616, NewCertificates0269.C8617, NewCertificates0269.C8618, NewCertificates0269.C8619}
def U0 : QuotientMatrix := !![1, 0, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 1, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def U3 : QuotientMatrix := !![0, 0, 0, 2, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def U4 : QuotientMatrix := !![0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 1, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,2)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D3 : Finset (Fin 8 × Fin 8) := {(0,3)}
def D4 : Finset (Fin 8 × Fin 8) := {(0,3), (1,2)}
theorem doubled_enumeration : ((supportEdges 3545125517269812360).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 3545125517269812360 D i ∧ offSum 3545125517269812360 D i ≤ 3) = {D0, D1, D2, D3, D4} := by
  decide +kernel
theorem augmentation0 : augmentation 3545125517269812360 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 3545125517269812360 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 3545125517269812360 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 3545125517269812360 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 3545125517269812360 D4 = U4 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 3545125517269812360 = {U0, U1, U2, U3, U4} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 3545125517269812360 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport182
