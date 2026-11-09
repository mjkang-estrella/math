import SignedCatalogue
import NewCertificates0138
import NewCertificates0139
import NewCertificates0140
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport096
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 4, 1, 5, 6, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0138.C4446, NewCertificates0138.C4447, NewCertificates0139.C4448, NewCertificates0139.C4449, NewCertificates0139.C4450, NewCertificates0139.C4451, NewCertificates0139.C4452, NewCertificates0139.C4453, NewCertificates0139.C4454, NewCertificates0139.C4455, NewCertificates0139.C4456, NewCertificates0139.C4457, NewCertificates0139.C4458, NewCertificates0139.C4459, NewCertificates0139.C4460, NewCertificates0139.C4461, NewCertificates0139.C4462, NewCertificates0139.C4463, NewCertificates0139.C4464, NewCertificates0139.C4465, NewCertificates0139.C4466, NewCertificates0139.C4467, NewCertificates0139.C4468, NewCertificates0139.C4469, NewCertificates0139.C4470, NewCertificates0139.C4471, NewCertificates0139.C4472, NewCertificates0139.C4473, NewCertificates0139.C4474, NewCertificates0139.C4475, NewCertificates0139.C4476, NewCertificates0139.C4477, NewCertificates0139.C4478, NewCertificates0139.C4479, NewCertificates0140.C4480, NewCertificates0140.C4481, NewCertificates0140.C4482, NewCertificates0140.C4483, NewCertificates0140.C4484, NewCertificates0140.C4485, NewCertificates0140.C4486, NewCertificates0140.C4487, NewCertificates0140.C4488, NewCertificates0140.C4489, NewCertificates0140.C4490, NewCertificates0140.C4491, NewCertificates0140.C4492, NewCertificates0140.C4493}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,3)}
theorem doubled_enumeration : ((supportEdges 1816169872973891712).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1816169872973891712 D i ∧ offSum 1816169872973891712 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1816169872973891712 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1816169872973891712 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1816169872973891712 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1816169872973891712 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport096
