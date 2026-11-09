import SignedCatalogue
import NewCertificates0018
import NewCertificates0019
import NewCertificates0020
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport013
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 6, 4, 5, 3, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0018.C592, NewCertificates0018.C593, NewCertificates0018.C594, NewCertificates0018.C595, NewCertificates0018.C596, NewCertificates0018.C597, NewCertificates0018.C598, NewCertificates0018.C599, NewCertificates0018.C600, NewCertificates0018.C601, NewCertificates0018.C602, NewCertificates0018.C603, NewCertificates0018.C604, NewCertificates0018.C605, NewCertificates0018.C606, NewCertificates0018.C607, NewCertificates0019.C608, NewCertificates0019.C609, NewCertificates0019.C610, NewCertificates0019.C611, NewCertificates0019.C612, NewCertificates0019.C613, NewCertificates0019.C614, NewCertificates0019.C615, NewCertificates0019.C616, NewCertificates0019.C617, NewCertificates0019.C618, NewCertificates0019.C619, NewCertificates0019.C620, NewCertificates0019.C621, NewCertificates0019.C622, NewCertificates0019.C623, NewCertificates0019.C624, NewCertificates0019.C625, NewCertificates0019.C626, NewCertificates0019.C627, NewCertificates0019.C628, NewCertificates0019.C629, NewCertificates0019.C630, NewCertificates0019.C631, NewCertificates0019.C632, NewCertificates0019.C633, NewCertificates0019.C634, NewCertificates0019.C635, NewCertificates0019.C636, NewCertificates0019.C637, NewCertificates0019.C638, NewCertificates0019.C639, NewCertificates0020.C640, NewCertificates0020.C641, NewCertificates0020.C642, NewCertificates0020.C643, NewCertificates0020.C644, NewCertificates0020.C645, NewCertificates0020.C646, NewCertificates0020.C647, NewCertificates0020.C648, NewCertificates0020.C649, NewCertificates0020.C650, NewCertificates0020.C651, NewCertificates0020.C652, NewCertificates0020.C653, NewCertificates0020.C654, NewCertificates0020.C655, NewCertificates0020.C656, NewCertificates0020.C657, NewCertificates0020.C658, NewCertificates0020.C659, NewCertificates0020.C660, NewCertificates0020.C661, NewCertificates0020.C662, NewCertificates0020.C663}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 4877473472741146752).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 4877473472741146752 D i ∧ offSum 4877473472741146752 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 4877473472741146752 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 4877473472741146752 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 4877473472741146752 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 4877473472741146752 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 4877473472741146752 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 4877473472741146752 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport013
