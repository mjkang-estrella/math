import SignedCatalogue
import NewCertificates0016
import NewCertificates0017
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport011
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 2, 6, 3, 4, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 4, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0016.C512, NewCertificates0016.C513, NewCertificates0016.C514, NewCertificates0016.C515, NewCertificates0016.C516, NewCertificates0016.C517, NewCertificates0016.C518, NewCertificates0016.C519, NewCertificates0016.C520, NewCertificates0016.C521, NewCertificates0016.C522, NewCertificates0016.C523, NewCertificates0016.C524, NewCertificates0016.C525, NewCertificates0016.C526, NewCertificates0016.C527, NewCertificates0016.C528, NewCertificates0016.C529, NewCertificates0016.C530, NewCertificates0016.C531, NewCertificates0016.C532, NewCertificates0016.C533, NewCertificates0016.C534, NewCertificates0016.C535, NewCertificates0016.C536, NewCertificates0016.C537, NewCertificates0016.C538, NewCertificates0016.C539, NewCertificates0016.C540, NewCertificates0016.C541, NewCertificates0016.C542, NewCertificates0016.C543, NewCertificates0017.C544, NewCertificates0017.C545, NewCertificates0017.C546, NewCertificates0017.C547, NewCertificates0017.C548, NewCertificates0017.C549, NewCertificates0017.C550, NewCertificates0017.C551, NewCertificates0017.C552, NewCertificates0017.C553, NewCertificates0017.C554, NewCertificates0017.C555, NewCertificates0017.C556, NewCertificates0017.C557, NewCertificates0017.C558, NewCertificates0017.C559}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(4,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,5)}
theorem doubled_enumeration : ((supportEdges 512311259832549504).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 512311259832549504 D i ∧ offSum 512311259832549504 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 512311259832549504 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 512311259832549504 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 512311259832549504 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 512311259832549504 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 512311259832549504 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport011
