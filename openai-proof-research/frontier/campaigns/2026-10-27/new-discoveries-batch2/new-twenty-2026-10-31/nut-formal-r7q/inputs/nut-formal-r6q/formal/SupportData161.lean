import SignedCatalogue
import NewCertificates0236
import NewCertificates0237
import NewCertificates0238
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport161
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 6, 4, 7, 1, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 3, 4, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0236.C7572, NewCertificates0236.C7573, NewCertificates0236.C7574, NewCertificates0236.C7575, NewCertificates0236.C7576, NewCertificates0236.C7577, NewCertificates0236.C7578, NewCertificates0236.C7579, NewCertificates0236.C7580, NewCertificates0236.C7581, NewCertificates0236.C7582, NewCertificates0236.C7583, NewCertificates0237.C7584, NewCertificates0237.C7585, NewCertificates0237.C7586, NewCertificates0237.C7587, NewCertificates0237.C7588, NewCertificates0237.C7589, NewCertificates0237.C7590, NewCertificates0237.C7591, NewCertificates0237.C7592, NewCertificates0237.C7593, NewCertificates0237.C7594, NewCertificates0237.C7595, NewCertificates0237.C7596, NewCertificates0237.C7597, NewCertificates0237.C7598, NewCertificates0237.C7599, NewCertificates0237.C7600, NewCertificates0237.C7601, NewCertificates0237.C7602, NewCertificates0237.C7603, NewCertificates0237.C7604, NewCertificates0237.C7605, NewCertificates0237.C7606, NewCertificates0237.C7607, NewCertificates0237.C7608, NewCertificates0237.C7609, NewCertificates0237.C7610, NewCertificates0237.C7611, NewCertificates0237.C7612, NewCertificates0237.C7613, NewCertificates0237.C7614, NewCertificates0237.C7615, NewCertificates0238.C7616, NewCertificates0238.C7617, NewCertificates0238.C7618, NewCertificates0238.C7619}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 1, 2, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,3)}
theorem doubled_enumeration : ((supportEdges 1599149365317372000).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1599149365317372000 D i ∧ offSum 1599149365317372000 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 1599149365317372000 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1599149365317372000 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 1599149365317372000 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1599149365317372000 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1599149365317372000 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport161
