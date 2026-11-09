import SignedCatalogue
import NewCertificates0240
import NewCertificates0241
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport164
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 6, 7, 2, 4, 1, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 0, 1, 1, 2, 2]
def matrices : Finset QuotientMatrix := {NewCertificates0240.C7684, NewCertificates0240.C7685, NewCertificates0240.C7686, NewCertificates0240.C7687, NewCertificates0240.C7688, NewCertificates0240.C7689, NewCertificates0240.C7690, NewCertificates0240.C7691, NewCertificates0240.C7692, NewCertificates0240.C7693, NewCertificates0240.C7694, NewCertificates0240.C7695, NewCertificates0240.C7696, NewCertificates0240.C7697, NewCertificates0240.C7698, NewCertificates0240.C7699, NewCertificates0240.C7700, NewCertificates0240.C7701, NewCertificates0240.C7702, NewCertificates0240.C7703, NewCertificates0240.C7704, NewCertificates0240.C7705, NewCertificates0240.C7706, NewCertificates0240.C7707, NewCertificates0240.C7708, NewCertificates0240.C7709, NewCertificates0240.C7710, NewCertificates0240.C7711, NewCertificates0241.C7712, NewCertificates0241.C7713, NewCertificates0241.C7714, NewCertificates0241.C7715}
def U0 : QuotientMatrix := !![0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 507522654562472160).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 507522654562472160 D i ∧ offSum 507522654562472160 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 507522654562472160 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 507522654562472160 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 507522654562472160 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport164
