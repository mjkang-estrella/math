import SignedCatalogue
import NewCertificates0243
import NewCertificates0244
import NewCertificates0245
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport168
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 4, 3, 5, 6, 7, 1, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 3, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0243.C7804, NewCertificates0243.C7805, NewCertificates0243.C7806, NewCertificates0243.C7807, NewCertificates0244.C7808, NewCertificates0244.C7809, NewCertificates0244.C7810, NewCertificates0244.C7811, NewCertificates0244.C7812, NewCertificates0244.C7813, NewCertificates0244.C7814, NewCertificates0244.C7815, NewCertificates0244.C7816, NewCertificates0244.C7817, NewCertificates0244.C7818, NewCertificates0244.C7819, NewCertificates0244.C7820, NewCertificates0244.C7821, NewCertificates0244.C7822, NewCertificates0244.C7823, NewCertificates0244.C7824, NewCertificates0244.C7825, NewCertificates0244.C7826, NewCertificates0244.C7827, NewCertificates0244.C7828, NewCertificates0244.C7829, NewCertificates0244.C7830, NewCertificates0244.C7831, NewCertificates0244.C7832, NewCertificates0244.C7833, NewCertificates0244.C7834, NewCertificates0244.C7835, NewCertificates0244.C7836, NewCertificates0244.C7837, NewCertificates0244.C7838, NewCertificates0244.C7839, NewCertificates0245.C7840, NewCertificates0245.C7841, NewCertificates0245.C7842, NewCertificates0245.C7843}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 2, 1, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(0,4)}
theorem doubled_enumeration : ((supportEdges 2749104564354465808).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2749104564354465808 D i ∧ offSum 2749104564354465808 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 2749104564354465808 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2749104564354465808 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 2749104564354465808 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2749104564354465808 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2749104564354465808 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport168
