import SignedCatalogue
import NewCertificates0243
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport167
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 4, 5, 3, 6, 7, 1, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0243.C7780, NewCertificates0243.C7781, NewCertificates0243.C7782, NewCertificates0243.C7783, NewCertificates0243.C7784, NewCertificates0243.C7785, NewCertificates0243.C7786, NewCertificates0243.C7787, NewCertificates0243.C7788, NewCertificates0243.C7789, NewCertificates0243.C7790, NewCertificates0243.C7791, NewCertificates0243.C7792, NewCertificates0243.C7793, NewCertificates0243.C7794, NewCertificates0243.C7795, NewCertificates0243.C7796, NewCertificates0243.C7797, NewCertificates0243.C7798, NewCertificates0243.C7799, NewCertificates0243.C7800, NewCertificates0243.C7801, NewCertificates0243.C7802, NewCertificates0243.C7803}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 1, 0, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 2, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(0,4)}
theorem doubled_enumeration : ((supportEdges 1019599267100147728).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1019599267100147728 D i ∧ offSum 1019599267100147728 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1019599267100147728 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1019599267100147728 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1019599267100147728 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1019599267100147728 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport167
