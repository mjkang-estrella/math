import SignedCatalogue
import NewCertificates0192
import NewCertificates0193
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport129
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 4, 1, 3, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0192.C6164, NewCertificates0192.C6165, NewCertificates0192.C6166, NewCertificates0192.C6167, NewCertificates0192.C6168, NewCertificates0192.C6169, NewCertificates0192.C6170, NewCertificates0192.C6171, NewCertificates0192.C6172, NewCertificates0192.C6173, NewCertificates0192.C6174, NewCertificates0192.C6175, NewCertificates0193.C6176, NewCertificates0193.C6177, NewCertificates0193.C6178, NewCertificates0193.C6179, NewCertificates0193.C6180, NewCertificates0193.C6181, NewCertificates0193.C6182, NewCertificates0193.C6183, NewCertificates0193.C6184, NewCertificates0193.C6185, NewCertificates0193.C6186, NewCertificates0193.C6187, NewCertificates0193.C6188, NewCertificates0193.C6189, NewCertificates0193.C6190, NewCertificates0193.C6191, NewCertificates0193.C6192, NewCertificates0193.C6193, NewCertificates0193.C6194, NewCertificates0193.C6195}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 1375034811215290560).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1375034811215290560 D i ∧ offSum 1375034811215290560 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1375034811215290560 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1375034811215290560 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1375034811215290560 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1375034811215290560 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport129
