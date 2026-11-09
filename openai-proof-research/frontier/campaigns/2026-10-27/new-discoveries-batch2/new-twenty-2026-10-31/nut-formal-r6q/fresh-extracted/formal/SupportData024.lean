import SignedCatalogue
import NewCertificates0036
import NewCertificates0037
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport024
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 4, 6, 5, 1, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0036.C1156, NewCertificates0036.C1157, NewCertificates0036.C1158, NewCertificates0036.C1159, NewCertificates0036.C1160, NewCertificates0036.C1161, NewCertificates0036.C1162, NewCertificates0036.C1163, NewCertificates0036.C1164, NewCertificates0036.C1165, NewCertificates0036.C1166, NewCertificates0036.C1167, NewCertificates0036.C1168, NewCertificates0036.C1169, NewCertificates0036.C1170, NewCertificates0036.C1171, NewCertificates0036.C1172, NewCertificates0036.C1173, NewCertificates0036.C1174, NewCertificates0036.C1175, NewCertificates0036.C1176, NewCertificates0036.C1177, NewCertificates0036.C1178, NewCertificates0036.C1179, NewCertificates0036.C1180, NewCertificates0036.C1181, NewCertificates0036.C1182, NewCertificates0036.C1183, NewCertificates0037.C1184, NewCertificates0037.C1185, NewCertificates0037.C1186, NewCertificates0037.C1187}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1813354849364885632).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1813354849364885632 D i ∧ offSum 1813354849364885632 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1813354849364885632 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1813354849364885632 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1813354849364885632 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport024
