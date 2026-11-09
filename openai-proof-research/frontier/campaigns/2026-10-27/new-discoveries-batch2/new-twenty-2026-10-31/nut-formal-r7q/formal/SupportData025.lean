import SignedCatalogue
import NewCertificates0037
import NewCertificates0038
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport025
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 4, 5, 6, 2, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0037.C1188, NewCertificates0037.C1189, NewCertificates0037.C1190, NewCertificates0037.C1191, NewCertificates0037.C1192, NewCertificates0037.C1193, NewCertificates0037.C1194, NewCertificates0037.C1195, NewCertificates0037.C1196, NewCertificates0037.C1197, NewCertificates0037.C1198, NewCertificates0037.C1199, NewCertificates0037.C1200, NewCertificates0037.C1201, NewCertificates0037.C1202, NewCertificates0037.C1203, NewCertificates0037.C1204, NewCertificates0037.C1205, NewCertificates0037.C1206, NewCertificates0037.C1207, NewCertificates0037.C1208, NewCertificates0037.C1209, NewCertificates0037.C1210, NewCertificates0037.C1211, NewCertificates0037.C1212, NewCertificates0037.C1213, NewCertificates0037.C1214, NewCertificates0037.C1215, NewCertificates0038.C1216, NewCertificates0038.C1217, NewCertificates0038.C1218, NewCertificates0038.C1219}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1808789952501137536).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1808789952501137536 D i ∧ offSum 1808789952501137536 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1808789952501137536 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1808789952501137536 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1808789952501137536 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport025
