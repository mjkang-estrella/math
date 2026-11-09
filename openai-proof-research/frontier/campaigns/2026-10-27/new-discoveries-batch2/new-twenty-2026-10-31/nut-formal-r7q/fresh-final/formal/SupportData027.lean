import SignedCatalogue
import NewCertificates0040
import NewCertificates0041
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport027
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 4, 5, 3, 6, 2, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0040.C1292, NewCertificates0040.C1293, NewCertificates0040.C1294, NewCertificates0040.C1295, NewCertificates0040.C1296, NewCertificates0040.C1297, NewCertificates0040.C1298, NewCertificates0040.C1299, NewCertificates0040.C1300, NewCertificates0040.C1301, NewCertificates0040.C1302, NewCertificates0040.C1303, NewCertificates0040.C1304, NewCertificates0040.C1305, NewCertificates0040.C1306, NewCertificates0040.C1307, NewCertificates0040.C1308, NewCertificates0040.C1309, NewCertificates0040.C1310, NewCertificates0040.C1311, NewCertificates0041.C1312, NewCertificates0041.C1313, NewCertificates0041.C1314, NewCertificates0041.C1315, NewCertificates0041.C1316, NewCertificates0041.C1317, NewCertificates0041.C1318, NewCertificates0041.C1319, NewCertificates0041.C1320, NewCertificates0041.C1321, NewCertificates0041.C1322, NewCertificates0041.C1323}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 3545112220237054080).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 3545112220237054080 D i ∧ offSum 3545112220237054080 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 3545112220237054080 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 3545112220237054080 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 3545112220237054080 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport027
