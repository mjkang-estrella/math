import SignedCatalogue
import NewCertificates0044
import NewCertificates0045
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport029
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 5, 4, 2, 6, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0044.C1420, NewCertificates0044.C1421, NewCertificates0044.C1422, NewCertificates0044.C1423, NewCertificates0044.C1424, NewCertificates0044.C1425, NewCertificates0044.C1426, NewCertificates0044.C1427, NewCertificates0044.C1428, NewCertificates0044.C1429, NewCertificates0044.C1430, NewCertificates0044.C1431, NewCertificates0044.C1432, NewCertificates0044.C1433, NewCertificates0044.C1434, NewCertificates0044.C1435, NewCertificates0044.C1436, NewCertificates0044.C1437, NewCertificates0044.C1438, NewCertificates0044.C1439, NewCertificates0045.C1440, NewCertificates0045.C1441, NewCertificates0045.C1442, NewCertificates0045.C1443, NewCertificates0045.C1444, NewCertificates0045.C1445, NewCertificates0045.C1446, NewCertificates0045.C1447, NewCertificates0045.C1448, NewCertificates0045.C1449, NewCertificates0045.C1450, NewCertificates0045.C1451, NewCertificates0045.C1452, NewCertificates0045.C1453, NewCertificates0045.C1454, NewCertificates0045.C1455, NewCertificates0045.C1456, NewCertificates0045.C1457, NewCertificates0045.C1458, NewCertificates0045.C1459, NewCertificates0045.C1460, NewCertificates0045.C1461, NewCertificates0045.C1462, NewCertificates0045.C1463, NewCertificates0045.C1464, NewCertificates0045.C1465, NewCertificates0045.C1466, NewCertificates0045.C1467}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
theorem doubled_enumeration : ((supportEdges 2968650920325300352).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2968650920325300352 D i ∧ offSum 2968650920325300352 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 2968650920325300352 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2968650920325300352 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2968650920325300352 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2968650920325300352 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport029
