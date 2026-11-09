import SignedCatalogue
import NewCertificates0046
import NewCertificates0047
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport031
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 4, 5, 6, 3, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0046.C1500, NewCertificates0046.C1501, NewCertificates0046.C1502, NewCertificates0046.C1503, NewCertificates0047.C1504, NewCertificates0047.C1505, NewCertificates0047.C1506, NewCertificates0047.C1507, NewCertificates0047.C1508, NewCertificates0047.C1509, NewCertificates0047.C1510, NewCertificates0047.C1511, NewCertificates0047.C1512, NewCertificates0047.C1513, NewCertificates0047.C1514, NewCertificates0047.C1515, NewCertificates0047.C1516, NewCertificates0047.C1517, NewCertificates0047.C1518, NewCertificates0047.C1519, NewCertificates0047.C1520, NewCertificates0047.C1521, NewCertificates0047.C1522, NewCertificates0047.C1523, NewCertificates0047.C1524, NewCertificates0047.C1525, NewCertificates0047.C1526, NewCertificates0047.C1527, NewCertificates0047.C1528, NewCertificates0047.C1529, NewCertificates0047.C1530, NewCertificates0047.C1531}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1520559574210330752).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1520559574210330752 D i ∧ offSum 1520559574210330752 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1520559574210330752 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1520559574210330752 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1520559574210330752 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport031
