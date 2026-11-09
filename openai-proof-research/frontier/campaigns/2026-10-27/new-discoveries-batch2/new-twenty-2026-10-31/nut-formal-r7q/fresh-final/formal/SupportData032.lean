import SignedCatalogue
import NewCertificates0047
import NewCertificates0048
import NewCertificates0049
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport032
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 3, 5, 4, 6, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0047.C1532, NewCertificates0047.C1533, NewCertificates0047.C1534, NewCertificates0047.C1535, NewCertificates0048.C1536, NewCertificates0048.C1537, NewCertificates0048.C1538, NewCertificates0048.C1539, NewCertificates0048.C1540, NewCertificates0048.C1541, NewCertificates0048.C1542, NewCertificates0048.C1543, NewCertificates0048.C1544, NewCertificates0048.C1545, NewCertificates0048.C1546, NewCertificates0048.C1547, NewCertificates0048.C1548, NewCertificates0048.C1549, NewCertificates0048.C1550, NewCertificates0048.C1551, NewCertificates0048.C1552, NewCertificates0048.C1553, NewCertificates0048.C1554, NewCertificates0048.C1555, NewCertificates0048.C1556, NewCertificates0048.C1557, NewCertificates0048.C1558, NewCertificates0048.C1559, NewCertificates0048.C1560, NewCertificates0048.C1561, NewCertificates0048.C1562, NewCertificates0048.C1563, NewCertificates0048.C1564, NewCertificates0048.C1565, NewCertificates0048.C1566, NewCertificates0048.C1567, NewCertificates0049.C1568, NewCertificates0049.C1569, NewCertificates0049.C1570, NewCertificates0049.C1571, NewCertificates0049.C1572, NewCertificates0049.C1573, NewCertificates0049.C1574, NewCertificates0049.C1575, NewCertificates0049.C1576, NewCertificates0049.C1577, NewCertificates0049.C1578, NewCertificates0049.C1579, NewCertificates0049.C1580, NewCertificates0049.C1581, NewCertificates0049.C1582, NewCertificates0049.C1583, NewCertificates0049.C1584, NewCertificates0049.C1585, NewCertificates0049.C1586, NewCertificates0049.C1587}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 950897549783351424).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 950897549783351424 D i ∧ offSum 950897549783351424 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 950897549783351424 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 950897549783351424 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 950897549783351424 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 950897549783351424 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 950897549783351424 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 950897549783351424 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport032
