import SignedCatalogue
import NewCertificates0049
import NewCertificates0050
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport033
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 3, 5, 4, 6, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0049.C1588, NewCertificates0049.C1589, NewCertificates0049.C1590, NewCertificates0049.C1591, NewCertificates0049.C1592, NewCertificates0049.C1593, NewCertificates0049.C1594, NewCertificates0049.C1595, NewCertificates0049.C1596, NewCertificates0049.C1597, NewCertificates0049.C1598, NewCertificates0049.C1599, NewCertificates0050.C1600, NewCertificates0050.C1601, NewCertificates0050.C1602, NewCertificates0050.C1603, NewCertificates0050.C1604, NewCertificates0050.C1605, NewCertificates0050.C1606, NewCertificates0050.C1607, NewCertificates0050.C1608, NewCertificates0050.C1609, NewCertificates0050.C1610, NewCertificates0050.C1611, NewCertificates0050.C1612, NewCertificates0050.C1613, NewCertificates0050.C1614, NewCertificates0050.C1615, NewCertificates0050.C1616, NewCertificates0050.C1617, NewCertificates0050.C1618, NewCertificates0050.C1619}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 950915279408349312).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 950915279408349312 D i ∧ offSum 950915279408349312 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 950915279408349312 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 950915279408349312 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 950915279408349312 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport033
