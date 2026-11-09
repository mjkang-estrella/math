import SignedCatalogue
import NewCertificates0045
import NewCertificates0046
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport030
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 4, 6, 5, 1, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0045.C1468, NewCertificates0045.C1469, NewCertificates0045.C1470, NewCertificates0045.C1471, NewCertificates0046.C1472, NewCertificates0046.C1473, NewCertificates0046.C1474, NewCertificates0046.C1475, NewCertificates0046.C1476, NewCertificates0046.C1477, NewCertificates0046.C1478, NewCertificates0046.C1479, NewCertificates0046.C1480, NewCertificates0046.C1481, NewCertificates0046.C1482, NewCertificates0046.C1483, NewCertificates0046.C1484, NewCertificates0046.C1485, NewCertificates0046.C1486, NewCertificates0046.C1487, NewCertificates0046.C1488, NewCertificates0046.C1489, NewCertificates0046.C1490, NewCertificates0046.C1491, NewCertificates0046.C1492, NewCertificates0046.C1493, NewCertificates0046.C1494, NewCertificates0046.C1495, NewCertificates0046.C1496, NewCertificates0046.C1497, NewCertificates0046.C1498, NewCertificates0046.C1499}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1813354883993059456).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1813354883993059456 D i ∧ offSum 1813354883993059456 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1813354883993059456 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1813354883993059456 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1813354883993059456 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport030
