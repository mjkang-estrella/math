import SignedCatalogue
import NewCertificates0058
import NewCertificates0059
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport036
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 4, 5, 3, 6, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0058.C1866, NewCertificates0058.C1867, NewCertificates0058.C1868, NewCertificates0058.C1869, NewCertificates0058.C1870, NewCertificates0058.C1871, NewCertificates0058.C1872, NewCertificates0058.C1873, NewCertificates0058.C1874, NewCertificates0058.C1875, NewCertificates0058.C1876, NewCertificates0058.C1877, NewCertificates0058.C1878, NewCertificates0058.C1879, NewCertificates0058.C1880, NewCertificates0058.C1881, NewCertificates0058.C1882, NewCertificates0058.C1883, NewCertificates0058.C1884, NewCertificates0058.C1885, NewCertificates0058.C1886, NewCertificates0058.C1887, NewCertificates0059.C1888, NewCertificates0059.C1889, NewCertificates0059.C1890, NewCertificates0059.C1891, NewCertificates0059.C1892, NewCertificates0059.C1893, NewCertificates0059.C1894, NewCertificates0059.C1895, NewCertificates0059.C1896, NewCertificates0059.C1897}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1525124505702252672).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1525124505702252672 D i ∧ offSum 1525124505702252672 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1525124505702252672 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1525124505702252672 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1525124505702252672 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport036
