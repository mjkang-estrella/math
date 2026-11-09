import SignedCatalogue
import NewCertificates0059
import NewCertificates0060
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport037
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 4, 5, 3, 6, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0059.C1898, NewCertificates0059.C1899, NewCertificates0059.C1900, NewCertificates0059.C1901, NewCertificates0059.C1902, NewCertificates0059.C1903, NewCertificates0059.C1904, NewCertificates0059.C1905, NewCertificates0059.C1906, NewCertificates0059.C1907, NewCertificates0059.C1908, NewCertificates0059.C1909, NewCertificates0059.C1910, NewCertificates0059.C1911, NewCertificates0059.C1912, NewCertificates0059.C1913, NewCertificates0059.C1914, NewCertificates0059.C1915, NewCertificates0059.C1916, NewCertificates0059.C1917, NewCertificates0059.C1918, NewCertificates0059.C1919, NewCertificates0060.C1920, NewCertificates0060.C1921, NewCertificates0060.C1922, NewCertificates0060.C1923, NewCertificates0060.C1924, NewCertificates0060.C1925, NewCertificates0060.C1926, NewCertificates0060.C1927, NewCertificates0060.C1928, NewCertificates0060.C1929}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1527367646324998272).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1527367646324998272 D i ∧ offSum 1527367646324998272 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1527367646324998272 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1527367646324998272 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1527367646324998272 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport037
