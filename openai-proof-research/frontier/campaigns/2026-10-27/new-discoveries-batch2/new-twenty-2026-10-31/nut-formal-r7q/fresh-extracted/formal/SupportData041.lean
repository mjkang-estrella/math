import SignedCatalogue
import NewCertificates0063
import NewCertificates0064
import NewCertificates0065
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport041
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 5, 6, 1, 4, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 4, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0063.C2042, NewCertificates0063.C2043, NewCertificates0063.C2044, NewCertificates0063.C2045, NewCertificates0063.C2046, NewCertificates0063.C2047, NewCertificates0064.C2048, NewCertificates0064.C2049, NewCertificates0064.C2050, NewCertificates0064.C2051, NewCertificates0064.C2052, NewCertificates0064.C2053, NewCertificates0064.C2054, NewCertificates0064.C2055, NewCertificates0064.C2056, NewCertificates0064.C2057, NewCertificates0064.C2058, NewCertificates0064.C2059, NewCertificates0064.C2060, NewCertificates0064.C2061, NewCertificates0064.C2062, NewCertificates0064.C2063, NewCertificates0064.C2064, NewCertificates0064.C2065, NewCertificates0064.C2066, NewCertificates0064.C2067, NewCertificates0064.C2068, NewCertificates0064.C2069, NewCertificates0064.C2070, NewCertificates0064.C2071, NewCertificates0064.C2072, NewCertificates0064.C2073, NewCertificates0064.C2074, NewCertificates0064.C2075, NewCertificates0064.C2076, NewCertificates0064.C2077, NewCertificates0064.C2078, NewCertificates0064.C2079, NewCertificates0065.C2080, NewCertificates0065.C2081, NewCertificates0065.C2082, NewCertificates0065.C2083, NewCertificates0065.C2084, NewCertificates0065.C2085, NewCertificates0065.C2086, NewCertificates0065.C2087, NewCertificates0065.C2088, NewCertificates0065.C2089}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,4)}
theorem doubled_enumeration : ((supportEdges 2968655301459329152).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2968655301459329152 D i ∧ offSum 2968655301459329152 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 2968655301459329152 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2968655301459329152 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2968655301459329152 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2968655301459329152 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport041
