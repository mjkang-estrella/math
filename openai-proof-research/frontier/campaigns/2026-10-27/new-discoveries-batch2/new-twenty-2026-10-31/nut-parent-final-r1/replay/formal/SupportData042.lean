import SignedCatalogue
import NewCertificates0065
import NewCertificates0066
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport042
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 6, 5, 1, 4, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0065.C2090, NewCertificates0065.C2091, NewCertificates0065.C2092, NewCertificates0065.C2093, NewCertificates0065.C2094, NewCertificates0065.C2095, NewCertificates0065.C2096, NewCertificates0065.C2097, NewCertificates0065.C2098, NewCertificates0065.C2099, NewCertificates0065.C2100, NewCertificates0065.C2101, NewCertificates0065.C2102, NewCertificates0065.C2103, NewCertificates0065.C2104, NewCertificates0065.C2105, NewCertificates0065.C2106, NewCertificates0065.C2107, NewCertificates0065.C2108, NewCertificates0065.C2109, NewCertificates0065.C2110, NewCertificates0065.C2111, NewCertificates0066.C2112, NewCertificates0066.C2113, NewCertificates0066.C2114, NewCertificates0066.C2115, NewCertificates0066.C2116, NewCertificates0066.C2117, NewCertificates0066.C2118, NewCertificates0066.C2119, NewCertificates0066.C2120, NewCertificates0066.C2121, NewCertificates0066.C2122, NewCertificates0066.C2123, NewCertificates0066.C2124, NewCertificates0066.C2125, NewCertificates0066.C2126, NewCertificates0066.C2127, NewCertificates0066.C2128, NewCertificates0066.C2129, NewCertificates0066.C2130, NewCertificates0066.C2131, NewCertificates0066.C2132, NewCertificates0066.C2133, NewCertificates0066.C2134, NewCertificates0066.C2135, NewCertificates0066.C2136, NewCertificates0066.C2137}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,4)}
theorem doubled_enumeration : ((supportEdges 5305900225323352192).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5305900225323352192 D i ∧ offSum 5305900225323352192 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 5305900225323352192 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5305900225323352192 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5305900225323352192 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5305900225323352192 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport042
