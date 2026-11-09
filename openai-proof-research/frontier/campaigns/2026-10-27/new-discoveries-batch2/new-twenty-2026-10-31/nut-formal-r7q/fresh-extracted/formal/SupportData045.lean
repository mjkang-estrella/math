import SignedCatalogue
import NewCertificates0069
import NewCertificates0070
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport045
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 4, 6, 2, 3, 1, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0069.C2234, NewCertificates0069.C2235, NewCertificates0069.C2236, NewCertificates0069.C2237, NewCertificates0069.C2238, NewCertificates0069.C2239, NewCertificates0070.C2240, NewCertificates0070.C2241, NewCertificates0070.C2242, NewCertificates0070.C2243, NewCertificates0070.C2244, NewCertificates0070.C2245, NewCertificates0070.C2246, NewCertificates0070.C2247, NewCertificates0070.C2248, NewCertificates0070.C2249, NewCertificates0070.C2250, NewCertificates0070.C2251, NewCertificates0070.C2252, NewCertificates0070.C2253, NewCertificates0070.C2254, NewCertificates0070.C2255, NewCertificates0070.C2256, NewCertificates0070.C2257, NewCertificates0070.C2258, NewCertificates0070.C2259, NewCertificates0070.C2260, NewCertificates0070.C2261, NewCertificates0070.C2262, NewCertificates0070.C2263, NewCertificates0070.C2264, NewCertificates0070.C2265}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 5882348228286890112).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5882348228286890112 D i ∧ offSum 5882348228286890112 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 5882348228286890112 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5882348228286890112 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5882348228286890112 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport045
