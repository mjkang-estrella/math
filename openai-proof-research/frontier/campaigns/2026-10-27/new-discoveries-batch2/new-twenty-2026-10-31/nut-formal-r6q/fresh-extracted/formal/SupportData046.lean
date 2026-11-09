import SignedCatalogue
import NewCertificates0070
import NewCertificates0071
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport046
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 3, 4, 5, 6, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0070.C2266, NewCertificates0070.C2267, NewCertificates0070.C2268, NewCertificates0070.C2269, NewCertificates0070.C2270, NewCertificates0070.C2271, NewCertificates0071.C2272, NewCertificates0071.C2273, NewCertificates0071.C2274, NewCertificates0071.C2275, NewCertificates0071.C2276, NewCertificates0071.C2277, NewCertificates0071.C2278, NewCertificates0071.C2279, NewCertificates0071.C2280, NewCertificates0071.C2281, NewCertificates0071.C2282, NewCertificates0071.C2283, NewCertificates0071.C2284, NewCertificates0071.C2285, NewCertificates0071.C2286, NewCertificates0071.C2287, NewCertificates0071.C2288, NewCertificates0071.C2289, NewCertificates0071.C2290, NewCertificates0071.C2291, NewCertificates0071.C2292, NewCertificates0071.C2293, NewCertificates0071.C2294, NewCertificates0071.C2295, NewCertificates0071.C2296, NewCertificates0071.C2297}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 950906363594162304).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 950906363594162304 D i ∧ offSum 950906363594162304 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 950906363594162304 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 950906363594162304 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 950906363594162304 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport046
