import SignedCatalogue
import NewCertificates0071
import NewCertificates0072
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport047
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 6, 4, 5, 1, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0071.C2298, NewCertificates0071.C2299, NewCertificates0071.C2300, NewCertificates0071.C2301, NewCertificates0071.C2302, NewCertificates0071.C2303, NewCertificates0072.C2304, NewCertificates0072.C2305, NewCertificates0072.C2306, NewCertificates0072.C2307, NewCertificates0072.C2308, NewCertificates0072.C2309, NewCertificates0072.C2310, NewCertificates0072.C2311, NewCertificates0072.C2312, NewCertificates0072.C2313, NewCertificates0072.C2314, NewCertificates0072.C2315, NewCertificates0072.C2316, NewCertificates0072.C2317, NewCertificates0072.C2318, NewCertificates0072.C2319, NewCertificates0072.C2320, NewCertificates0072.C2321, NewCertificates0072.C2322, NewCertificates0072.C2323, NewCertificates0072.C2324, NewCertificates0072.C2325, NewCertificates0072.C2326, NewCertificates0072.C2327, NewCertificates0072.C2328, NewCertificates0072.C2329}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 5010848512597835904).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5010848512597835904 D i ∧ offSum 5010848512597835904 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 5010848512597835904 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5010848512597835904 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5010848512597835904 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport047
