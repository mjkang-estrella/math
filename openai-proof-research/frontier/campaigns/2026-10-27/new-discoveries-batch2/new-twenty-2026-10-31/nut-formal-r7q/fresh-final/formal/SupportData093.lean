import SignedCatalogue
import NewCertificates0134
import NewCertificates0135
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport093
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 4, 2, 5, 1, 6] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0134.C4294, NewCertificates0134.C4295, NewCertificates0134.C4296, NewCertificates0134.C4297, NewCertificates0134.C4298, NewCertificates0134.C4299, NewCertificates0134.C4300, NewCertificates0134.C4301, NewCertificates0134.C4302, NewCertificates0134.C4303, NewCertificates0134.C4304, NewCertificates0134.C4305, NewCertificates0134.C4306, NewCertificates0134.C4307, NewCertificates0134.C4308, NewCertificates0134.C4309, NewCertificates0134.C4310, NewCertificates0134.C4311, NewCertificates0134.C4312, NewCertificates0134.C4313, NewCertificates0134.C4314, NewCertificates0134.C4315, NewCertificates0134.C4316, NewCertificates0134.C4317, NewCertificates0134.C4318, NewCertificates0134.C4319, NewCertificates0135.C4320, NewCertificates0135.C4321, NewCertificates0135.C4322, NewCertificates0135.C4323, NewCertificates0135.C4324, NewCertificates0135.C4325}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1815597998645203072).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1815597998645203072 D i ∧ offSum 1815597998645203072 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1815597998645203072 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1815597998645203072 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1815597998645203072 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport093
