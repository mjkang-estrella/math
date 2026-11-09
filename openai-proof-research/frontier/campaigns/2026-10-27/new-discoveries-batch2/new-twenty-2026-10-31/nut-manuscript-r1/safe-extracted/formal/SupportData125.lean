import SignedCatalogue
import NewCertificates0189
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport125
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 4, 1, 5, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0189.C6052, NewCertificates0189.C6053, NewCertificates0189.C6054, NewCertificates0189.C6055, NewCertificates0189.C6056, NewCertificates0189.C6057, NewCertificates0189.C6058, NewCertificates0189.C6059, NewCertificates0189.C6060, NewCertificates0189.C6061, NewCertificates0189.C6062, NewCertificates0189.C6063, NewCertificates0189.C6064, NewCertificates0189.C6065, NewCertificates0189.C6066, NewCertificates0189.C6067}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 2528078825671139520).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2528078825671139520 D i ∧ offSum 2528078825671139520 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 2528078825671139520 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2528078825671139520 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2528078825671139520 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport125
