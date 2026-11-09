import SignedCatalogue
import NewCertificates0156
import NewCertificates0157
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport107
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 2, 6, 5, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0156.C4998, NewCertificates0156.C4999, NewCertificates0156.C5000, NewCertificates0156.C5001, NewCertificates0156.C5002, NewCertificates0156.C5003, NewCertificates0156.C5004, NewCertificates0156.C5005, NewCertificates0156.C5006, NewCertificates0156.C5007, NewCertificates0156.C5008, NewCertificates0156.C5009, NewCertificates0156.C5010, NewCertificates0156.C5011, NewCertificates0156.C5012, NewCertificates0156.C5013, NewCertificates0156.C5014, NewCertificates0156.C5015, NewCertificates0156.C5016, NewCertificates0156.C5017, NewCertificates0156.C5018, NewCertificates0156.C5019, NewCertificates0156.C5020, NewCertificates0156.C5021, NewCertificates0156.C5022, NewCertificates0156.C5023, NewCertificates0157.C5024, NewCertificates0157.C5025, NewCertificates0157.C5026, NewCertificates0157.C5027, NewCertificates0157.C5028, NewCertificates0157.C5029}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 511752742551864448).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 511752742551864448 D i ∧ offSum 511752742551864448 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 511752742551864448 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 511752742551864448 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 511752742551864448 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport107
