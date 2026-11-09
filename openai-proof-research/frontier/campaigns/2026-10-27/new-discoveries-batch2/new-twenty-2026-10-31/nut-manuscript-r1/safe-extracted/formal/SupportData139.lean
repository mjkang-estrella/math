import SignedCatalogue
import NewCertificates0202
import NewCertificates0203
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport139
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 3, 4, 5, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 3, 4, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0202.C6484, NewCertificates0202.C6485, NewCertificates0202.C6486, NewCertificates0202.C6487, NewCertificates0202.C6488, NewCertificates0202.C6489, NewCertificates0202.C6490, NewCertificates0202.C6491, NewCertificates0202.C6492, NewCertificates0202.C6493, NewCertificates0202.C6494, NewCertificates0202.C6495, NewCertificates0203.C6496, NewCertificates0203.C6497, NewCertificates0203.C6498, NewCertificates0203.C6499, NewCertificates0203.C6500, NewCertificates0203.C6501, NewCertificates0203.C6502, NewCertificates0203.C6503, NewCertificates0203.C6504, NewCertificates0203.C6505, NewCertificates0203.C6506, NewCertificates0203.C6507, NewCertificates0203.C6508, NewCertificates0203.C6509, NewCertificates0203.C6510, NewCertificates0203.C6511, NewCertificates0203.C6512, NewCertificates0203.C6513, NewCertificates0203.C6514, NewCertificates0203.C6515}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 5009438929096028352).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5009438929096028352 D i ∧ offSum 5009438929096028352 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 5009438929096028352 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5009438929096028352 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5009438929096028352 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport139
