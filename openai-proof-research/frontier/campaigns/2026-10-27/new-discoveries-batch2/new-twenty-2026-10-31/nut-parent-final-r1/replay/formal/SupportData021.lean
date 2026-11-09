import SignedCatalogue
import NewCertificates0030
import NewCertificates0031
import NewCertificates0032
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport021
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 3, 6, 5, 1, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0030.C984, NewCertificates0030.C985, NewCertificates0030.C986, NewCertificates0030.C987, NewCertificates0030.C988, NewCertificates0030.C989, NewCertificates0030.C990, NewCertificates0030.C991, NewCertificates0031.C992, NewCertificates0031.C993, NewCertificates0031.C994, NewCertificates0031.C995, NewCertificates0031.C996, NewCertificates0031.C997, NewCertificates0031.C998, NewCertificates0031.C999, NewCertificates0031.C1000, NewCertificates0031.C1001, NewCertificates0031.C1002, NewCertificates0031.C1003, NewCertificates0031.C1004, NewCertificates0031.C1005, NewCertificates0031.C1006, NewCertificates0031.C1007, NewCertificates0031.C1008, NewCertificates0031.C1009, NewCertificates0031.C1010, NewCertificates0031.C1011, NewCertificates0031.C1012, NewCertificates0031.C1013, NewCertificates0031.C1014, NewCertificates0031.C1015, NewCertificates0031.C1016, NewCertificates0031.C1017, NewCertificates0031.C1018, NewCertificates0031.C1019, NewCertificates0031.C1020, NewCertificates0031.C1021, NewCertificates0031.C1022, NewCertificates0031.C1023, NewCertificates0032.C1024, NewCertificates0032.C1025, NewCertificates0032.C1026, NewCertificates0032.C1027, NewCertificates0032.C1028, NewCertificates0032.C1029, NewCertificates0032.C1030, NewCertificates0032.C1031}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(4,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,5)}
theorem doubled_enumeration : ((supportEdges 942967975273578624).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 942967975273578624 D i ∧ offSum 942967975273578624 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 942967975273578624 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 942967975273578624 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 942967975273578624 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 942967975273578624 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 942967975273578624 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport021
