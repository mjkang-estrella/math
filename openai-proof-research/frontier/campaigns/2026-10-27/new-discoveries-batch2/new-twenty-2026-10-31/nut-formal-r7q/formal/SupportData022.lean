import SignedCatalogue
import NewCertificates0032
import NewCertificates0033
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport022
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 4, 6, 3, 5, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0032.C1032, NewCertificates0032.C1033, NewCertificates0032.C1034, NewCertificates0032.C1035, NewCertificates0032.C1036, NewCertificates0032.C1037, NewCertificates0032.C1038, NewCertificates0032.C1039, NewCertificates0032.C1040, NewCertificates0032.C1041, NewCertificates0032.C1042, NewCertificates0032.C1043, NewCertificates0032.C1044, NewCertificates0032.C1045, NewCertificates0032.C1046, NewCertificates0032.C1047, NewCertificates0032.C1048, NewCertificates0032.C1049, NewCertificates0032.C1050, NewCertificates0032.C1051, NewCertificates0032.C1052, NewCertificates0032.C1053, NewCertificates0032.C1054, NewCertificates0032.C1055, NewCertificates0033.C1056, NewCertificates0033.C1057, NewCertificates0033.C1058, NewCertificates0033.C1059, NewCertificates0033.C1060, NewCertificates0033.C1061, NewCertificates0033.C1062, NewCertificates0033.C1063}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1524003003307147392).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1524003003307147392 D i ∧ offSum 1524003003307147392 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1524003003307147392 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1524003003307147392 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1524003003307147392 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport022
