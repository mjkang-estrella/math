import SignedCatalogue
import NewCertificates0033
import NewCertificates0034
import NewCertificates0035
import NewCertificates0036
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport023
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 4, 6, 5, 1, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0033.C1064, NewCertificates0033.C1065, NewCertificates0033.C1066, NewCertificates0033.C1067, NewCertificates0033.C1068, NewCertificates0033.C1069, NewCertificates0033.C1070, NewCertificates0033.C1071, NewCertificates0033.C1072, NewCertificates0033.C1073, NewCertificates0033.C1074, NewCertificates0033.C1075, NewCertificates0033.C1076, NewCertificates0033.C1077, NewCertificates0033.C1078, NewCertificates0033.C1079, NewCertificates0033.C1080, NewCertificates0033.C1081, NewCertificates0033.C1082, NewCertificates0033.C1083, NewCertificates0033.C1084, NewCertificates0033.C1085, NewCertificates0033.C1086, NewCertificates0033.C1087, NewCertificates0034.C1088, NewCertificates0034.C1089, NewCertificates0034.C1090, NewCertificates0034.C1091, NewCertificates0034.C1092, NewCertificates0034.C1093, NewCertificates0034.C1094, NewCertificates0034.C1095, NewCertificates0034.C1096, NewCertificates0034.C1097, NewCertificates0034.C1098, NewCertificates0034.C1099, NewCertificates0034.C1100, NewCertificates0034.C1101, NewCertificates0034.C1102, NewCertificates0034.C1103, NewCertificates0034.C1104, NewCertificates0034.C1105, NewCertificates0034.C1106, NewCertificates0034.C1107, NewCertificates0034.C1108, NewCertificates0034.C1109, NewCertificates0034.C1110, NewCertificates0034.C1111, NewCertificates0034.C1112, NewCertificates0034.C1113, NewCertificates0034.C1114, NewCertificates0034.C1115, NewCertificates0034.C1116, NewCertificates0034.C1117, NewCertificates0034.C1118, NewCertificates0034.C1119, NewCertificates0035.C1120, NewCertificates0035.C1121, NewCertificates0035.C1122, NewCertificates0035.C1123, NewCertificates0035.C1124, NewCertificates0035.C1125, NewCertificates0035.C1126, NewCertificates0035.C1127, NewCertificates0035.C1128, NewCertificates0035.C1129, NewCertificates0035.C1130, NewCertificates0035.C1131, NewCertificates0035.C1132, NewCertificates0035.C1133, NewCertificates0035.C1134, NewCertificates0035.C1135, NewCertificates0035.C1136, NewCertificates0035.C1137, NewCertificates0035.C1138, NewCertificates0035.C1139, NewCertificates0035.C1140, NewCertificates0035.C1141, NewCertificates0035.C1142, NewCertificates0035.C1143, NewCertificates0035.C1144, NewCertificates0035.C1145, NewCertificates0035.C1146, NewCertificates0035.C1147, NewCertificates0035.C1148, NewCertificates0035.C1149, NewCertificates0035.C1150, NewCertificates0035.C1151, NewCertificates0036.C1152, NewCertificates0036.C1153, NewCertificates0036.C1154, NewCertificates0036.C1155}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 2, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 2, 0, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def U5 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 2, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def U6 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def U7 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 2, 0, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def U8 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,6)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,6), (2,5)}
def D4 : Finset (Fin 8 × Fin 8) := {(4,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(1,6), (4,5)}
def D6 : Finset (Fin 8 × Fin 8) := {(3,6)}
def D7 : Finset (Fin 8 × Fin 8) := {(2,5), (3,6)}
def D8 : Finset (Fin 8 × Fin 8) := {(3,6), (4,5)}
theorem doubled_enumeration : ((supportEdges 1804277281365966976).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1804277281365966976 D i ∧ offSum 1804277281365966976 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7, D8} := by
  decide +kernel
theorem augmentation0 : augmentation 1804277281365966976 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1804277281365966976 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 1804277281365966976 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 1804277281365966976 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 1804277281365966976 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 1804277281365966976 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 1804277281365966976 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 1804277281365966976 D7 = U7 := by
  decide +kernel
theorem augmentation8 : augmentation 1804277281365966976 D8 = U8 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1804277281365966976 = {U0, U1, U2, U3, U4, U5, U6, U7, U8} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7, augmentation8]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1804277281365966976 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport023
