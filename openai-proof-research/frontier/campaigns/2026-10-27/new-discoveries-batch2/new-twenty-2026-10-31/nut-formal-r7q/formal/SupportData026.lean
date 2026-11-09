import SignedCatalogue
import NewCertificates0038
import NewCertificates0039
import NewCertificates0040
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport026
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 4, 6, 3, 1, 5, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0038.C1220, NewCertificates0038.C1221, NewCertificates0038.C1222, NewCertificates0038.C1223, NewCertificates0038.C1224, NewCertificates0038.C1225, NewCertificates0038.C1226, NewCertificates0038.C1227, NewCertificates0038.C1228, NewCertificates0038.C1229, NewCertificates0038.C1230, NewCertificates0038.C1231, NewCertificates0038.C1232, NewCertificates0038.C1233, NewCertificates0038.C1234, NewCertificates0038.C1235, NewCertificates0038.C1236, NewCertificates0038.C1237, NewCertificates0038.C1238, NewCertificates0038.C1239, NewCertificates0038.C1240, NewCertificates0038.C1241, NewCertificates0038.C1242, NewCertificates0038.C1243, NewCertificates0038.C1244, NewCertificates0038.C1245, NewCertificates0038.C1246, NewCertificates0038.C1247, NewCertificates0039.C1248, NewCertificates0039.C1249, NewCertificates0039.C1250, NewCertificates0039.C1251, NewCertificates0039.C1252, NewCertificates0039.C1253, NewCertificates0039.C1254, NewCertificates0039.C1255, NewCertificates0039.C1256, NewCertificates0039.C1257, NewCertificates0039.C1258, NewCertificates0039.C1259, NewCertificates0039.C1260, NewCertificates0039.C1261, NewCertificates0039.C1262, NewCertificates0039.C1263, NewCertificates0039.C1264, NewCertificates0039.C1265, NewCertificates0039.C1266, NewCertificates0039.C1267, NewCertificates0039.C1268, NewCertificates0039.C1269, NewCertificates0039.C1270, NewCertificates0039.C1271, NewCertificates0039.C1272, NewCertificates0039.C1273, NewCertificates0039.C1274, NewCertificates0039.C1275, NewCertificates0039.C1276, NewCertificates0039.C1277, NewCertificates0039.C1278, NewCertificates0039.C1279, NewCertificates0040.C1280, NewCertificates0040.C1281, NewCertificates0040.C1282, NewCertificates0040.C1283, NewCertificates0040.C1284, NewCertificates0040.C1285, NewCertificates0040.C1286, NewCertificates0040.C1287, NewCertificates0040.C1288, NewCertificates0040.C1289, NewCertificates0040.C1290, NewCertificates0040.C1291}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 5882339414476079232).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5882339414476079232 D i ∧ offSum 5882339414476079232 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 5882339414476079232 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5882339414476079232 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 5882339414476079232 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 5882339414476079232 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5882339414476079232 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5882339414476079232 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport026
