import SignedCatalogue
import NewCertificates0041
import NewCertificates0042
import NewCertificates0043
import NewCertificates0044
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport028
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 5, 4, 2, 6, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0041.C1324, NewCertificates0041.C1325, NewCertificates0041.C1326, NewCertificates0041.C1327, NewCertificates0041.C1328, NewCertificates0041.C1329, NewCertificates0041.C1330, NewCertificates0041.C1331, NewCertificates0041.C1332, NewCertificates0041.C1333, NewCertificates0041.C1334, NewCertificates0041.C1335, NewCertificates0041.C1336, NewCertificates0041.C1337, NewCertificates0041.C1338, NewCertificates0041.C1339, NewCertificates0041.C1340, NewCertificates0041.C1341, NewCertificates0041.C1342, NewCertificates0041.C1343, NewCertificates0042.C1344, NewCertificates0042.C1345, NewCertificates0042.C1346, NewCertificates0042.C1347, NewCertificates0042.C1348, NewCertificates0042.C1349, NewCertificates0042.C1350, NewCertificates0042.C1351, NewCertificates0042.C1352, NewCertificates0042.C1353, NewCertificates0042.C1354, NewCertificates0042.C1355, NewCertificates0042.C1356, NewCertificates0042.C1357, NewCertificates0042.C1358, NewCertificates0042.C1359, NewCertificates0042.C1360, NewCertificates0042.C1361, NewCertificates0042.C1362, NewCertificates0042.C1363, NewCertificates0042.C1364, NewCertificates0042.C1365, NewCertificates0042.C1366, NewCertificates0042.C1367, NewCertificates0042.C1368, NewCertificates0042.C1369, NewCertificates0042.C1370, NewCertificates0042.C1371, NewCertificates0042.C1372, NewCertificates0042.C1373, NewCertificates0042.C1374, NewCertificates0042.C1375, NewCertificates0043.C1376, NewCertificates0043.C1377, NewCertificates0043.C1378, NewCertificates0043.C1379, NewCertificates0043.C1380, NewCertificates0043.C1381, NewCertificates0043.C1382, NewCertificates0043.C1383, NewCertificates0043.C1384, NewCertificates0043.C1385, NewCertificates0043.C1386, NewCertificates0043.C1387, NewCertificates0043.C1388, NewCertificates0043.C1389, NewCertificates0043.C1390, NewCertificates0043.C1391, NewCertificates0043.C1392, NewCertificates0043.C1393, NewCertificates0043.C1394, NewCertificates0043.C1395, NewCertificates0043.C1396, NewCertificates0043.C1397, NewCertificates0043.C1398, NewCertificates0043.C1399, NewCertificates0043.C1400, NewCertificates0043.C1401, NewCertificates0043.C1402, NewCertificates0043.C1403, NewCertificates0043.C1404, NewCertificates0043.C1405, NewCertificates0043.C1406, NewCertificates0043.C1407, NewCertificates0044.C1408, NewCertificates0044.C1409, NewCertificates0044.C1410, NewCertificates0044.C1411, NewCertificates0044.C1412, NewCertificates0044.C1413, NewCertificates0044.C1414, NewCertificates0044.C1415, NewCertificates0044.C1416, NewCertificates0044.C1417, NewCertificates0044.C1418, NewCertificates0044.C1419}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 2, 0, 0, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 2, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 2, 0, 0, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def U5 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 1, 0, 0, 2, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def U6 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def U7 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 2, 0, 0, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def U8 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def U9 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 2, 0, 0, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,6)}
def D2 : Finset (Fin 8 × Fin 8) := {(4,6)}
def D3 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D4 : Finset (Fin 8 × Fin 8) := {(1,6), (2,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(2,5), (4,6)}
def D6 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D7 : Finset (Fin 8 × Fin 8) := {(1,6), (3,4)}
def D8 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
def D9 : Finset (Fin 8 × Fin 8) := {(1,6), (2,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 2959573352326381696).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2959573352326381696 D i ∧ offSum 2959573352326381696 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7, D8, D9} := by
  decide +kernel
theorem augmentation0 : augmentation 2959573352326381696 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2959573352326381696 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 2959573352326381696 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 2959573352326381696 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 2959573352326381696 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 2959573352326381696 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 2959573352326381696 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 2959573352326381696 D7 = U7 := by
  decide +kernel
theorem augmentation8 : augmentation 2959573352326381696 D8 = U8 := by
  decide +kernel
theorem augmentation9 : augmentation 2959573352326381696 D9 = U9 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2959573352326381696 = {U0, U1, U2, U3, U4, U5, U6, U7, U8, U9} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7, augmentation8, augmentation9]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2959573352326381696 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport028
