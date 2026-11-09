import SignedCatalogue
import NewCertificates0253
import NewCertificates0254
import NewCertificates0255
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport175
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 4, 7, 1, 5, 6, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 4, 5, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0253.C8116, NewCertificates0253.C8117, NewCertificates0253.C8118, NewCertificates0253.C8119, NewCertificates0253.C8120, NewCertificates0253.C8121, NewCertificates0253.C8122, NewCertificates0253.C8123, NewCertificates0253.C8124, NewCertificates0253.C8125, NewCertificates0253.C8126, NewCertificates0253.C8127, NewCertificates0254.C8128, NewCertificates0254.C8129, NewCertificates0254.C8130, NewCertificates0254.C8131, NewCertificates0254.C8132, NewCertificates0254.C8133, NewCertificates0254.C8134, NewCertificates0254.C8135, NewCertificates0254.C8136, NewCertificates0254.C8137, NewCertificates0254.C8138, NewCertificates0254.C8139, NewCertificates0254.C8140, NewCertificates0254.C8141, NewCertificates0254.C8142, NewCertificates0254.C8143, NewCertificates0254.C8144, NewCertificates0254.C8145, NewCertificates0254.C8146, NewCertificates0254.C8147, NewCertificates0254.C8148, NewCertificates0254.C8149, NewCertificates0254.C8150, NewCertificates0254.C8151, NewCertificates0254.C8152, NewCertificates0254.C8153, NewCertificates0254.C8154, NewCertificates0254.C8155, NewCertificates0254.C8156, NewCertificates0254.C8157, NewCertificates0254.C8158, NewCertificates0254.C8159, NewCertificates0255.C8160, NewCertificates0255.C8161, NewCertificates0255.C8162, NewCertificates0255.C8163}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(0,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(0,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 3615478461323845648).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 3615478461323845648 D i ∧ offSum 3615478461323845648 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 3615478461323845648 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 3615478461323845648 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 3615478461323845648 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 3615478461323845648 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 3615478461323845648 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 3615478461323845648 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport175
