import SignedCatalogue
import NewCertificates0252
import NewCertificates0253
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport174
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 4, 6, 3, 5, 2, 1, 7] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0252.C8068, NewCertificates0252.C8069, NewCertificates0252.C8070, NewCertificates0252.C8071, NewCertificates0252.C8072, NewCertificates0252.C8073, NewCertificates0252.C8074, NewCertificates0252.C8075, NewCertificates0252.C8076, NewCertificates0252.C8077, NewCertificates0252.C8078, NewCertificates0252.C8079, NewCertificates0252.C8080, NewCertificates0252.C8081, NewCertificates0252.C8082, NewCertificates0252.C8083, NewCertificates0252.C8084, NewCertificates0252.C8085, NewCertificates0252.C8086, NewCertificates0252.C8087, NewCertificates0252.C8088, NewCertificates0252.C8089, NewCertificates0252.C8090, NewCertificates0252.C8091, NewCertificates0252.C8092, NewCertificates0252.C8093, NewCertificates0252.C8094, NewCertificates0252.C8095, NewCertificates0253.C8096, NewCertificates0253.C8097, NewCertificates0253.C8098, NewCertificates0253.C8099, NewCertificates0253.C8100, NewCertificates0253.C8101, NewCertificates0253.C8102, NewCertificates0253.C8103, NewCertificates0253.C8104, NewCertificates0253.C8105, NewCertificates0253.C8106, NewCertificates0253.C8107, NewCertificates0253.C8108, NewCertificates0253.C8109, NewCertificates0253.C8110, NewCertificates0253.C8111, NewCertificates0253.C8112, NewCertificates0253.C8113, NewCertificates0253.C8114, NewCertificates0253.C8115}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(0,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(0,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 2754164757715525648).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2754164757715525648 D i ∧ offSum 2754164757715525648 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 2754164757715525648 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2754164757715525648 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 2754164757715525648 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 2754164757715525648 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2754164757715525648 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2754164757715525648 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport174
