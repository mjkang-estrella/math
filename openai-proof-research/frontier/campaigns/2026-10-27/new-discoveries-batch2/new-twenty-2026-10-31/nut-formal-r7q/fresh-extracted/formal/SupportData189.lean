import SignedCatalogue
import NewCertificates0278
import NewCertificates0279
import NewCertificates0280
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport189
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 1, 7, 4, 5, 6, 3, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 2, 3, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0278.C8924, NewCertificates0278.C8925, NewCertificates0278.C8926, NewCertificates0278.C8927, NewCertificates0279.C8928, NewCertificates0279.C8929, NewCertificates0279.C8930, NewCertificates0279.C8931, NewCertificates0279.C8932, NewCertificates0279.C8933, NewCertificates0279.C8934, NewCertificates0279.C8935, NewCertificates0279.C8936, NewCertificates0279.C8937, NewCertificates0279.C8938, NewCertificates0279.C8939, NewCertificates0279.C8940, NewCertificates0279.C8941, NewCertificates0279.C8942, NewCertificates0279.C8943, NewCertificates0279.C8944, NewCertificates0279.C8945, NewCertificates0279.C8946, NewCertificates0279.C8947, NewCertificates0279.C8948, NewCertificates0279.C8949, NewCertificates0279.C8950, NewCertificates0279.C8951, NewCertificates0279.C8952, NewCertificates0279.C8953, NewCertificates0279.C8954, NewCertificates0279.C8955, NewCertificates0279.C8956, NewCertificates0279.C8957, NewCertificates0279.C8958, NewCertificates0279.C8959, NewCertificates0280.C8960, NewCertificates0280.C8961, NewCertificates0280.C8962, NewCertificates0280.C8963, NewCertificates0280.C8964, NewCertificates0280.C8965, NewCertificates0280.C8966, NewCertificates0280.C8967, NewCertificates0280.C8968, NewCertificates0280.C8969, NewCertificates0280.C8970, NewCertificates0280.C8971, NewCertificates0280.C8972, NewCertificates0280.C8973, NewCertificates0280.C8974, NewCertificates0280.C8975, NewCertificates0280.C8976, NewCertificates0280.C8977, NewCertificates0280.C8978, NewCertificates0280.C8979}
def U0 : QuotientMatrix := !![1, 1, 0, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 1, 0, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U2 : QuotientMatrix := !![0, 2, 0, 0, 0, 0, 0, 1; 2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U3 : QuotientMatrix := !![0, 2, 0, 0, 0, 0, 0, 1; 2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(0,1)}
def D3 : Finset (Fin 8 × Fin 8) := {(0,1), (2,3)}
theorem doubled_enumeration : ((supportEdges 1383828705214235010).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1383828705214235010 D i ∧ offSum 1383828705214235010 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 1383828705214235010 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1383828705214235010 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 1383828705214235010 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 1383828705214235010 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1383828705214235010 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1383828705214235010 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport189
