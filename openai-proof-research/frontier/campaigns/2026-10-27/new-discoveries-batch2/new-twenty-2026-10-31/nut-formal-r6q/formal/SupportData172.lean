import SignedCatalogue
import NewCertificates0248
import NewCertificates0249
import NewCertificates0250
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport172
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 4, 6, 1, 5, 7, 3, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0248.C7956, NewCertificates0248.C7957, NewCertificates0248.C7958, NewCertificates0248.C7959, NewCertificates0248.C7960, NewCertificates0248.C7961, NewCertificates0248.C7962, NewCertificates0248.C7963, NewCertificates0248.C7964, NewCertificates0248.C7965, NewCertificates0248.C7966, NewCertificates0248.C7967, NewCertificates0249.C7968, NewCertificates0249.C7969, NewCertificates0249.C7970, NewCertificates0249.C7971, NewCertificates0249.C7972, NewCertificates0249.C7973, NewCertificates0249.C7974, NewCertificates0249.C7975, NewCertificates0249.C7976, NewCertificates0249.C7977, NewCertificates0249.C7978, NewCertificates0249.C7979, NewCertificates0249.C7980, NewCertificates0249.C7981, NewCertificates0249.C7982, NewCertificates0249.C7983, NewCertificates0249.C7984, NewCertificates0249.C7985, NewCertificates0249.C7986, NewCertificates0249.C7987, NewCertificates0249.C7988, NewCertificates0249.C7989, NewCertificates0249.C7990, NewCertificates0249.C7991, NewCertificates0249.C7992, NewCertificates0249.C7993, NewCertificates0249.C7994, NewCertificates0249.C7995, NewCertificates0249.C7996, NewCertificates0249.C7997, NewCertificates0249.C7998, NewCertificates0249.C7999, NewCertificates0250.C8000, NewCertificates0250.C8001, NewCertificates0250.C8002, NewCertificates0250.C8003}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 1, 0, 0; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 1, 0, 0; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(0,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(0,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 2752482504388165648).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2752482504388165648 D i ∧ offSum 2752482504388165648 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 2752482504388165648 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2752482504388165648 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 2752482504388165648 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 2752482504388165648 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2752482504388165648 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2752482504388165648 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport172
