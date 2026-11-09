import SignedCatalogue
import NewCertificates0216
import NewCertificates0217
import NewCertificates0218
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport149
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 6, 3, 7, 2, 4, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0216.C6924, NewCertificates0216.C6925, NewCertificates0216.C6926, NewCertificates0216.C6927, NewCertificates0216.C6928, NewCertificates0216.C6929, NewCertificates0216.C6930, NewCertificates0216.C6931, NewCertificates0216.C6932, NewCertificates0216.C6933, NewCertificates0216.C6934, NewCertificates0216.C6935, NewCertificates0216.C6936, NewCertificates0216.C6937, NewCertificates0216.C6938, NewCertificates0216.C6939, NewCertificates0216.C6940, NewCertificates0216.C6941, NewCertificates0216.C6942, NewCertificates0216.C6943, NewCertificates0217.C6944, NewCertificates0217.C6945, NewCertificates0217.C6946, NewCertificates0217.C6947, NewCertificates0217.C6948, NewCertificates0217.C6949, NewCertificates0217.C6950, NewCertificates0217.C6951, NewCertificates0217.C6952, NewCertificates0217.C6953, NewCertificates0217.C6954, NewCertificates0217.C6955, NewCertificates0217.C6956, NewCertificates0217.C6957, NewCertificates0217.C6958, NewCertificates0217.C6959, NewCertificates0217.C6960, NewCertificates0217.C6961, NewCertificates0217.C6962, NewCertificates0217.C6963, NewCertificates0217.C6964, NewCertificates0217.C6965, NewCertificates0217.C6966, NewCertificates0217.C6967, NewCertificates0217.C6968, NewCertificates0217.C6969, NewCertificates0217.C6970, NewCertificates0217.C6971, NewCertificates0217.C6972, NewCertificates0217.C6973, NewCertificates0217.C6974, NewCertificates0217.C6975, NewCertificates0218.C6976, NewCertificates0218.C6977, NewCertificates0218.C6978, NewCertificates0218.C6979, NewCertificates0218.C6980, NewCertificates0218.C6981, NewCertificates0218.C6982, NewCertificates0218.C6983, NewCertificates0218.C6984, NewCertificates0218.C6985, NewCertificates0218.C6986, NewCertificates0218.C6987, NewCertificates0218.C6988, NewCertificates0218.C6989, NewCertificates0218.C6990, NewCertificates0218.C6991, NewCertificates0218.C6992, NewCertificates0218.C6993, NewCertificates0218.C6994, NewCertificates0218.C6995}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 0, 2, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0]
def U5 : QuotientMatrix := !![1, 0, 0, 0, 0, 2, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 0, 1; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0]
def U6 : QuotientMatrix := !![1, 0, 0, 0, 0, 2, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0]
def U7 : QuotientMatrix := !![1, 0, 0, 0, 0, 2, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 0, 1; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,4), (2,3)}
def D4 : Finset (Fin 8 × Fin 8) := {(0,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(0,5), (1,4)}
def D6 : Finset (Fin 8 × Fin 8) := {(0,5), (2,3)}
def D7 : Finset (Fin 8 × Fin 8) := {(0,5), (1,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 6100197723024658464).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 6100197723024658464 D i ∧ offSum 6100197723024658464 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7} := by
  decide +kernel
theorem augmentation0 : augmentation 6100197723024658464 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 6100197723024658464 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 6100197723024658464 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 6100197723024658464 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 6100197723024658464 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 6100197723024658464 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 6100197723024658464 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 6100197723024658464 D7 = U7 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 6100197723024658464 = {U0, U1, U2, U3, U4, U5, U6, U7} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 6100197723024658464 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport149
