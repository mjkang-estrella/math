import SignedCatalogue
import NewCertificates0218
import NewCertificates0219
import NewCertificates0220
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport150
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 7, 1, 6, 2, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 4, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0218.C6996, NewCertificates0218.C6997, NewCertificates0218.C6998, NewCertificates0218.C6999, NewCertificates0218.C7000, NewCertificates0218.C7001, NewCertificates0218.C7002, NewCertificates0218.C7003, NewCertificates0218.C7004, NewCertificates0218.C7005, NewCertificates0218.C7006, NewCertificates0218.C7007, NewCertificates0219.C7008, NewCertificates0219.C7009, NewCertificates0219.C7010, NewCertificates0219.C7011, NewCertificates0219.C7012, NewCertificates0219.C7013, NewCertificates0219.C7014, NewCertificates0219.C7015, NewCertificates0219.C7016, NewCertificates0219.C7017, NewCertificates0219.C7018, NewCertificates0219.C7019, NewCertificates0219.C7020, NewCertificates0219.C7021, NewCertificates0219.C7022, NewCertificates0219.C7023, NewCertificates0219.C7024, NewCertificates0219.C7025, NewCertificates0219.C7026, NewCertificates0219.C7027, NewCertificates0219.C7028, NewCertificates0219.C7029, NewCertificates0219.C7030, NewCertificates0219.C7031, NewCertificates0219.C7032, NewCertificates0219.C7033, NewCertificates0219.C7034, NewCertificates0219.C7035, NewCertificates0219.C7036, NewCertificates0219.C7037, NewCertificates0219.C7038, NewCertificates0219.C7039, NewCertificates0220.C7040, NewCertificates0220.C7041, NewCertificates0220.C7042, NewCertificates0220.C7043, NewCertificates0220.C7044, NewCertificates0220.C7045, NewCertificates0220.C7046, NewCertificates0220.C7047, NewCertificates0220.C7048, NewCertificates0220.C7049, NewCertificates0220.C7050, NewCertificates0220.C7051, NewCertificates0220.C7052, NewCertificates0220.C7053, NewCertificates0220.C7054, NewCertificates0220.C7055, NewCertificates0220.C7056, NewCertificates0220.C7057, NewCertificates0220.C7058, NewCertificates0220.C7059, NewCertificates0220.C7060, NewCertificates0220.C7061, NewCertificates0220.C7062, NewCertificates0220.C7063, NewCertificates0220.C7064, NewCertificates0220.C7065, NewCertificates0220.C7066, NewCertificates0220.C7067}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 2, 0, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 1, 0, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 2, 0, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U5 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 1, 0, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U6 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U7 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 2, 0, 0, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U8 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 1, 0, 0, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D4 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
def D5 : Finset (Fin 8 × Fin 8) := {(1,5), (2,4)}
def D6 : Finset (Fin 8 × Fin 8) := {(0,5)}
def D7 : Finset (Fin 8 × Fin 8) := {(0,5), (3,4)}
def D8 : Finset (Fin 8 × Fin 8) := {(0,5), (2,4)}
theorem doubled_enumeration : ((supportEdges 4867268648702615712).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 4867268648702615712 D i ∧ offSum 4867268648702615712 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7, D8} := by
  decide +kernel
theorem augmentation0 : augmentation 4867268648702615712 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 4867268648702615712 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 4867268648702615712 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 4867268648702615712 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 4867268648702615712 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 4867268648702615712 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 4867268648702615712 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 4867268648702615712 D7 = U7 := by
  decide +kernel
theorem augmentation8 : augmentation 4867268648702615712 D8 = U8 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 4867268648702615712 = {U0, U1, U2, U3, U4, U5, U6, U7, U8} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7, augmentation8]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 4867268648702615712 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport150
