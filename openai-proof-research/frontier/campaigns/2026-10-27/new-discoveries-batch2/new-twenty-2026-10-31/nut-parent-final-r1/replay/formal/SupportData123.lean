import SignedCatalogue
import NewCertificates0186
import NewCertificates0187
import NewCertificates0188
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport123
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 1, 4, 5, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0186.C5972, NewCertificates0186.C5973, NewCertificates0186.C5974, NewCertificates0186.C5975, NewCertificates0186.C5976, NewCertificates0186.C5977, NewCertificates0186.C5978, NewCertificates0186.C5979, NewCertificates0186.C5980, NewCertificates0186.C5981, NewCertificates0186.C5982, NewCertificates0186.C5983, NewCertificates0187.C5984, NewCertificates0187.C5985, NewCertificates0187.C5986, NewCertificates0187.C5987, NewCertificates0187.C5988, NewCertificates0187.C5989, NewCertificates0187.C5990, NewCertificates0187.C5991, NewCertificates0187.C5992, NewCertificates0187.C5993, NewCertificates0187.C5994, NewCertificates0187.C5995, NewCertificates0187.C5996, NewCertificates0187.C5997, NewCertificates0187.C5998, NewCertificates0187.C5999, NewCertificates0187.C6000, NewCertificates0187.C6001, NewCertificates0187.C6002, NewCertificates0187.C6003, NewCertificates0187.C6004, NewCertificates0187.C6005, NewCertificates0187.C6006, NewCertificates0187.C6007, NewCertificates0187.C6008, NewCertificates0187.C6009, NewCertificates0187.C6010, NewCertificates0187.C6011, NewCertificates0187.C6012, NewCertificates0187.C6013, NewCertificates0187.C6014, NewCertificates0187.C6015, NewCertificates0188.C6016, NewCertificates0188.C6017, NewCertificates0188.C6018, NewCertificates0188.C6019, NewCertificates0188.C6020, NewCertificates0188.C6021, NewCertificates0188.C6022, NewCertificates0188.C6023, NewCertificates0188.C6024, NewCertificates0188.C6025, NewCertificates0188.C6026, NewCertificates0188.C6027, NewCertificates0188.C6028, NewCertificates0188.C6029, NewCertificates0188.C6030, NewCertificates0188.C6031, NewCertificates0188.C6032, NewCertificates0188.C6033, NewCertificates0188.C6034, NewCertificates0188.C6035}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U5 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U6 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U7 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D4 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
def D5 : Finset (Fin 8 × Fin 8) := {(2,4)}
def D6 : Finset (Fin 8 × Fin 8) := {(2,4), (3,5)}
def D7 : Finset (Fin 8 × Fin 8) := {(1,5), (2,4)}
theorem doubled_enumeration : ((supportEdges 4865306019910164672).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 4865306019910164672 D i ∧ offSum 4865306019910164672 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7} := by
  decide +kernel
theorem augmentation0 : augmentation 4865306019910164672 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 4865306019910164672 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 4865306019910164672 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 4865306019910164672 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 4865306019910164672 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 4865306019910164672 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 4865306019910164672 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 4865306019910164672 D7 = U7 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 4865306019910164672 = {U0, U1, U2, U3, U4, U5, U6, U7} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 4865306019910164672 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport123
