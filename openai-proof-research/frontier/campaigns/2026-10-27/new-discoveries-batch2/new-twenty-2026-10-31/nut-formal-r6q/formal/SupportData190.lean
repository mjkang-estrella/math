import SignedCatalogue
import NewCertificates0280
import NewCertificates0281
import NewCertificates0282
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport190
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 1, 7, 6, 2, 3, 4, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0280.C8980, NewCertificates0280.C8981, NewCertificates0280.C8982, NewCertificates0280.C8983, NewCertificates0280.C8984, NewCertificates0280.C8985, NewCertificates0280.C8986, NewCertificates0280.C8987, NewCertificates0280.C8988, NewCertificates0280.C8989, NewCertificates0280.C8990, NewCertificates0280.C8991, NewCertificates0281.C8992, NewCertificates0281.C8993, NewCertificates0281.C8994, NewCertificates0281.C8995, NewCertificates0281.C8996, NewCertificates0281.C8997, NewCertificates0281.C8998, NewCertificates0281.C8999, NewCertificates0281.C9000, NewCertificates0281.C9001, NewCertificates0281.C9002, NewCertificates0281.C9003, NewCertificates0281.C9004, NewCertificates0281.C9005, NewCertificates0281.C9006, NewCertificates0281.C9007, NewCertificates0281.C9008, NewCertificates0281.C9009, NewCertificates0281.C9010, NewCertificates0281.C9011, NewCertificates0281.C9012, NewCertificates0281.C9013, NewCertificates0281.C9014, NewCertificates0281.C9015, NewCertificates0281.C9016, NewCertificates0281.C9017, NewCertificates0281.C9018, NewCertificates0281.C9019, NewCertificates0281.C9020, NewCertificates0281.C9021, NewCertificates0281.C9022, NewCertificates0281.C9023, NewCertificates0282.C9024, NewCertificates0282.C9025, NewCertificates0282.C9026, NewCertificates0282.C9027}
def U0 : QuotientMatrix := !![1, 1, 0, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![0, 2, 0, 0, 0, 0, 0, 1; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(0,1)}
theorem doubled_enumeration : ((supportEdges 942972407950360962).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 942972407950360962 D i ∧ offSum 942972407950360962 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 942972407950360962 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 942972407950360962 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 942972407950360962 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 942972407950360962 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport190
