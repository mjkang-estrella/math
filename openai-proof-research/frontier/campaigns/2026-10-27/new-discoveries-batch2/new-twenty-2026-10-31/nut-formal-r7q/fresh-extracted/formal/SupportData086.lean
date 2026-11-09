import SignedCatalogue
import NewCertificates0123
import NewCertificates0124
import NewCertificates0125
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport086
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 5, 6, 4, 3, 1, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0123.C3958, NewCertificates0123.C3959, NewCertificates0123.C3960, NewCertificates0123.C3961, NewCertificates0123.C3962, NewCertificates0123.C3963, NewCertificates0123.C3964, NewCertificates0123.C3965, NewCertificates0123.C3966, NewCertificates0123.C3967, NewCertificates0124.C3968, NewCertificates0124.C3969, NewCertificates0124.C3970, NewCertificates0124.C3971, NewCertificates0124.C3972, NewCertificates0124.C3973, NewCertificates0124.C3974, NewCertificates0124.C3975, NewCertificates0124.C3976, NewCertificates0124.C3977, NewCertificates0124.C3978, NewCertificates0124.C3979, NewCertificates0124.C3980, NewCertificates0124.C3981, NewCertificates0124.C3982, NewCertificates0124.C3983, NewCertificates0124.C3984, NewCertificates0124.C3985, NewCertificates0124.C3986, NewCertificates0124.C3987, NewCertificates0124.C3988, NewCertificates0124.C3989, NewCertificates0124.C3990, NewCertificates0124.C3991, NewCertificates0124.C3992, NewCertificates0124.C3993, NewCertificates0124.C3994, NewCertificates0124.C3995, NewCertificates0124.C3996, NewCertificates0124.C3997, NewCertificates0124.C3998, NewCertificates0124.C3999, NewCertificates0125.C4000, NewCertificates0125.C4001, NewCertificates0125.C4002, NewCertificates0125.C4003, NewCertificates0125.C4004, NewCertificates0125.C4005, NewCertificates0125.C4006, NewCertificates0125.C4007, NewCertificates0125.C4008, NewCertificates0125.C4009, NewCertificates0125.C4010, NewCertificates0125.C4011, NewCertificates0125.C4012, NewCertificates0125.C4013, NewCertificates0125.C4014, NewCertificates0125.C4015, NewCertificates0125.C4016, NewCertificates0125.C4017, NewCertificates0125.C4018, NewCertificates0125.C4019, NewCertificates0125.C4020, NewCertificates0125.C4021, NewCertificates0125.C4022, NewCertificates0125.C4023, NewCertificates0125.C4024, NewCertificates0125.C4025, NewCertificates0125.C4026, NewCertificates0125.C4027, NewCertificates0125.C4028, NewCertificates0125.C4029}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 7037103263355244672).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 7037103263355244672 D i ∧ offSum 7037103263355244672 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 7037103263355244672 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 7037103263355244672 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 7037103263355244672 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 7037103263355244672 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 7037103263355244672 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 7037103263355244672 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport086
