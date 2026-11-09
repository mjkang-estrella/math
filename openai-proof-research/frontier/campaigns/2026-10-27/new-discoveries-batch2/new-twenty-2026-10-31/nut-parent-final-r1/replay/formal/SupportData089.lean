import SignedCatalogue
import NewCertificates0127
import NewCertificates0128
import NewCertificates0129
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport089
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 5, 4, 6, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 5, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0127.C4094, NewCertificates0127.C4095, NewCertificates0128.C4096, NewCertificates0128.C4097, NewCertificates0128.C4098, NewCertificates0128.C4099, NewCertificates0128.C4100, NewCertificates0128.C4101, NewCertificates0128.C4102, NewCertificates0128.C4103, NewCertificates0128.C4104, NewCertificates0128.C4105, NewCertificates0128.C4106, NewCertificates0128.C4107, NewCertificates0128.C4108, NewCertificates0128.C4109, NewCertificates0128.C4110, NewCertificates0128.C4111, NewCertificates0128.C4112, NewCertificates0128.C4113, NewCertificates0128.C4114, NewCertificates0128.C4115, NewCertificates0128.C4116, NewCertificates0128.C4117, NewCertificates0128.C4118, NewCertificates0128.C4119, NewCertificates0128.C4120, NewCertificates0128.C4121, NewCertificates0128.C4122, NewCertificates0128.C4123, NewCertificates0128.C4124, NewCertificates0128.C4125, NewCertificates0128.C4126, NewCertificates0128.C4127, NewCertificates0129.C4128, NewCertificates0129.C4129, NewCertificates0129.C4130, NewCertificates0129.C4131, NewCertificates0129.C4132, NewCertificates0129.C4133, NewCertificates0129.C4134, NewCertificates0129.C4135, NewCertificates0129.C4136, NewCertificates0129.C4137, NewCertificates0129.C4138, NewCertificates0129.C4139, NewCertificates0129.C4140, NewCertificates0129.C4141, NewCertificates0129.C4142, NewCertificates0129.C4143, NewCertificates0129.C4144, NewCertificates0129.C4145, NewCertificates0129.C4146, NewCertificates0129.C4147, NewCertificates0129.C4148, NewCertificates0129.C4149}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 2534629535895818368).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2534629535895818368 D i ∧ offSum 2534629535895818368 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 2534629535895818368 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2534629535895818368 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 2534629535895818368 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 2534629535895818368 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2534629535895818368 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2534629535895818368 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport089
