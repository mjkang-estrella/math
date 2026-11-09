import SignedCatalogue
import NewCertificates0129
import NewCertificates0130
import NewCertificates0131
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport090
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 5, 6, 3, 4, 1, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0129.C4150, NewCertificates0129.C4151, NewCertificates0129.C4152, NewCertificates0129.C4153, NewCertificates0129.C4154, NewCertificates0129.C4155, NewCertificates0129.C4156, NewCertificates0129.C4157, NewCertificates0129.C4158, NewCertificates0129.C4159, NewCertificates0130.C4160, NewCertificates0130.C4161, NewCertificates0130.C4162, NewCertificates0130.C4163, NewCertificates0130.C4164, NewCertificates0130.C4165, NewCertificates0130.C4166, NewCertificates0130.C4167, NewCertificates0130.C4168, NewCertificates0130.C4169, NewCertificates0130.C4170, NewCertificates0130.C4171, NewCertificates0130.C4172, NewCertificates0130.C4173, NewCertificates0130.C4174, NewCertificates0130.C4175, NewCertificates0130.C4176, NewCertificates0130.C4177, NewCertificates0130.C4178, NewCertificates0130.C4179, NewCertificates0130.C4180, NewCertificates0130.C4181, NewCertificates0130.C4182, NewCertificates0130.C4183, NewCertificates0130.C4184, NewCertificates0130.C4185, NewCertificates0130.C4186, NewCertificates0130.C4187, NewCertificates0130.C4188, NewCertificates0130.C4189, NewCertificates0130.C4190, NewCertificates0130.C4191, NewCertificates0131.C4192, NewCertificates0131.C4193, NewCertificates0131.C4194, NewCertificates0131.C4195, NewCertificates0131.C4196, NewCertificates0131.C4197, NewCertificates0131.C4198, NewCertificates0131.C4199, NewCertificates0131.C4200, NewCertificates0131.C4201, NewCertificates0131.C4202, NewCertificates0131.C4203, NewCertificates0131.C4204, NewCertificates0131.C4205}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 7027471540963266688).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 7027471540963266688 D i ∧ offSum 7027471540963266688 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 7027471540963266688 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 7027471540963266688 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 7027471540963266688 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 7027471540963266688 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 7027471540963266688 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 7027471540963266688 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport090
