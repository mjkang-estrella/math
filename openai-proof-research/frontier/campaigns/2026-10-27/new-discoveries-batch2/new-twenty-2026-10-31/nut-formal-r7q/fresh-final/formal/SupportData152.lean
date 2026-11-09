import SignedCatalogue
import NewCertificates0223
import NewCertificates0224
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport152
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 7, 6, 1, 2, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 2, 3, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0223.C7140, NewCertificates0223.C7141, NewCertificates0223.C7142, NewCertificates0223.C7143, NewCertificates0223.C7144, NewCertificates0223.C7145, NewCertificates0223.C7146, NewCertificates0223.C7147, NewCertificates0223.C7148, NewCertificates0223.C7149, NewCertificates0223.C7150, NewCertificates0223.C7151, NewCertificates0223.C7152, NewCertificates0223.C7153, NewCertificates0223.C7154, NewCertificates0223.C7155, NewCertificates0223.C7156, NewCertificates0223.C7157, NewCertificates0223.C7158, NewCertificates0223.C7159, NewCertificates0223.C7160, NewCertificates0223.C7161, NewCertificates0223.C7162, NewCertificates0223.C7163, NewCertificates0223.C7164, NewCertificates0223.C7165, NewCertificates0223.C7166, NewCertificates0223.C7167, NewCertificates0224.C7168, NewCertificates0224.C7169, NewCertificates0224.C7170, NewCertificates0224.C7171, NewCertificates0224.C7172, NewCertificates0224.C7173, NewCertificates0224.C7174, NewCertificates0224.C7175, NewCertificates0224.C7176, NewCertificates0224.C7177, NewCertificates0224.C7178, NewCertificates0224.C7179, NewCertificates0224.C7180, NewCertificates0224.C7181, NewCertificates0224.C7182, NewCertificates0224.C7183, NewCertificates0224.C7184, NewCertificates0224.C7185, NewCertificates0224.C7186, NewCertificates0224.C7187, NewCertificates0224.C7188, NewCertificates0224.C7189, NewCertificates0224.C7190, NewCertificates0224.C7191, NewCertificates0224.C7192, NewCertificates0224.C7193, NewCertificates0224.C7194, NewCertificates0224.C7195, NewCertificates0224.C7196, NewCertificates0224.C7197, NewCertificates0224.C7198, NewCertificates0224.C7199}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U4 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 1, 0; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U5 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 1, 0; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U6 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U7 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,4), (2,3)}
def D4 : Finset (Fin 8 × Fin 8) := {(0,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(0,5), (2,3)}
def D6 : Finset (Fin 8 × Fin 8) := {(0,5), (1,4)}
def D7 : Finset (Fin 8 × Fin 8) := {(0,5), (1,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 520237509834739872).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 520237509834739872 D i ∧ offSum 520237509834739872 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7} := by
  decide +kernel
theorem augmentation0 : augmentation 520237509834739872 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 520237509834739872 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 520237509834739872 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 520237509834739872 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 520237509834739872 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 520237509834739872 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 520237509834739872 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 520237509834739872 D7 = U7 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 520237509834739872 = {U0, U1, U2, U3, U4, U5, U6, U7} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 520237509834739872 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport152
