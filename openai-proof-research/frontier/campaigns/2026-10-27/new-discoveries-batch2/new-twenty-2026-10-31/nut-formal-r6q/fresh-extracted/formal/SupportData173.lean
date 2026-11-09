import SignedCatalogue
import NewCertificates0250
import NewCertificates0251
import NewCertificates0252
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport173
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 4, 3, 2, 5, 6, 7, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 3, 4, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0250.C8004, NewCertificates0250.C8005, NewCertificates0250.C8006, NewCertificates0250.C8007, NewCertificates0250.C8008, NewCertificates0250.C8009, NewCertificates0250.C8010, NewCertificates0250.C8011, NewCertificates0250.C8012, NewCertificates0250.C8013, NewCertificates0250.C8014, NewCertificates0250.C8015, NewCertificates0250.C8016, NewCertificates0250.C8017, NewCertificates0250.C8018, NewCertificates0250.C8019, NewCertificates0250.C8020, NewCertificates0250.C8021, NewCertificates0250.C8022, NewCertificates0250.C8023, NewCertificates0250.C8024, NewCertificates0250.C8025, NewCertificates0250.C8026, NewCertificates0250.C8027, NewCertificates0250.C8028, NewCertificates0250.C8029, NewCertificates0250.C8030, NewCertificates0250.C8031, NewCertificates0251.C8032, NewCertificates0251.C8033, NewCertificates0251.C8034, NewCertificates0251.C8035, NewCertificates0251.C8036, NewCertificates0251.C8037, NewCertificates0251.C8038, NewCertificates0251.C8039, NewCertificates0251.C8040, NewCertificates0251.C8041, NewCertificates0251.C8042, NewCertificates0251.C8043, NewCertificates0251.C8044, NewCertificates0251.C8045, NewCertificates0251.C8046, NewCertificates0251.C8047, NewCertificates0251.C8048, NewCertificates0251.C8049, NewCertificates0251.C8050, NewCertificates0251.C8051, NewCertificates0251.C8052, NewCertificates0251.C8053, NewCertificates0251.C8054, NewCertificates0251.C8055, NewCertificates0251.C8056, NewCertificates0251.C8057, NewCertificates0251.C8058, NewCertificates0251.C8059, NewCertificates0251.C8060, NewCertificates0251.C8061, NewCertificates0251.C8062, NewCertificates0251.C8063, NewCertificates0252.C8064, NewCertificates0252.C8065, NewCertificates0252.C8066, NewCertificates0252.C8067}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(0,4)}
def D4 : Finset (Fin 8 × Fin 8) := {(0,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 7107458705216028688).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 7107458705216028688 D i ∧ offSum 7107458705216028688 D i ≤ 3) = {D0, D1, D2, D3, D4} := by
  decide +kernel
theorem augmentation0 : augmentation 7107458705216028688 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 7107458705216028688 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 7107458705216028688 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 7107458705216028688 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 7107458705216028688 D4 = U4 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 7107458705216028688 = {U0, U1, U2, U3, U4} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 7107458705216028688 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport173
