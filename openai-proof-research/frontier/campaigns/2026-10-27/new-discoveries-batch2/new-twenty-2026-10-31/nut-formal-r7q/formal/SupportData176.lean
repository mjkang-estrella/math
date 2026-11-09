import SignedCatalogue
import NewCertificates0255
import NewCertificates0256
import NewCertificates0257
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport176
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 4, 1, 7, 5, 6, 3, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 3, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0255.C8164, NewCertificates0255.C8165, NewCertificates0255.C8166, NewCertificates0255.C8167, NewCertificates0255.C8168, NewCertificates0255.C8169, NewCertificates0255.C8170, NewCertificates0255.C8171, NewCertificates0255.C8172, NewCertificates0255.C8173, NewCertificates0255.C8174, NewCertificates0255.C8175, NewCertificates0255.C8176, NewCertificates0255.C8177, NewCertificates0255.C8178, NewCertificates0255.C8179, NewCertificates0255.C8180, NewCertificates0255.C8181, NewCertificates0255.C8182, NewCertificates0255.C8183, NewCertificates0255.C8184, NewCertificates0255.C8185, NewCertificates0255.C8186, NewCertificates0255.C8187, NewCertificates0255.C8188, NewCertificates0255.C8189, NewCertificates0255.C8190, NewCertificates0255.C8191, NewCertificates0256.C8192, NewCertificates0256.C8193, NewCertificates0256.C8194, NewCertificates0256.C8195, NewCertificates0256.C8196, NewCertificates0256.C8197, NewCertificates0256.C8198, NewCertificates0256.C8199, NewCertificates0256.C8200, NewCertificates0256.C8201, NewCertificates0256.C8202, NewCertificates0256.C8203, NewCertificates0256.C8204, NewCertificates0256.C8205, NewCertificates0256.C8206, NewCertificates0256.C8207, NewCertificates0256.C8208, NewCertificates0256.C8209, NewCertificates0256.C8210, NewCertificates0256.C8211, NewCertificates0256.C8212, NewCertificates0256.C8213, NewCertificates0256.C8214, NewCertificates0256.C8215, NewCertificates0256.C8216, NewCertificates0256.C8217, NewCertificates0256.C8218, NewCertificates0256.C8219, NewCertificates0256.C8220, NewCertificates0256.C8221, NewCertificates0256.C8222, NewCertificates0256.C8223, NewCertificates0257.C8224, NewCertificates0257.C8225, NewCertificates0257.C8226, NewCertificates0257.C8227, NewCertificates0257.C8228, NewCertificates0257.C8229, NewCertificates0257.C8230, NewCertificates0257.C8231, NewCertificates0257.C8232, NewCertificates0257.C8233, NewCertificates0257.C8234, NewCertificates0257.C8235}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def U5 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,4), (2,3)}
def D4 : Finset (Fin 8 × Fin 8) := {(0,4)}
def D5 : Finset (Fin 8 × Fin 8) := {(0,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 7108026027716677648).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 7108026027716677648 D i ∧ offSum 7108026027716677648 D i ≤ 3) = {D0, D1, D2, D3, D4, D5} := by
  decide +kernel
theorem augmentation0 : augmentation 7108026027716677648 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 7108026027716677648 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 7108026027716677648 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 7108026027716677648 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 7108026027716677648 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 7108026027716677648 D5 = U5 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 7108026027716677648 = {U0, U1, U2, U3, U4, U5} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 7108026027716677648 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport176
