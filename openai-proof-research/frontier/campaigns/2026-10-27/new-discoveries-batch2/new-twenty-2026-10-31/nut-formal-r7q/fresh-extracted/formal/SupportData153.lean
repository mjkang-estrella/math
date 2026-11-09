import SignedCatalogue
import NewCertificates0225
import NewCertificates0226
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport153
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 7, 1, 4, 6, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 2, 3, 4, 5, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0225.C7200, NewCertificates0225.C7201, NewCertificates0225.C7202, NewCertificates0225.C7203, NewCertificates0225.C7204, NewCertificates0225.C7205, NewCertificates0225.C7206, NewCertificates0225.C7207, NewCertificates0225.C7208, NewCertificates0225.C7209, NewCertificates0225.C7210, NewCertificates0225.C7211, NewCertificates0225.C7212, NewCertificates0225.C7213, NewCertificates0225.C7214, NewCertificates0225.C7215, NewCertificates0225.C7216, NewCertificates0225.C7217, NewCertificates0225.C7218, NewCertificates0225.C7219, NewCertificates0225.C7220, NewCertificates0225.C7221, NewCertificates0225.C7222, NewCertificates0225.C7223, NewCertificates0225.C7224, NewCertificates0225.C7225, NewCertificates0225.C7226, NewCertificates0225.C7227, NewCertificates0225.C7228, NewCertificates0225.C7229, NewCertificates0225.C7230, NewCertificates0225.C7231, NewCertificates0226.C7232, NewCertificates0226.C7233, NewCertificates0226.C7234, NewCertificates0226.C7235, NewCertificates0226.C7236, NewCertificates0226.C7237, NewCertificates0226.C7238, NewCertificates0226.C7239, NewCertificates0226.C7240, NewCertificates0226.C7241, NewCertificates0226.C7242, NewCertificates0226.C7243, NewCertificates0226.C7244, NewCertificates0226.C7245, NewCertificates0226.C7246, NewCertificates0226.C7247, NewCertificates0226.C7248, NewCertificates0226.C7249, NewCertificates0226.C7250, NewCertificates0226.C7251, NewCertificates0226.C7252, NewCertificates0226.C7253, NewCertificates0226.C7254, NewCertificates0226.C7255, NewCertificates0226.C7256, NewCertificates0226.C7257, NewCertificates0226.C7258, NewCertificates0226.C7259}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U4 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 1, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U5 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 0, 1, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U6 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U7 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,4), (2,3)}
def D4 : Finset (Fin 8 × Fin 8) := {(0,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(0,5), (2,3)}
def D6 : Finset (Fin 8 × Fin 8) := {(0,5), (1,4)}
def D7 : Finset (Fin 8 × Fin 8) := {(0,5), (1,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 2530039212288807072).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2530039212288807072 D i ∧ offSum 2530039212288807072 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7} := by
  decide +kernel
theorem augmentation0 : augmentation 2530039212288807072 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2530039212288807072 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 2530039212288807072 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 2530039212288807072 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 2530039212288807072 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 2530039212288807072 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 2530039212288807072 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 2530039212288807072 D7 = U7 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2530039212288807072 = {U0, U1, U2, U3, U4, U5, U6, U7} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2530039212288807072 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport153
