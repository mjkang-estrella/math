import SignedCatalogue
import NewCertificates0231
import NewCertificates0232
import NewCertificates0233
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport157
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 7, 4, 2, 6, 1, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0231.C7400, NewCertificates0231.C7401, NewCertificates0231.C7402, NewCertificates0231.C7403, NewCertificates0231.C7404, NewCertificates0231.C7405, NewCertificates0231.C7406, NewCertificates0231.C7407, NewCertificates0231.C7408, NewCertificates0231.C7409, NewCertificates0231.C7410, NewCertificates0231.C7411, NewCertificates0231.C7412, NewCertificates0231.C7413, NewCertificates0231.C7414, NewCertificates0231.C7415, NewCertificates0231.C7416, NewCertificates0231.C7417, NewCertificates0231.C7418, NewCertificates0231.C7419, NewCertificates0231.C7420, NewCertificates0231.C7421, NewCertificates0231.C7422, NewCertificates0231.C7423, NewCertificates0232.C7424, NewCertificates0232.C7425, NewCertificates0232.C7426, NewCertificates0232.C7427, NewCertificates0232.C7428, NewCertificates0232.C7429, NewCertificates0232.C7430, NewCertificates0232.C7431, NewCertificates0232.C7432, NewCertificates0232.C7433, NewCertificates0232.C7434, NewCertificates0232.C7435, NewCertificates0232.C7436, NewCertificates0232.C7437, NewCertificates0232.C7438, NewCertificates0232.C7439, NewCertificates0232.C7440, NewCertificates0232.C7441, NewCertificates0232.C7442, NewCertificates0232.C7443, NewCertificates0232.C7444, NewCertificates0232.C7445, NewCertificates0232.C7446, NewCertificates0232.C7447, NewCertificates0232.C7448, NewCertificates0232.C7449, NewCertificates0232.C7450, NewCertificates0232.C7451, NewCertificates0232.C7452, NewCertificates0232.C7453, NewCertificates0232.C7454, NewCertificates0232.C7455, NewCertificates0233.C7456, NewCertificates0233.C7457, NewCertificates0233.C7458, NewCertificates0233.C7459, NewCertificates0233.C7460, NewCertificates0233.C7461, NewCertificates0233.C7462, NewCertificates0233.C7463, NewCertificates0233.C7464, NewCertificates0233.C7465, NewCertificates0233.C7466, NewCertificates0233.C7467, NewCertificates0233.C7468, NewCertificates0233.C7469, NewCertificates0233.C7470, NewCertificates0233.C7471, NewCertificates0233.C7472, NewCertificates0233.C7473, NewCertificates0233.C7474, NewCertificates0233.C7475}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U5 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U6 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U7 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U8 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U9 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,4), (2,3)}
def D4 : Finset (Fin 8 × Fin 8) := {(4,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(2,3), (4,5)}
def D6 : Finset (Fin 8 × Fin 8) := {(0,5)}
def D7 : Finset (Fin 8 × Fin 8) := {(0,5), (2,3)}
def D8 : Finset (Fin 8 × Fin 8) := {(0,5), (1,4)}
def D9 : Finset (Fin 8 × Fin 8) := {(0,5), (1,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 5010836374279442592).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5010836374279442592 D i ∧ offSum 5010836374279442592 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7, D8, D9} := by
  decide +kernel
theorem augmentation0 : augmentation 5010836374279442592 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5010836374279442592 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 5010836374279442592 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 5010836374279442592 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 5010836374279442592 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 5010836374279442592 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 5010836374279442592 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 5010836374279442592 D7 = U7 := by
  decide +kernel
theorem augmentation8 : augmentation 5010836374279442592 D8 = U8 := by
  decide +kernel
theorem augmentation9 : augmentation 5010836374279442592 D9 = U9 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5010836374279442592 = {U0, U1, U2, U3, U4, U5, U6, U7, U8, U9} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7, augmentation8, augmentation9]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5010836374279442592 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport157
