import SignedCatalogue
import NewCertificates0172
import NewCertificates0173
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport113
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 1, 3, 2, 4, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0172.C5508, NewCertificates0172.C5509, NewCertificates0172.C5510, NewCertificates0172.C5511, NewCertificates0172.C5512, NewCertificates0172.C5513, NewCertificates0172.C5514, NewCertificates0172.C5515, NewCertificates0172.C5516, NewCertificates0172.C5517, NewCertificates0172.C5518, NewCertificates0172.C5519, NewCertificates0172.C5520, NewCertificates0172.C5521, NewCertificates0172.C5522, NewCertificates0172.C5523, NewCertificates0172.C5524, NewCertificates0172.C5525, NewCertificates0172.C5526, NewCertificates0172.C5527, NewCertificates0172.C5528, NewCertificates0172.C5529, NewCertificates0172.C5530, NewCertificates0172.C5531, NewCertificates0172.C5532, NewCertificates0172.C5533, NewCertificates0172.C5534, NewCertificates0172.C5535, NewCertificates0173.C5536, NewCertificates0173.C5537, NewCertificates0173.C5538, NewCertificates0173.C5539, NewCertificates0173.C5540, NewCertificates0173.C5541, NewCertificates0173.C5542, NewCertificates0173.C5543, NewCertificates0173.C5544, NewCertificates0173.C5545, NewCertificates0173.C5546, NewCertificates0173.C5547}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(4,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D4 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 507521546393272512).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 507521546393272512 D i ∧ offSum 507521546393272512 D i ≤ 3) = {D0, D1, D2, D3, D4} := by
  decide +kernel
theorem augmentation0 : augmentation 507521546393272512 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 507521546393272512 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 507521546393272512 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 507521546393272512 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 507521546393272512 D4 = U4 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 507521546393272512 = {U0, U1, U2, U3, U4} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 507521546393272512 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport113
