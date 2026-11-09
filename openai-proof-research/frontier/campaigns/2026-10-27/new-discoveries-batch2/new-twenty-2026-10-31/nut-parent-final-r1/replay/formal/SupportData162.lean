import SignedCatalogue
import NewCertificates0238
import NewCertificates0239
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport162
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 6, 7, 1, 4, 3, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 0, 1, 1, 2, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0238.C7620, NewCertificates0238.C7621, NewCertificates0238.C7622, NewCertificates0238.C7623, NewCertificates0238.C7624, NewCertificates0238.C7625, NewCertificates0238.C7626, NewCertificates0238.C7627, NewCertificates0238.C7628, NewCertificates0238.C7629, NewCertificates0238.C7630, NewCertificates0238.C7631, NewCertificates0238.C7632, NewCertificates0238.C7633, NewCertificates0238.C7634, NewCertificates0238.C7635, NewCertificates0238.C7636, NewCertificates0238.C7637, NewCertificates0238.C7638, NewCertificates0238.C7639, NewCertificates0238.C7640, NewCertificates0238.C7641, NewCertificates0238.C7642, NewCertificates0238.C7643, NewCertificates0238.C7644, NewCertificates0238.C7645, NewCertificates0238.C7646, NewCertificates0238.C7647, NewCertificates0239.C7648, NewCertificates0239.C7649, NewCertificates0239.C7650, NewCertificates0239.C7651}
def U0 : QuotientMatrix := !![0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 507520464128106720).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 507520464128106720 D i ∧ offSum 507520464128106720 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 507520464128106720 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 507520464128106720 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 507520464128106720 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport162
