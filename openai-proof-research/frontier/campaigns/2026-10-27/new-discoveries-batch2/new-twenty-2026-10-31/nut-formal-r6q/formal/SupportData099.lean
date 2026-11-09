import SignedCatalogue
import NewCertificates0143
import NewCertificates0144
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport099
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 5, 6, 2, 4, 3, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 5, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0143.C4590, NewCertificates0143.C4591, NewCertificates0143.C4592, NewCertificates0143.C4593, NewCertificates0143.C4594, NewCertificates0143.C4595, NewCertificates0143.C4596, NewCertificates0143.C4597, NewCertificates0143.C4598, NewCertificates0143.C4599, NewCertificates0143.C4600, NewCertificates0143.C4601, NewCertificates0143.C4602, NewCertificates0143.C4603, NewCertificates0143.C4604, NewCertificates0143.C4605, NewCertificates0143.C4606, NewCertificates0143.C4607, NewCertificates0144.C4608, NewCertificates0144.C4609, NewCertificates0144.C4610, NewCertificates0144.C4611, NewCertificates0144.C4612, NewCertificates0144.C4613, NewCertificates0144.C4614, NewCertificates0144.C4615, NewCertificates0144.C4616, NewCertificates0144.C4617, NewCertificates0144.C4618, NewCertificates0144.C4619, NewCertificates0144.C4620, NewCertificates0144.C4621, NewCertificates0144.C4622, NewCertificates0144.C4623, NewCertificates0144.C4624, NewCertificates0144.C4625, NewCertificates0144.C4626, NewCertificates0144.C4627, NewCertificates0144.C4628, NewCertificates0144.C4629, NewCertificates0144.C4630, NewCertificates0144.C4631, NewCertificates0144.C4632, NewCertificates0144.C4633, NewCertificates0144.C4634, NewCertificates0144.C4635, NewCertificates0144.C4636, NewCertificates0144.C4637}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,3)}
theorem doubled_enumeration : ((supportEdges 7031408092937980032).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 7031408092937980032 D i ∧ offSum 7031408092937980032 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 7031408092937980032 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 7031408092937980032 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 7031408092937980032 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 7031408092937980032 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport099
