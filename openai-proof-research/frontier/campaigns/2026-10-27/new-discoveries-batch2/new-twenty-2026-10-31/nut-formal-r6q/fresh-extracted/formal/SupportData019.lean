import SignedCatalogue
import NewCertificates0027
import NewCertificates0028
import NewCertificates0029
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport019
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 5, 3, 6, 4, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 3, 5, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0027.C888, NewCertificates0027.C889, NewCertificates0027.C890, NewCertificates0027.C891, NewCertificates0027.C892, NewCertificates0027.C893, NewCertificates0027.C894, NewCertificates0027.C895, NewCertificates0028.C896, NewCertificates0028.C897, NewCertificates0028.C898, NewCertificates0028.C899, NewCertificates0028.C900, NewCertificates0028.C901, NewCertificates0028.C902, NewCertificates0028.C903, NewCertificates0028.C904, NewCertificates0028.C905, NewCertificates0028.C906, NewCertificates0028.C907, NewCertificates0028.C908, NewCertificates0028.C909, NewCertificates0028.C910, NewCertificates0028.C911, NewCertificates0028.C912, NewCertificates0028.C913, NewCertificates0028.C914, NewCertificates0028.C915, NewCertificates0028.C916, NewCertificates0028.C917, NewCertificates0028.C918, NewCertificates0028.C919, NewCertificates0028.C920, NewCertificates0028.C921, NewCertificates0028.C922, NewCertificates0028.C923, NewCertificates0028.C924, NewCertificates0028.C925, NewCertificates0028.C926, NewCertificates0028.C927, NewCertificates0029.C928, NewCertificates0029.C929, NewCertificates0029.C930, NewCertificates0029.C931, NewCertificates0029.C932, NewCertificates0029.C933, NewCertificates0029.C934, NewCertificates0029.C935}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,4)}
theorem doubled_enumeration : ((supportEdges 2537998586018300032).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2537998586018300032 D i ∧ offSum 2537998586018300032 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 2537998586018300032 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2537998586018300032 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2537998586018300032 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2537998586018300032 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport019
