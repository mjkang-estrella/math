import SignedCatalogue
import NewCertificates0153
import NewCertificates0154
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport105
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 4, 6, 5, 1, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0153.C4902, NewCertificates0153.C4903, NewCertificates0153.C4904, NewCertificates0153.C4905, NewCertificates0153.C4906, NewCertificates0153.C4907, NewCertificates0153.C4908, NewCertificates0153.C4909, NewCertificates0153.C4910, NewCertificates0153.C4911, NewCertificates0153.C4912, NewCertificates0153.C4913, NewCertificates0153.C4914, NewCertificates0153.C4915, NewCertificates0153.C4916, NewCertificates0153.C4917, NewCertificates0153.C4918, NewCertificates0153.C4919, NewCertificates0153.C4920, NewCertificates0153.C4921, NewCertificates0153.C4922, NewCertificates0153.C4923, NewCertificates0153.C4924, NewCertificates0153.C4925, NewCertificates0153.C4926, NewCertificates0153.C4927, NewCertificates0154.C4928, NewCertificates0154.C4929, NewCertificates0154.C4930, NewCertificates0154.C4931, NewCertificates0154.C4932, NewCertificates0154.C4933, NewCertificates0154.C4934, NewCertificates0154.C4935, NewCertificates0154.C4936, NewCertificates0154.C4937, NewCertificates0154.C4938, NewCertificates0154.C4939, NewCertificates0154.C4940, NewCertificates0154.C4941, NewCertificates0154.C4942, NewCertificates0154.C4943, NewCertificates0154.C4944, NewCertificates0154.C4945, NewCertificates0154.C4946, NewCertificates0154.C4947, NewCertificates0154.C4948, NewCertificates0154.C4949}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,2)}
theorem doubled_enumeration : ((supportEdges 1813354883993191552).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1813354883993191552 D i ∧ offSum 1813354883993191552 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1813354883993191552 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1813354883993191552 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1813354883993191552 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1813354883993191552 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport105
