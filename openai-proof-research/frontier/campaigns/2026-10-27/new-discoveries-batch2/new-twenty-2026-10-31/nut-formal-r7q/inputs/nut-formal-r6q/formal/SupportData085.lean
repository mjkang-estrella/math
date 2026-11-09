import SignedCatalogue
import NewCertificates0122
import NewCertificates0123
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport085
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 2, 5, 6, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0122.C3926, NewCertificates0122.C3927, NewCertificates0122.C3928, NewCertificates0122.C3929, NewCertificates0122.C3930, NewCertificates0122.C3931, NewCertificates0122.C3932, NewCertificates0122.C3933, NewCertificates0122.C3934, NewCertificates0122.C3935, NewCertificates0123.C3936, NewCertificates0123.C3937, NewCertificates0123.C3938, NewCertificates0123.C3939, NewCertificates0123.C3940, NewCertificates0123.C3941, NewCertificates0123.C3942, NewCertificates0123.C3943, NewCertificates0123.C3944, NewCertificates0123.C3945, NewCertificates0123.C3946, NewCertificates0123.C3947, NewCertificates0123.C3948, NewCertificates0123.C3949, NewCertificates0123.C3950, NewCertificates0123.C3951, NewCertificates0123.C3952, NewCertificates0123.C3953, NewCertificates0123.C3954, NewCertificates0123.C3955, NewCertificates0123.C3956, NewCertificates0123.C3957}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 516315457638686848).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 516315457638686848 D i ∧ offSum 516315457638686848 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 516315457638686848 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 516315457638686848 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 516315457638686848 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport085
