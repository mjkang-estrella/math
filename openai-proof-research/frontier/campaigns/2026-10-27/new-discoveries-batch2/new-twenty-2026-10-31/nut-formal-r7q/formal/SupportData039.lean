import SignedCatalogue
import NewCertificates0061
import NewCertificates0062
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport039
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 3, 5, 6, 4, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0061.C1962, NewCertificates0061.C1963, NewCertificates0061.C1964, NewCertificates0061.C1965, NewCertificates0061.C1966, NewCertificates0061.C1967, NewCertificates0061.C1968, NewCertificates0061.C1969, NewCertificates0061.C1970, NewCertificates0061.C1971, NewCertificates0061.C1972, NewCertificates0061.C1973, NewCertificates0061.C1974, NewCertificates0061.C1975, NewCertificates0061.C1976, NewCertificates0061.C1977, NewCertificates0061.C1978, NewCertificates0061.C1979, NewCertificates0061.C1980, NewCertificates0061.C1981, NewCertificates0061.C1982, NewCertificates0061.C1983, NewCertificates0062.C1984, NewCertificates0062.C1985, NewCertificates0062.C1986, NewCertificates0062.C1987, NewCertificates0062.C1988, NewCertificates0062.C1989, NewCertificates0062.C1990, NewCertificates0062.C1991, NewCertificates0062.C1992, NewCertificates0062.C1993}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 942972407950360704).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 942972407950360704 D i ∧ offSum 942972407950360704 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 942972407950360704 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 942972407950360704 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 942972407950360704 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport039
