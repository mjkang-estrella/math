import SignedCatalogue
import NewCertificates0060
import NewCertificates0061
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport038
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 6, 5, 1, 4, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0060.C1930, NewCertificates0060.C1931, NewCertificates0060.C1932, NewCertificates0060.C1933, NewCertificates0060.C1934, NewCertificates0060.C1935, NewCertificates0060.C1936, NewCertificates0060.C1937, NewCertificates0060.C1938, NewCertificates0060.C1939, NewCertificates0060.C1940, NewCertificates0060.C1941, NewCertificates0060.C1942, NewCertificates0060.C1943, NewCertificates0060.C1944, NewCertificates0060.C1945, NewCertificates0060.C1946, NewCertificates0060.C1947, NewCertificates0060.C1948, NewCertificates0060.C1949, NewCertificates0060.C1950, NewCertificates0060.C1951, NewCertificates0061.C1952, NewCertificates0061.C1953, NewCertificates0061.C1954, NewCertificates0061.C1955, NewCertificates0061.C1956, NewCertificates0061.C1957, NewCertificates0061.C1958, NewCertificates0061.C1959, NewCertificates0061.C1960, NewCertificates0061.C1961}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 5013100569034768512).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5013100569034768512 D i ∧ offSum 5013100569034768512 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 5013100569034768512 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5013100569034768512 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5013100569034768512 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport038
