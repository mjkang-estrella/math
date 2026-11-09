import SignedCatalogue
import NewCertificates0066
import NewCertificates0067
import NewCertificates0068
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport043
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 5, 6, 3, 1, 4, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0066.C2138, NewCertificates0066.C2139, NewCertificates0066.C2140, NewCertificates0066.C2141, NewCertificates0066.C2142, NewCertificates0066.C2143, NewCertificates0067.C2144, NewCertificates0067.C2145, NewCertificates0067.C2146, NewCertificates0067.C2147, NewCertificates0067.C2148, NewCertificates0067.C2149, NewCertificates0067.C2150, NewCertificates0067.C2151, NewCertificates0067.C2152, NewCertificates0067.C2153, NewCertificates0067.C2154, NewCertificates0067.C2155, NewCertificates0067.C2156, NewCertificates0067.C2157, NewCertificates0067.C2158, NewCertificates0067.C2159, NewCertificates0067.C2160, NewCertificates0067.C2161, NewCertificates0067.C2162, NewCertificates0067.C2163, NewCertificates0067.C2164, NewCertificates0067.C2165, NewCertificates0067.C2166, NewCertificates0067.C2167, NewCertificates0067.C2168, NewCertificates0067.C2169, NewCertificates0067.C2170, NewCertificates0067.C2171, NewCertificates0067.C2172, NewCertificates0067.C2173, NewCertificates0067.C2174, NewCertificates0067.C2175, NewCertificates0068.C2176, NewCertificates0068.C2177, NewCertificates0068.C2178, NewCertificates0068.C2179, NewCertificates0068.C2180, NewCertificates0068.C2181, NewCertificates0068.C2182, NewCertificates0068.C2183, NewCertificates0068.C2184, NewCertificates0068.C2185, NewCertificates0068.C2186, NewCertificates0068.C2187, NewCertificates0068.C2188, NewCertificates0068.C2189, NewCertificates0068.C2190, NewCertificates0068.C2191, NewCertificates0068.C2192, NewCertificates0068.C2193, NewCertificates0068.C2194, NewCertificates0068.C2195, NewCertificates0068.C2196, NewCertificates0068.C2197, NewCertificates0068.C2198, NewCertificates0068.C2199, NewCertificates0068.C2200, NewCertificates0068.C2201}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,4)}
theorem doubled_enumeration : ((supportEdges 7035405522577670272).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 7035405522577670272 D i ∧ offSum 7035405522577670272 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 7035405522577670272 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 7035405522577670272 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 7035405522577670272 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 7035405522577670272 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 7035405522577670272 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport043
