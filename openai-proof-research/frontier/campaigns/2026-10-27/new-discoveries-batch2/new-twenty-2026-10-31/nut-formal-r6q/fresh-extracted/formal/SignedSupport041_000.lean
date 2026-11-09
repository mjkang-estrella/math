import SupportData041
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport041
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0063.C2042, NewCertificates0063.C2043, NewCertificates0063.C2044, NewCertificates0063.C2045, NewCertificates0063.C2046, NewCertificates0063.C2047, NewCertificates0064.C2048, NewCertificates0064.C2049, NewCertificates0064.C2050, NewCertificates0064.C2051, NewCertificates0064.C2052, NewCertificates0064.C2053, NewCertificates0064.C2054, NewCertificates0064.C2055, NewCertificates0064.C2056, NewCertificates0064.C2057, NewCertificates0064.C2058, NewCertificates0064.C2059, NewCertificates0064.C2060, NewCertificates0064.C2061, NewCertificates0064.C2062, NewCertificates0064.C2063, NewCertificates0064.C2064, NewCertificates0064.C2065, NewCertificates0064.C2066, NewCertificates0064.C2067, NewCertificates0064.C2068, NewCertificates0064.C2069, NewCertificates0064.C2070, NewCertificates0064.C2071, NewCertificates0064.C2072, NewCertificates0064.C2073} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0064.C2074, NewCertificates0064.C2075, NewCertificates0064.C2076, NewCertificates0064.C2077, NewCertificates0064.C2078, NewCertificates0064.C2079, NewCertificates0065.C2080, NewCertificates0065.C2081, NewCertificates0065.C2082, NewCertificates0065.C2083, NewCertificates0065.C2084, NewCertificates0065.C2085, NewCertificates0065.C2086, NewCertificates0065.C2087, NewCertificates0065.C2088, NewCertificates0065.C2089} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0063.obstruction2042
  · exact NewCertificates0063.obstruction2043
  · exact NewCertificates0063.obstruction2044
  · exact NewCertificates0063.obstruction2045
  · exact NewCertificates0063.obstruction2046
  · exact NewCertificates0063.obstruction2047
  · exact NewCertificates0064.obstruction2048
  · exact NewCertificates0064.obstruction2049
  · exact NewCertificates0064.obstruction2050
  · exact NewCertificates0064.obstruction2051
  · exact NewCertificates0064.obstruction2052
  · exact NewCertificates0064.obstruction2053
  · exact NewCertificates0064.obstruction2054
  · exact NewCertificates0064.obstruction2055
  · exact NewCertificates0064.obstruction2056
  · exact NewCertificates0064.obstruction2057
  · exact NewCertificates0064.obstruction2058
  · exact NewCertificates0064.obstruction2059
  · exact NewCertificates0064.obstruction2060
  · exact NewCertificates0064.obstruction2061
  · exact NewCertificates0064.obstruction2062
  · exact NewCertificates0064.obstruction2063
  · exact NewCertificates0064.obstruction2064
  · exact NewCertificates0064.obstruction2065
  · exact NewCertificates0064.obstruction2066
  · exact NewCertificates0064.obstruction2067
  · exact NewCertificates0064.obstruction2068
  · exact NewCertificates0064.obstruction2069
  · exact NewCertificates0064.obstruction2070
  · exact NewCertificates0064.obstruction2071
  · exact NewCertificates0064.obstruction2072
  · exact NewCertificates0064.obstruction2073
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0064.obstruction2074
  · exact NewCertificates0064.obstruction2075
  · exact NewCertificates0064.obstruction2076
  · exact NewCertificates0064.obstruction2077
  · exact NewCertificates0064.obstruction2078
  · exact NewCertificates0064.obstruction2079
  · exact NewCertificates0065.obstruction2080
  · exact NewCertificates0065.obstruction2081
  · exact NewCertificates0065.obstruction2082
  · exact NewCertificates0065.obstruction2083
  · exact NewCertificates0065.obstruction2084
  · exact NewCertificates0065.obstruction2085
  · exact NewCertificates0065.obstruction2086
  · exact NewCertificates0065.obstruction2087
  · exact NewCertificates0065.obstruction2088
  · exact NewCertificates0065.obstruction2089
end Nut8.FiniteSupport041
