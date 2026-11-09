import SupportData042
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport042
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0065.C2090, NewCertificates0065.C2091, NewCertificates0065.C2092, NewCertificates0065.C2093, NewCertificates0065.C2094, NewCertificates0065.C2095, NewCertificates0065.C2096, NewCertificates0065.C2097, NewCertificates0065.C2098, NewCertificates0065.C2099, NewCertificates0065.C2100, NewCertificates0065.C2101, NewCertificates0065.C2102, NewCertificates0065.C2103, NewCertificates0065.C2104, NewCertificates0065.C2105, NewCertificates0065.C2106, NewCertificates0065.C2107, NewCertificates0065.C2108, NewCertificates0065.C2109, NewCertificates0065.C2110, NewCertificates0065.C2111, NewCertificates0066.C2112, NewCertificates0066.C2113, NewCertificates0066.C2114, NewCertificates0066.C2115, NewCertificates0066.C2116, NewCertificates0066.C2117, NewCertificates0066.C2118, NewCertificates0066.C2119, NewCertificates0066.C2120, NewCertificates0066.C2121} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0066.C2122, NewCertificates0066.C2123, NewCertificates0066.C2124, NewCertificates0066.C2125, NewCertificates0066.C2126, NewCertificates0066.C2127, NewCertificates0066.C2128, NewCertificates0066.C2129, NewCertificates0066.C2130, NewCertificates0066.C2131, NewCertificates0066.C2132, NewCertificates0066.C2133, NewCertificates0066.C2134, NewCertificates0066.C2135, NewCertificates0066.C2136, NewCertificates0066.C2137} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0065.obstruction2090
  · exact NewCertificates0065.obstruction2091
  · exact NewCertificates0065.obstruction2092
  · exact NewCertificates0065.obstruction2093
  · exact NewCertificates0065.obstruction2094
  · exact NewCertificates0065.obstruction2095
  · exact NewCertificates0065.obstruction2096
  · exact NewCertificates0065.obstruction2097
  · exact NewCertificates0065.obstruction2098
  · exact NewCertificates0065.obstruction2099
  · exact NewCertificates0065.obstruction2100
  · exact NewCertificates0065.obstruction2101
  · exact NewCertificates0065.obstruction2102
  · exact NewCertificates0065.obstruction2103
  · exact NewCertificates0065.obstruction2104
  · exact NewCertificates0065.obstruction2105
  · exact NewCertificates0065.obstruction2106
  · exact NewCertificates0065.obstruction2107
  · exact NewCertificates0065.obstruction2108
  · exact NewCertificates0065.obstruction2109
  · exact NewCertificates0065.obstruction2110
  · exact NewCertificates0065.obstruction2111
  · exact NewCertificates0066.obstruction2112
  · exact NewCertificates0066.obstruction2113
  · exact NewCertificates0066.obstruction2114
  · exact NewCertificates0066.obstruction2115
  · exact NewCertificates0066.obstruction2116
  · exact NewCertificates0066.obstruction2117
  · exact NewCertificates0066.obstruction2118
  · exact NewCertificates0066.obstruction2119
  · exact NewCertificates0066.obstruction2120
  · exact NewCertificates0066.obstruction2121
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0066.obstruction2122
  · exact NewCertificates0066.obstruction2123
  · exact NewCertificates0066.obstruction2124
  · exact NewCertificates0066.obstruction2125
  · exact NewCertificates0066.obstruction2126
  · exact NewCertificates0066.obstruction2127
  · exact NewCertificates0066.obstruction2128
  · exact NewCertificates0066.obstruction2129
  · exact NewCertificates0066.obstruction2130
  · exact NewCertificates0066.obstruction2131
  · exact NewCertificates0066.obstruction2132
  · exact NewCertificates0066.obstruction2133
  · exact NewCertificates0066.obstruction2134
  · exact NewCertificates0066.obstruction2135
  · exact NewCertificates0066.obstruction2136
  · exact NewCertificates0066.obstruction2137
end Nut8.FiniteSupport042
