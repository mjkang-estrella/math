import SupportData043
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport043
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0066.C2138, NewCertificates0066.C2139, NewCertificates0066.C2140, NewCertificates0066.C2141, NewCertificates0066.C2142, NewCertificates0066.C2143, NewCertificates0067.C2144, NewCertificates0067.C2145, NewCertificates0067.C2146, NewCertificates0067.C2147, NewCertificates0067.C2148, NewCertificates0067.C2149, NewCertificates0067.C2150, NewCertificates0067.C2151, NewCertificates0067.C2152, NewCertificates0067.C2153, NewCertificates0067.C2154, NewCertificates0067.C2155, NewCertificates0067.C2156, NewCertificates0067.C2157, NewCertificates0067.C2158, NewCertificates0067.C2159, NewCertificates0067.C2160, NewCertificates0067.C2161, NewCertificates0067.C2162, NewCertificates0067.C2163, NewCertificates0067.C2164, NewCertificates0067.C2165, NewCertificates0067.C2166, NewCertificates0067.C2167, NewCertificates0067.C2168, NewCertificates0067.C2169} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0067.C2170, NewCertificates0067.C2171, NewCertificates0067.C2172, NewCertificates0067.C2173, NewCertificates0067.C2174, NewCertificates0067.C2175, NewCertificates0068.C2176, NewCertificates0068.C2177, NewCertificates0068.C2178, NewCertificates0068.C2179, NewCertificates0068.C2180, NewCertificates0068.C2181, NewCertificates0068.C2182, NewCertificates0068.C2183, NewCertificates0068.C2184, NewCertificates0068.C2185} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0068.C2186, NewCertificates0068.C2187, NewCertificates0068.C2188, NewCertificates0068.C2189, NewCertificates0068.C2190, NewCertificates0068.C2191, NewCertificates0068.C2192, NewCertificates0068.C2193, NewCertificates0068.C2194, NewCertificates0068.C2195, NewCertificates0068.C2196, NewCertificates0068.C2197, NewCertificates0068.C2198, NewCertificates0068.C2199, NewCertificates0068.C2200, NewCertificates0068.C2201} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0066.obstruction2138
  · exact NewCertificates0066.obstruction2139
  · exact NewCertificates0066.obstruction2140
  · exact NewCertificates0066.obstruction2141
  · exact NewCertificates0066.obstruction2142
  · exact NewCertificates0066.obstruction2143
  · exact NewCertificates0067.obstruction2144
  · exact NewCertificates0067.obstruction2145
  · exact NewCertificates0067.obstruction2146
  · exact NewCertificates0067.obstruction2147
  · exact NewCertificates0067.obstruction2148
  · exact NewCertificates0067.obstruction2149
  · exact NewCertificates0067.obstruction2150
  · exact NewCertificates0067.obstruction2151
  · exact NewCertificates0067.obstruction2152
  · exact NewCertificates0067.obstruction2153
  · exact NewCertificates0067.obstruction2154
  · exact NewCertificates0067.obstruction2155
  · exact NewCertificates0067.obstruction2156
  · exact NewCertificates0067.obstruction2157
  · exact NewCertificates0067.obstruction2158
  · exact NewCertificates0067.obstruction2159
  · exact NewCertificates0067.obstruction2160
  · exact NewCertificates0067.obstruction2161
  · exact NewCertificates0067.obstruction2162
  · exact NewCertificates0067.obstruction2163
  · exact NewCertificates0067.obstruction2164
  · exact NewCertificates0067.obstruction2165
  · exact NewCertificates0067.obstruction2166
  · exact NewCertificates0067.obstruction2167
  · exact NewCertificates0067.obstruction2168
  · exact NewCertificates0067.obstruction2169
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0067.obstruction2170
  · exact NewCertificates0067.obstruction2171
  · exact NewCertificates0067.obstruction2172
  · exact NewCertificates0067.obstruction2173
  · exact NewCertificates0067.obstruction2174
  · exact NewCertificates0067.obstruction2175
  · exact NewCertificates0068.obstruction2176
  · exact NewCertificates0068.obstruction2177
  · exact NewCertificates0068.obstruction2178
  · exact NewCertificates0068.obstruction2179
  · exact NewCertificates0068.obstruction2180
  · exact NewCertificates0068.obstruction2181
  · exact NewCertificates0068.obstruction2182
  · exact NewCertificates0068.obstruction2183
  · exact NewCertificates0068.obstruction2184
  · exact NewCertificates0068.obstruction2185
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0068.obstruction2186
  · exact NewCertificates0068.obstruction2187
  · exact NewCertificates0068.obstruction2188
  · exact NewCertificates0068.obstruction2189
  · exact NewCertificates0068.obstruction2190
  · exact NewCertificates0068.obstruction2191
  · exact NewCertificates0068.obstruction2192
  · exact NewCertificates0068.obstruction2193
  · exact NewCertificates0068.obstruction2194
  · exact NewCertificates0068.obstruction2195
  · exact NewCertificates0068.obstruction2196
  · exact NewCertificates0068.obstruction2197
  · exact NewCertificates0068.obstruction2198
  · exact NewCertificates0068.obstruction2199
  · exact NewCertificates0068.obstruction2200
  · exact NewCertificates0068.obstruction2201
end Nut8.FiniteSupport043
