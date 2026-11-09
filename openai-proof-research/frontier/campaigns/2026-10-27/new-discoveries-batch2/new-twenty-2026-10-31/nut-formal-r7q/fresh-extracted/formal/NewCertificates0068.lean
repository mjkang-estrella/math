import VerifiedDet
namespace Nut8.NewCertificates0068
def C2176 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2176 : C2176.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2176 : ¬ (C2176.det = 0 ∧ ∀ i, C2176.adjugate i i ≠ 0) := by
  intro h
  have := certificate2176
  rw [h.1] at this
  norm_num at this
def C2177 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2177 : C2177.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2177 : ¬ (C2177.det = 0 ∧ ∀ i, C2177.adjugate i i ≠ 0) := by
  intro h
  have := certificate2177
  rw [h.1] at this
  norm_num at this
def C2178 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2178 : C2178.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2178 : ¬ (C2178.det = 0 ∧ ∀ i, C2178.adjugate i i ≠ 0) := by
  intro h
  have := certificate2178
  rw [h.1] at this
  norm_num at this
def C2179 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2179 : C2179.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2179 : ¬ (C2179.det = 0 ∧ ∀ i, C2179.adjugate i i ≠ 0) := by
  intro h
  have := certificate2179
  rw [h.1] at this
  norm_num at this
def C2180 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2180 : C2180.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2180 : ¬ (C2180.det = 0 ∧ ∀ i, C2180.adjugate i i ≠ 0) := by
  intro h
  have := certificate2180
  rw [h.1] at this
  norm_num at this
def C2181 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2181 : C2181.det = (60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2181 : ¬ (C2181.det = 0 ∧ ∀ i, C2181.adjugate i i ≠ 0) := by
  intro h
  have := certificate2181
  rw [h.1] at this
  norm_num at this
def C2182 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2182 : C2182.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2182 : ¬ (C2182.det = 0 ∧ ∀ i, C2182.adjugate i i ≠ 0) := by
  intro h
  have := certificate2182
  rw [h.1] at this
  norm_num at this
def C2183 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2183 : C2183.det = (60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2183 : ¬ (C2183.det = 0 ∧ ∀ i, C2183.adjugate i i ≠ 0) := by
  intro h
  have := certificate2183
  rw [h.1] at this
  norm_num at this
def C2184 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2184 : C2184.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2184 : ¬ (C2184.det = 0 ∧ ∀ i, C2184.adjugate i i ≠ 0) := by
  intro h
  have := certificate2184
  rw [h.1] at this
  norm_num at this
def C2185 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2185 : C2185.det = (-72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2185 : ¬ (C2185.det = 0 ∧ ∀ i, C2185.adjugate i i ≠ 0) := by
  intro h
  have := certificate2185
  rw [h.1] at this
  norm_num at this
def C2186 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2186 : C2186.det = (-99 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2186 : ¬ (C2186.det = 0 ∧ ∀ i, C2186.adjugate i i ≠ 0) := by
  intro h
  have := certificate2186
  rw [h.1] at this
  norm_num at this
def C2187 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2187 : C2187.det = (93 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2187 : ¬ (C2187.det = 0 ∧ ∀ i, C2187.adjugate i i ≠ 0) := by
  intro h
  have := certificate2187
  rw [h.1] at this
  norm_num at this
def C2188 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2188 : C2188.det = (69 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2188 : ¬ (C2188.det = 0 ∧ ∀ i, C2188.adjugate i i ≠ 0) := by
  intro h
  have := certificate2188
  rw [h.1] at this
  norm_num at this
def C2189 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2189 : C2189.det = (-59 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2189 : ¬ (C2189.det = 0 ∧ ∀ i, C2189.adjugate i i ≠ 0) := by
  intro h
  have := certificate2189
  rw [h.1] at this
  norm_num at this
def C2190 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2190 : C2190.det = (69 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2190 : ¬ (C2190.det = 0 ∧ ∀ i, C2190.adjugate i i ≠ 0) := by
  intro h
  have := certificate2190
  rw [h.1] at this
  norm_num at this
def C2191 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2191 : C2191.det = (-59 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2191 : ¬ (C2191.det = 0 ∧ ∀ i, C2191.adjugate i i ≠ 0) := by
  intro h
  have := certificate2191
  rw [h.1] at this
  norm_num at this
def C2192 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2192 : C2192.det = (-35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2192 : ¬ (C2192.det = 0 ∧ ∀ i, C2192.adjugate i i ≠ 0) := by
  intro h
  have := certificate2192
  rw [h.1] at this
  norm_num at this
def C2193 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2193 : C2193.det = (29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2193 : ¬ (C2193.det = 0 ∧ ∀ i, C2193.adjugate i i ≠ 0) := by
  intro h
  have := certificate2193
  rw [h.1] at this
  norm_num at this
def C2194 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2194 : C2194.det = (29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2194 : ¬ (C2194.det = 0 ∧ ∀ i, C2194.adjugate i i ≠ 0) := by
  intro h
  have := certificate2194
  rw [h.1] at this
  norm_num at this
def C2195 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2195 : C2195.det = (-35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2195 : ¬ (C2195.det = 0 ∧ ∀ i, C2195.adjugate i i ≠ 0) := by
  intro h
  have := certificate2195
  rw [h.1] at this
  norm_num at this
def C2196 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2196 : C2196.det = (-59 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2196 : ¬ (C2196.det = 0 ∧ ∀ i, C2196.adjugate i i ≠ 0) := by
  intro h
  have := certificate2196
  rw [h.1] at this
  norm_num at this
def C2197 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2197 : C2197.det = (69 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2197 : ¬ (C2197.det = 0 ∧ ∀ i, C2197.adjugate i i ≠ 0) := by
  intro h
  have := certificate2197
  rw [h.1] at this
  norm_num at this
def C2198 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2198 : C2198.det = (-59 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2198 : ¬ (C2198.det = 0 ∧ ∀ i, C2198.adjugate i i ≠ 0) := by
  intro h
  have := certificate2198
  rw [h.1] at this
  norm_num at this
def C2199 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2199 : C2199.det = (69 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2199 : ¬ (C2199.det = 0 ∧ ∀ i, C2199.adjugate i i ≠ 0) := by
  intro h
  have := certificate2199
  rw [h.1] at this
  norm_num at this
def C2200 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2200 : C2200.det = (93 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2200 : ¬ (C2200.det = 0 ∧ ∀ i, C2200.adjugate i i ≠ 0) := by
  intro h
  have := certificate2200
  rw [h.1] at this
  norm_num at this
def C2201 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2201 : C2201.det = (-99 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2201 : ¬ (C2201.det = 0 ∧ ∀ i, C2201.adjugate i i ≠ 0) := by
  intro h
  have := certificate2201
  rw [h.1] at this
  norm_num at this
def C2202 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2202 : C2202.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2202 : ¬ (C2202.det = 0 ∧ ∀ i, C2202.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2202
def C2203 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2203 : C2203.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2203 : ¬ (C2203.det = 0 ∧ ∀ i, C2203.adjugate i i ≠ 0) := by
  intro h
  have := certificate2203
  rw [h.1] at this
  norm_num at this
def C2204 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2204 : C2204.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2204 : ¬ (C2204.det = 0 ∧ ∀ i, C2204.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2204
def C2205 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2205 : C2205.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2205 : ¬ (C2205.det = 0 ∧ ∀ i, C2205.adjugate i i ≠ 0) := by
  intro h
  have := certificate2205
  rw [h.1] at this
  norm_num at this
def C2206 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2206 : C2206.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2206 : ¬ (C2206.det = 0 ∧ ∀ i, C2206.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2206
def C2207 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2207 : C2207.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2207 : ¬ (C2207.det = 0 ∧ ∀ i, C2207.adjugate i i ≠ 0) := by
  intro h
  have := certificate2207
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0068
