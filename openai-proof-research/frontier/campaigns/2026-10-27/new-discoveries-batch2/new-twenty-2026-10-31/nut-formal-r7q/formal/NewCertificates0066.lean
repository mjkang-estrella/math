import VerifiedDet
namespace Nut8.NewCertificates0066
def C2112 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2112 : C2112.det = (71 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2112 : ¬ (C2112.det = 0 ∧ ∀ i, C2112.adjugate i i ≠ 0) := by
  intro h
  have := certificate2112
  rw [h.1] at this
  norm_num at this
def C2113 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2113 : C2113.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2113 : ¬ (C2113.det = 0 ∧ ∀ i, C2113.adjugate i i ≠ 0) := by
  intro h
  have := certificate2113
  rw [h.1] at this
  norm_num at this
def C2114 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2114 : C2114.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2114 : ¬ (C2114.det = 0 ∧ ∀ i, C2114.adjugate i i ≠ 0) := by
  intro h
  have := certificate2114
  rw [h.1] at this
  norm_num at this
def C2115 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2115 : C2115.det = (71 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2115 : ¬ (C2115.det = 0 ∧ ∀ i, C2115.adjugate i i ≠ 0) := by
  intro h
  have := certificate2115
  rw [h.1] at this
  norm_num at this
def C2116 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2116 : C2116.det = (51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2116 : ¬ (C2116.det = 0 ∧ ∀ i, C2116.adjugate i i ≠ 0) := by
  intro h
  have := certificate2116
  rw [h.1] at this
  norm_num at this
def C2117 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2117 : C2117.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2117 : ¬ (C2117.det = 0 ∧ ∀ i, C2117.adjugate i i ≠ 0) := by
  intro h
  have := certificate2117
  rw [h.1] at this
  norm_num at this
def C2118 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2118 : C2118.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2118 : ¬ (C2118.det = 0 ∧ ∀ i, C2118.adjugate i i ≠ 0) := by
  intro h
  have := certificate2118
  rw [h.1] at this
  norm_num at this
def C2119 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2119 : C2119.det = (-53 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2119 : ¬ (C2119.det = 0 ∧ ∀ i, C2119.adjugate i i ≠ 0) := by
  intro h
  have := certificate2119
  rw [h.1] at this
  norm_num at this
def C2120 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2120 : C2120.det = (-49 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2120 : ¬ (C2120.det = 0 ∧ ∀ i, C2120.adjugate i i ≠ 0) := by
  intro h
  have := certificate2120
  rw [h.1] at this
  norm_num at this
def C2121 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2121 : C2121.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2121 : ¬ (C2121.det = 0 ∧ ∀ i, C2121.adjugate i i ≠ 0) := by
  intro h
  have := certificate2121
  rw [h.1] at this
  norm_num at this
def C2122 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2122 : C2122.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2122 : ¬ (C2122.det = 0 ∧ ∀ i, C2122.adjugate i i ≠ 0) := by
  intro h
  have := certificate2122
  rw [h.1] at this
  norm_num at this
def C2123 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2123 : C2123.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2123 : ¬ (C2123.det = 0 ∧ ∀ i, C2123.adjugate i i ≠ 0) := by
  intro h
  have := certificate2123
  rw [h.1] at this
  norm_num at this
def C2124 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2124 : C2124.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2124 : ¬ (C2124.det = 0 ∧ ∀ i, C2124.adjugate i i ≠ 0) := by
  intro h
  have := certificate2124
  rw [h.1] at this
  norm_num at this
def C2125 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2125 : C2125.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2125 : ¬ (C2125.det = 0 ∧ ∀ i, C2125.adjugate i i ≠ 0) := by
  intro h
  have := certificate2125
  rw [h.1] at this
  norm_num at this
def C2126 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2126 : C2126.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2126 : ¬ (C2126.det = 0 ∧ ∀ i, C2126.adjugate i i ≠ 0) := by
  intro h
  have := certificate2126
  rw [h.1] at this
  norm_num at this
def C2127 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2127 : C2127.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2127 : ¬ (C2127.det = 0 ∧ ∀ i, C2127.adjugate i i ≠ 0) := by
  intro h
  have := certificate2127
  rw [h.1] at this
  norm_num at this
def C2128 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2128 : C2128.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2128 : ¬ (C2128.det = 0 ∧ ∀ i, C2128.adjugate i i ≠ 0) := by
  intro h
  have := certificate2128
  rw [h.1] at this
  norm_num at this
def C2129 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2129 : C2129.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2129 : ¬ (C2129.det = 0 ∧ ∀ i, C2129.adjugate i i ≠ 0) := by
  intro h
  have := certificate2129
  rw [h.1] at this
  norm_num at this
def C2130 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2130 : C2130.det = (-67 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2130 : ¬ (C2130.det = 0 ∧ ∀ i, C2130.adjugate i i ≠ 0) := by
  intro h
  have := certificate2130
  rw [h.1] at this
  norm_num at this
def C2131 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2131 : C2131.det = (-47 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2131 : ¬ (C2131.det = 0 ∧ ∀ i, C2131.adjugate i i ≠ 0) := by
  intro h
  have := certificate2131
  rw [h.1] at this
  norm_num at this
def C2132 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2132 : C2132.det = (69 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2132 : ¬ (C2132.det = 0 ∧ ∀ i, C2132.adjugate i i ≠ 0) := by
  intro h
  have := certificate2132
  rw [h.1] at this
  norm_num at this
def C2133 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2133 : C2133.det = (57 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2133 : ¬ (C2133.det = 0 ∧ ∀ i, C2133.adjugate i i ≠ 0) := by
  intro h
  have := certificate2133
  rw [h.1] at this
  norm_num at this
def C2134 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2134 : C2134.det = (57 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2134 : ¬ (C2134.det = 0 ∧ ∀ i, C2134.adjugate i i ≠ 0) := by
  intro h
  have := certificate2134
  rw [h.1] at this
  norm_num at this
def C2135 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2135 : C2135.det = (69 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2135 : ¬ (C2135.det = 0 ∧ ∀ i, C2135.adjugate i i ≠ 0) := by
  intro h
  have := certificate2135
  rw [h.1] at this
  norm_num at this
def C2136 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate2136 : C2136.det = (-47 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2136 : ¬ (C2136.det = 0 ∧ ∀ i, C2136.adjugate i i ≠ 0) := by
  intro h
  have := certificate2136
  rw [h.1] at this
  norm_num at this
def C2137 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate2137 : C2137.det = (-67 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2137 : ¬ (C2137.det = 0 ∧ ∀ i, C2137.adjugate i i ≠ 0) := by
  intro h
  have := certificate2137
  rw [h.1] at this
  norm_num at this
def C2138 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2138 : C2138.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2138 : ¬ (C2138.det = 0 ∧ ∀ i, C2138.adjugate i i ≠ 0) := by
  intro h
  have := certificate2138
  rw [h.1] at this
  norm_num at this
def C2139 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2139 : C2139.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2139 : ¬ (C2139.det = 0 ∧ ∀ i, C2139.adjugate i i ≠ 0) := by
  intro h
  have := certificate2139
  rw [h.1] at this
  norm_num at this
def C2140 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2140 : C2140.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2140 : ¬ (C2140.det = 0 ∧ ∀ i, C2140.adjugate i i ≠ 0) := by
  intro h
  have := certificate2140
  rw [h.1] at this
  norm_num at this
def C2141 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate2141 : C2141.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2141 : ¬ (C2141.det = 0 ∧ ∀ i, C2141.adjugate i i ≠ 0) := by
  intro h
  have := certificate2141
  rw [h.1] at this
  norm_num at this
def C2142 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2142 : C2142.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2142 : ¬ (C2142.det = 0 ∧ ∀ i, C2142.adjugate i i ≠ 0) := by
  intro h
  have := certificate2142
  rw [h.1] at this
  norm_num at this
def C2143 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate2143 : C2143.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2143 : ¬ (C2143.det = 0 ∧ ∀ i, C2143.adjugate i i ≠ 0) := by
  intro h
  have := certificate2143
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0066
