import VerifiedDet
namespace Nut8.NewCertificates0185
def C5920 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5920 : C5920.det = (225 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5920 : ¬ (C5920.det = 0 ∧ ∀ i, C5920.adjugate i i ≠ 0) := by
  intro h
  have := certificate5920
  rw [h.1] at this
  norm_num at this
def C5921 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5921 : C5921.det = (289 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5921 : ¬ (C5921.det = 0 ∧ ∀ i, C5921.adjugate i i ≠ 0) := by
  intro h
  have := certificate5921
  rw [h.1] at this
  norm_num at this
def C5922 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5922 : C5922.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5922 : ¬ (C5922.det = 0 ∧ ∀ i, C5922.adjugate i i ≠ 0) := by
  intro h
  have := certificate5922
  rw [h.1] at this
  norm_num at this
def C5923 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5923 : C5923.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5923 : ¬ (C5923.det = 0 ∧ ∀ i, C5923.adjugate i i ≠ 0) := by
  intro h
  have := certificate5923
  rw [h.1] at this
  norm_num at this
def C5924 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5924 : C5924.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5924 : ¬ (C5924.det = 0 ∧ ∀ i, C5924.adjugate i i ≠ 0) := by
  intro h
  have := certificate5924
  rw [h.1] at this
  norm_num at this
def C5925 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5925 : C5925.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5925 : ¬ (C5925.det = 0 ∧ ∀ i, C5925.adjugate i i ≠ 0) := by
  intro h
  have := certificate5925
  rw [h.1] at this
  norm_num at this
def C5926 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5926 : C5926.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5926 : ¬ (C5926.det = 0 ∧ ∀ i, C5926.adjugate i i ≠ 0) := by
  intro h
  have := certificate5926
  rw [h.1] at this
  norm_num at this
def C5927 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5927 : C5927.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5927 : ¬ (C5927.det = 0 ∧ ∀ i, C5927.adjugate i i ≠ 0) := by
  intro h
  have := certificate5927
  rw [h.1] at this
  norm_num at this
def C5928 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5928 : C5928.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5928 : ¬ (C5928.det = 0 ∧ ∀ i, C5928.adjugate i i ≠ 0) := by
  intro h
  have := certificate5928
  rw [h.1] at this
  norm_num at this
def C5929 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5929 : C5929.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5929 : ¬ (C5929.det = 0 ∧ ∀ i, C5929.adjugate i i ≠ 0) := by
  intro h
  have := certificate5929
  rw [h.1] at this
  norm_num at this
def C5930 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5930 : C5930.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5930 : ¬ (C5930.det = 0 ∧ ∀ i, C5930.adjugate i i ≠ 0) := by
  intro h
  have := certificate5930
  rw [h.1] at this
  norm_num at this
def C5931 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5931 : C5931.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5931 : ¬ (C5931.det = 0 ∧ ∀ i, C5931.adjugate i i ≠ 0) := by
  intro h
  have := certificate5931
  rw [h.1] at this
  norm_num at this
def C5932 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5932 : C5932.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5932 : ¬ (C5932.det = 0 ∧ ∀ i, C5932.adjugate i i ≠ 0) := by
  intro h
  have := certificate5932
  rw [h.1] at this
  norm_num at this
def C5933 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5933 : C5933.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5933 : ¬ (C5933.det = 0 ∧ ∀ i, C5933.adjugate i i ≠ 0) := by
  intro h
  have := certificate5933
  rw [h.1] at this
  norm_num at this
def C5934 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5934 : C5934.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5934 : ¬ (C5934.det = 0 ∧ ∀ i, C5934.adjugate i i ≠ 0) := by
  intro h
  have := certificate5934
  rw [h.1] at this
  norm_num at this
def C5935 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5935 : C5935.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5935 : ¬ (C5935.det = 0 ∧ ∀ i, C5935.adjugate i i ≠ 0) := by
  intro h
  have := certificate5935
  rw [h.1] at this
  norm_num at this
def C5936 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5936 : C5936.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5936 : ¬ (C5936.det = 0 ∧ ∀ i, C5936.adjugate i i ≠ 0) := by
  intro h
  have := certificate5936
  rw [h.1] at this
  norm_num at this
def C5937 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5937 : C5937.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5937 : ¬ (C5937.det = 0 ∧ ∀ i, C5937.adjugate i i ≠ 0) := by
  intro h
  have := certificate5937
  rw [h.1] at this
  norm_num at this
def C5938 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5938 : C5938.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5938 : ¬ (C5938.det = 0 ∧ ∀ i, C5938.adjugate i i ≠ 0) := by
  intro h
  have := certificate5938
  rw [h.1] at this
  norm_num at this
def C5939 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5939 : C5939.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5939 : ¬ (C5939.det = 0 ∧ ∀ i, C5939.adjugate i i ≠ 0) := by
  intro h
  have := certificate5939
  rw [h.1] at this
  norm_num at this
def C5940 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5940 : C5940.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5940 : ¬ (C5940.det = 0 ∧ ∀ i, C5940.adjugate i i ≠ 0) := by
  intro h
  have := certificate5940
  rw [h.1] at this
  norm_num at this
def C5941 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5941 : C5941.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5941 : ¬ (C5941.det = 0 ∧ ∀ i, C5941.adjugate i i ≠ 0) := by
  intro h
  have := certificate5941
  rw [h.1] at this
  norm_num at this
def C5942 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5942 : C5942.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5942 : ¬ (C5942.det = 0 ∧ ∀ i, C5942.adjugate i i ≠ 0) := by
  intro h
  have := certificate5942
  rw [h.1] at this
  norm_num at this
def C5943 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5943 : C5943.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5943 : ¬ (C5943.det = 0 ∧ ∀ i, C5943.adjugate i i ≠ 0) := by
  intro h
  have := certificate5943
  rw [h.1] at this
  norm_num at this
def C5944 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5944 : C5944.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5944 : ¬ (C5944.det = 0 ∧ ∀ i, C5944.adjugate i i ≠ 0) := by
  intro h
  have := certificate5944
  rw [h.1] at this
  norm_num at this
def C5945 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5945 : C5945.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5945 : ¬ (C5945.det = 0 ∧ ∀ i, C5945.adjugate i i ≠ 0) := by
  intro h
  have := certificate5945
  rw [h.1] at this
  norm_num at this
def C5946 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5946 : C5946.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5946 : ¬ (C5946.det = 0 ∧ ∀ i, C5946.adjugate i i ≠ 0) := by
  intro h
  have := certificate5946
  rw [h.1] at this
  norm_num at this
def C5947 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5947 : C5947.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5947 : ¬ (C5947.det = 0 ∧ ∀ i, C5947.adjugate i i ≠ 0) := by
  intro h
  have := certificate5947
  rw [h.1] at this
  norm_num at this
def C5948 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5948 : C5948.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5948 : ¬ (C5948.det = 0 ∧ ∀ i, C5948.adjugate i i ≠ 0) := by
  intro h
  have := certificate5948
  rw [h.1] at this
  norm_num at this
def C5949 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5949 : C5949.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5949 : ¬ (C5949.det = 0 ∧ ∀ i, C5949.adjugate i i ≠ 0) := by
  intro h
  have := certificate5949
  rw [h.1] at this
  norm_num at this
def C5950 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5950 : C5950.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5950 : ¬ (C5950.det = 0 ∧ ∀ i, C5950.adjugate i i ≠ 0) := by
  intro h
  have := certificate5950
  rw [h.1] at this
  norm_num at this
def C5951 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5951 : C5951.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5951 : ¬ (C5951.det = 0 ∧ ∀ i, C5951.adjugate i i ≠ 0) := by
  intro h
  have := certificate5951
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0185
