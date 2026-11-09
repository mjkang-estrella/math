import HalfPlane
namespace ContactPilot
noncomputable section

def edgeList : List (Fin 5 × Fin 5) := [(0,1),(0,2),(0,3),(1,3),(2,4),(3,4)]

def candidateGraph : SimpleGraph (Fin 5) where
  Adj i j := (i,j) ∈ edgeList ∨ (j,i) ∈ edgeList
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i; fin_cases i <;> decide⟩

def candidateColors (i : Fin 5) : Bool := decide (i = 0 ∨ i = 3 ∨ i = 4)

theorem nearest_w_one : NearestWDistance candidateGraph candidateColors 0 1 := by
  constructor
  · refine ⟨1, by decide, SimpleGraph.Walk.cons (by change (0,1) ∈ edgeList ∨ (1,0) ∈ edgeList; simp [edgeList]) .nil, rfl⟩
  · intro j hj p
    by_contra hn
    have hz : p.length = 0 := by omega
    have he : (0:Fin 5) = j := p.eq_of_length_eq_zero hz
    subst j
    simp [candidateColors] at hj

/-- Explicit root paths certify connectedness without deciding reachability. -/
theorem root_reaches_all : ∀ j : Fin 5, Nonempty (candidateGraph.Walk 0 j) := by
  intro j
  fin_cases j
  · exact ⟨.nil⟩
  · exact ⟨.cons (by change (0,1) ∈ edgeList ∨ (1,0) ∈ edgeList; simp [edgeList]) .nil⟩
  · exact ⟨.cons (by change (0,2) ∈ edgeList ∨ (2,0) ∈ edgeList; simp [edgeList]) .nil⟩
  · exact ⟨.cons (by change (0,3) ∈ edgeList ∨ (3,0) ∈ edgeList; simp [edgeList]) .nil⟩
  · exact ⟨.cons (show candidateGraph.Adj 0 3 by
      change (0,3) ∈ edgeList ∨ (3,0) ∈ edgeList; simp [edgeList])
      (.cons (show candidateGraph.Adj 3 4 by
        change (3,4) ∈ edgeList ∨ (4,3) ∈ edgeList; simp [edgeList]) .nil)⟩

theorem colors_admissible : candidateColors 0 = true ∧
    candidateColors 1 = false ∧ candidateColors 2 = false ∧
    candidateColors 3 = true ∧ candidateColors 4 = true := by decide

def N (z w : ℂ) : ℂ := (w*z-w-1)*(w*z+w-1)
def Q (z w : ℂ) : ℂ := -w^2*z^3+2*w^2*z+4*w*z^2+2*w*z-w-3*z

def candidateMatrix (z w : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![-z,1,1,1,0; 1,-w,0,1,0; 1,0,-w,0,1; 1,1,0,-z,1; 0,0,1,1,-z]

theorem resolvent_matrix (z w : ℂ) :
    resolventMatrix candidateGraph candidateColors z w = candidateMatrix z w := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [resolventMatrix, candidateGraph, edgeList, candidateColors,
      candidateMatrix, Matrix.sub_apply, Matrix.diagonal_apply]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem candidate_det (z w : ℂ) : (candidateMatrix z w).det = Q z w := by
  simp [candidateMatrix, Matrix.det_succ_row_zero, Fin.succAbove,
    Fin.sum_univ_succ, Matrix.submatrix_apply, Q]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem candidate_adjugate (z w : ℂ) : (candidateMatrix z w).adjugate 0 0 = N z w := by
  rw [Matrix.adjugate_apply]
  simp [candidateMatrix, Matrix.det_succ_row_zero, Fin.succAbove,
    Fin.sum_univ_succ, Matrix.submatrix_apply, Matrix.updateRow_apply, Pi.single_apply, N]
  ring

theorem graph_quotient (z w : ℂ) :
    graphFunction candidateGraph candidateColors 0 z w = N z w / Q z w := by
  unfold graphFunction
  rw [resolvent_matrix, Matrix.inv_def, candidate_det]
  simp only [Matrix.smul_apply, smul_eq_mul, candidate_adjugate]
  simp [div_eq_mul_inv, mul_comm]

/-- Exact identity tying the cleared local polynomial to the resolvent quotient. -/
theorem R_from_quotient (x w : ℂ) (hx : x ≠ 0) :
    R x w = x^3*(Q (-1/x) w-Complex.I*N (-1/x) w) := by
  unfold R A B C Q N
  field_simp
  ring
end
end ContactPilot
