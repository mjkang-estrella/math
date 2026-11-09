import Mathlib
set_option autoImplicit false
set_option warningAsError true
namespace RefinedSpectral
open Matrix

def witness : Matrix (Fin 4) (Fin 7) ℝ := fun i j =>
  if i.val < 3 ∨ j.val = 0 then 1 else 0

def candidate : Matrix (Fin 4) (Fin 6) ℝ := fun i j =>
  if i.val < 2 ∨ j.val < 5 then 1 else 0

theorem witness_edges : ∑ i : Fin 4, ∑ j : Fin 7, witness i j = 22 := by
  simp only [Fin.sum_univ_succ]
  norm_num [witness]

theorem candidate_edges : ∑ i : Fin 4, ∑ j : Fin 6, candidate i j = 22 := by
  simp only [Fin.sum_univ_succ]
  norm_num [candidate]

theorem witness_gram : witness * witness.transpose =
    !![7,7,7,1; 7,7,7,1; 7,7,7,1; 1,1,1,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.transpose_apply, witness, Fin.sum_univ_succ]

theorem candidate_gram : candidate * candidate.transpose =
    !![6,6,5,5; 6,6,5,5; 5,5,5,5; 5,5,5,5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals norm_num [Matrix.transpose_apply, candidate]

theorem only_dimensions (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    (hsp : s ≤ 4) (htq : t ≤ 7) (hlo : 22 ≤ s*t)
    (hhi : s*t - 22 ≤ min s t) : s = 4 ∧ t = 6 := by
  have hs4 : s = 4 := by
    have : s * t ≤ s * 7 := Nat.mul_le_mul_left s htq
    omega
  subst s
  have h := Nat.min_le_left 4 t
  constructor
  · rfl
  · omega

noncomputable def x : ℝ := 11 + Real.sqrt 103
noncomputable def y : ℝ := 11 + Real.sqrt 101

theorem x_polynomial : x^2 - 22*x + 18 = 0 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 103 by norm_num)
  dsimp [x]
  nlinarith

theorem y_polynomial : y^2 - 22*y + 20 = 0 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 101 by norm_num)
  dsimp [y]
  nlinarith

theorem y_lt_x : y < x := by
  dsimp [x,y]
  have h : Real.sqrt (101:ℝ) < Real.sqrt 103 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem positive_x : 21 < x := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 103 by norm_num)
  have hp := Real.sqrt_nonneg (103:ℝ)
  dsimp [x]
  nlinarith

theorem positive_y : 21 < y := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 101 by norm_num)
  have hp := Real.sqrt_nonneg (101:ℝ)
  dsimp [y]
  nlinarith

theorem witness_gram_eigenvector :
    (witness * witness.transpose).mulVec ![x-1,x-1,x-1,3] =
      x • ![x-1,x-1,x-1,3] := by
  rw [witness_gram]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    nlinarith [x_polynomial]

theorem candidate_gram_eigenvector :
    (candidate * candidate.transpose).mulVec ![y-10,y-10,10,10] =
      y • ![y-10,y-10,10,10] := by
  rw [candidate_gram]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    nlinarith [y_polynomial]

#print axioms witness_edges
#print axioms witness_gram
#print axioms candidate_gram
#print axioms only_dimensions
#print axioms y_lt_x
#print axioms witness_gram_eigenvector
#print axioms candidate_gram_eigenvector
end RefinedSpectral

namespace RefinedSpectral
open Matrix

theorem eigenvalue_le_positive {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) (r : ℝ)
    (hAw : A.mulVec w = r • w)
    (v : n → ℝ) (hv : v ≠ 0) (z : ℝ) (hAv : A.mulVec v = z • v) : z ≤ r := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun j => |v j| / w j) ⟨k, Finset.mem_univ k⟩
  let C := |v i| / w i
  have hC : 0 < C := lt_of_lt_of_le (div_pos (abs_pos.mpr hk) (hw k))
    (hi k (Finset.mem_univ k))
  have hb : ∀ j, |v j| ≤ C * w j := fun j =>
    (div_le_iff₀ (hw j)).mp (hi j (Finset.mem_univ j))
  have he : C * w i = |v i| := div_mul_cancel₀ _ (ne_of_gt (hw i))
  have hvi : 0 < |v i| := by nlinarith [hw i]
  have h1 : |z| * |v i| ≤ ∑ j, A i j * |v j| := by
    have h := Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j => A i j * v j)
    have hz := congrFun hAv i
    change (∑ j, A i j * v j) = z * v i at hz
    rw [hz, abs_mul] at h
    simpa only [abs_mul, abs_of_nonneg (hA i _)] using h
  have h2 : (∑ j, A i j * |v j|) ≤ r * |v i| := by
    calc
      _ ≤ ∑ j, A i j * (C * w j) := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hb j) (hA i j)
      _ = C * (∑ j, A i j * w j) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ = C * (r * w i) := by rw [show (∑ j, A i j * w j) = r * w i from congrFun hAw i]
      _ = r * |v i| := by rw [← he]; ring
  have habs : |z| ≤ r := by nlinarith [h1.trans h2]
  exact (le_abs_self z).trans habs
end RefinedSpectral

namespace RefinedSpectral
open Matrix

def adjacency {p q : ℕ} (B : Matrix (Fin p) (Fin q) ℝ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
  Matrix.fromBlocks 0 B B.transpose 0

noncomputable def rho {p q : ℕ} (B : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  sSup {z | ∃ v : (Fin p ⊕ Fin q) → ℝ, v ≠ 0 ∧ (adjacency B).mulVec v = z • v}

theorem rho_of_positive {p q : ℕ} (B : Matrix (Fin p) (Fin q) ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (w : (Fin p ⊕ Fin q) → ℝ)
    (hw : ∀ i, 0 < w i) (hne : w ≠ 0) (r : ℝ)
    (he : (adjacency B).mulVec w = r • w) : rho B = r := by
  have hA : ∀ i j, 0 ≤ adjacency B i j := by
    intro i j
    cases i <;> cases j <;> simp [adjacency, Matrix.fromBlocks, hB]
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨w,hne,he⟩
  · rintro z ⟨v,hv,hAv⟩
    exact eigenvalue_le_positive (adjacency B) hA w hw r he v hv z hAv

-- A positive Gram eigenvector yields a positive adjacency eigenvector.
theorem block_eigenvector {p q : ℕ} (B : Matrix (Fin p) (Fin q) ℝ)
    (u : Fin p → ℝ) (r : ℝ) (hr : r ≠ 0)
    (he : (B * B.transpose).mulVec u = r^2 • u) :
    (adjacency B).mulVec (Sum.elim u (r⁻¹ • B.transpose.mulVec u)) =
      r • Sum.elim u (r⁻¹ • B.transpose.mulVec u) := by
  ext i
  cases i with
  | inl i =>
    simp only [adjacency, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add,
      Sum.elim_inl, Sum.elim_inr, Function.comp_def, Pi.smul_apply, smul_eq_mul]
    change (B.mulVec (r⁻¹ • B.transpose.mulVec u)) i = r * u i
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, he]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hr]
  | inr j =>
    simp [adjacency, Matrix.fromBlocks_mulVec, hr]
end RefinedSpectral

namespace RefinedSpectral
open Matrix

theorem rho_eq_sqrt_of_gram {p q : ℕ} (hp : 0 < p)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (u : Fin p → ℝ) (hu : ∀ i, 0 < u i)
    (hcol : ∀ j, 0 < B.transpose.mulVec u j)
    (z : ℝ) (hz : 0 < z) (he : (B * B.transpose).mulVec u = z • u) :
    rho B = Real.sqrt z := by
  let r := Real.sqrt z
  have hr : 0 < r := Real.sqrt_pos.mpr hz
  let w := Sum.elim u (r⁻¹ • B.transpose.mulVec u)
  have hw : ∀ i, 0 < w i := by
    intro i
    cases i with
    | inl i => exact hu i
    | inr j => exact mul_pos (inv_pos.mpr hr) (hcol j)
  apply rho_of_positive B hB w hw
  · intro h
    have hi := hw (Sum.inl ⟨0,hp⟩)
    rw [h] at hi
    exact (lt_irrefl 0) hi
  · exact block_eigenvector B u r (ne_of_gt hr) (by
      simpa only [r, Real.sq_sqrt hz.le] using he)

theorem witness_rho : rho witness = Real.sqrt x := by
  apply rho_eq_sqrt_of_gram (by decide) witness
    (fun i j => by simp only [witness]; split <;> norm_num)
    ![x-1,x-1,x-1,3]
  · intro i; fin_cases i <;> simp <;> linarith [positive_x]
  · intro j; fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, witness] <;>
      linarith [positive_x]
  · linarith [positive_x]
  · exact witness_gram_eigenvector

theorem candidate_rho : rho candidate = Real.sqrt y := by
  apply rho_eq_sqrt_of_gram (by decide) candidate
    (fun i j => by simp only [candidate]; split <;> norm_num)
    ![y-10,y-10,10,10]
  · intro i; fin_cases i <;> simp <;> linarith [positive_y]
  · intro j; fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, candidate] <;>
      linarith [positive_y]
  · linarith [positive_y]
  · exact candidate_gram_eigenvector

noncomputable def refined (s t e : ℕ) : Matrix (Fin s) (Fin t) ℝ :=
  fun i j => if s ≤ t then
    (if i.val < s - (s*t-e) ∨ j.val < t-1 then 1 else 0)
  else (if i.val < s-1 ∨ j.val < t - (s*t-e) then 1 else 0)

theorem refined_4_6 : refined 4 6 22 = candidate := by
  ext i j
  rfl

def Conjecture : Prop := ∀ (p q e : ℕ) (B : Matrix (Fin p) (Fin q) ℝ),
  (∀ i j, B i j = 0 ∨ B i j = 1) →
  (∑ i, ∑ j, B i j) = (e:ℝ) → 1 < e → e < p*q →
  ∃ s t : ℕ, 0 < s ∧ 0 < t ∧ s ≤ p ∧ t ≤ q ∧
    e ≤ s*t ∧ s*t-e ≤ min s t ∧ rho B ≤ rho (refined s t e)

theorem counterexample : ¬ Conjecture := by
  intro h
  obtain ⟨s,t,hs,ht,hsp,htq,hlo,hhi,hr⟩ := h 4 7 22 witness
    (fun i j => by simp only [witness]; split <;> simp)
    witness_edges (by decide) (by decide)
  obtain ⟨rfl,rfl⟩ := only_dimensions s t hs ht hsp htq hlo hhi
  rw [refined_4_6, witness_rho, candidate_rho] at hr
  have hy : 0 ≤ y := by linarith [positive_y]
  have hlt := Real.sqrt_lt_sqrt hy y_lt_x
  exact (not_le_of_gt hlt) hr

#print axioms eigenvalue_le_positive
#print axioms block_eigenvector
#print axioms rho_eq_sqrt_of_gram
#print axioms witness_rho
#print axioms candidate_rho
#print axioms counterexample
end RefinedSpectral

#check RefinedSpectral.counterexample
#print RefinedSpectral.Conjecture
