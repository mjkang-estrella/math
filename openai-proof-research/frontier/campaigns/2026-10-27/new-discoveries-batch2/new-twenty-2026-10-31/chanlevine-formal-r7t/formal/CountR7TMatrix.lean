import CountR7TStates
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace ChanLevine.Round7T
open Round3
variable {R S : Type*} [CommRing R] [Fintype S] [DecidableEq S]

def pathWeight (A : ℕ → Matrix S S R) (r : ℕ) (i j : S) (q : Fin r → S) : R :=
  ∏ k : Fin (r+1), A k.val (Fin.cons (α := fun _ => S) i q k) (Fin.snoc (α := fun _ => S) q j k)

theorem pathWeight_snoc (A : ℕ → Matrix S S R) (r : ℕ) (i j x : S)
    (q : Fin r → S) :
    pathWeight A (r+1) i j (Fin.snoc (α := fun _ => S) q x) =
      pathWeight A r i x q * A (r+1) x j := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro k _
    apply congrArg₂ (A k.val)
    · exact Fin.cases (by simp) (fun t => by simp) k
    · simp
  · simp

theorem product_entry_paths (A : ℕ → Matrix S S R) (r : ℕ) (i j : S) :
    orderedProduct A (r+1) i j = ∑ q : Fin r → S, pathWeight A r i j q := by
  induction r generalizing i j with
  | zero =>
    simp only [orderedProduct, pathWeight, Fin.prod_univ_succ, Finset.univ_eq_empty, Finset.prod_empty, mul_one, Fin.cons_zero]
    simp [Fin.snoc]
  | succ r ih =>
    rw [orderedProduct_succ, Matrix.mul_apply]
    simp_rw [ih, Finset.sum_mul]
    have he := (Fin.snocEquiv (fun _ : Fin (r+1) => S)).sum_comp
      (fun q => pathWeight A (r+1) i j q)
    rw [← he, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro q _
    exact (pathWeight_snoc A r i j x q).symm

def finCycleWeight (A : ℕ → Matrix S S R) (r : ℕ) (w : Fin (r+1) → S) : R :=
  ∏ k : Fin (r+1), A k.val (w k)
    (Fin.snoc (α := fun _ => S) (Fin.tail w) (w 0) k)

theorem trace_cycle_words (A : ℕ → Matrix S S R) (r : ℕ) :
    (orderedProduct A (r+1)).trace =
      ∑ w : Fin (r+1) → S, finCycleWeight A r w := by
  unfold Matrix.trace
  simp_rw [Matrix.diag_apply, product_entry_paths]
  have he := (Fin.consEquiv (fun _ : Fin (r+1) => S)).sum_comp
    (fun w => finCycleWeight A r w)
  rw [← he, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro q _
  simp [finCycleWeight,pathWeight, Fin.consEquiv]
end ChanLevine.Round7T
