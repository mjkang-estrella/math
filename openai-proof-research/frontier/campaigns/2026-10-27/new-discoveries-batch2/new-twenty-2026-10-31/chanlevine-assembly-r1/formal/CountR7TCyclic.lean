import CountR7TMatrix
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace ChanLevine.Round7T
open Round3
variable {R S : Type*} [CommRing R] [Fintype S] [DecidableEq S]

theorem cyclic_successor (r : ℕ) (q : ZMod (r+1) → S) (k : Fin (r+1)) :
    Fin.snoc (α := fun _ => S) (Fin.tail (fun j : Fin (r+1) => q (j.val : ZMod (r+1))))
      (q 0) k = q ((k.val : ZMod (r+1))+1) := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp only [Fin.snoc_last, Fin.val_last]
    congr 1
    have h : ((r : ℕ) : ZMod (r+1)) + 1 = 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using (ZMod.natCast_self (r+1))
    exact h.symm
  · simp only [Fin.snoc_castSucc, Fin.tail, Fin.val_succ, Fin.val_castSucc,
      Nat.cast_add, Nat.cast_one]

theorem trace_zmod_words (r : ℕ) (B : ZMod (r+1) → Matrix S S R) :
    (orderedProduct (fun k : ℕ => B (k : ZMod (r+1))) (r+1)).trace =
      ∑ q : ZMod (r+1) → S, ∏ k, B k (q k) (q (k+1)) := by
  rw [trace_cycle_words]
  let e : (ZMod (r+1) → S) ≃ (Fin (r+1) → S) :=
    Equiv.piCongrLeft (fun _ => S) (ZMod.finEquiv (r+1)).symm.toEquiv
  rw [← e.sum_comp (finCycleWeight (fun k : ℕ => B (k : ZMod (r+1))) r)]
  apply Finset.sum_congr rfl
  intro q _
  change finCycleWeight (fun k : ℕ => B (k : ZMod (r+1))) r q = _
  unfold finCycleWeight
  have hc (k : Fin (r+1)) : (k.val : ZMod (r+1)) = k :=
    ZMod.natCast_zmod_val (n := r+1) k
  have hn (k : Fin (r+1)) :
      Fin.snoc (α := fun _ => S) (Fin.tail q) (q 0) k = q ((show ZMod (r+1) from k)+1) := by
    simpa only [hc] using cyclic_successor r q k
  simp only [hc]
  apply Finset.prod_congr rfl
  intro k _
  exact congrArg (B k (q k)) (hn k)
end ChanLevine.Round7T
