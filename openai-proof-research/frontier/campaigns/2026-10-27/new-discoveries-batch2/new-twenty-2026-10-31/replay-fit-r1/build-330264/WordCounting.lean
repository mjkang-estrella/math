import AutomatonSemantics
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RACGNormal330264.Machine
open RACGSemantics330264
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {S : Type*} (M : Machine G S) [Fintype V]

/-- These are individual alphabet words, not equivalence classes or group elements. -/
abbrev Words (k : ℕ) (s : S) := {w : Fin k → V // M.Accept s (List.ofFn w)}
noncomputable instance wordsFintype (k : ℕ) (s : S) : Fintype (M.Words k s) := by
  classical
  exact inferInstanceAs (Fintype {w : Fin k → V // M.Accept s (List.ofFn w)})

noncomputable def wordCount (k : ℕ) (s : S) := Fintype.card (M.Words k s)

noncomputable def splitWords (k : ℕ) (s : S) : M.Words (k + 1) s ≃
    Σ a : V, {w : Fin k → V // M.Accept s (a :: List.ofFn w)} where
  toFun w := ⟨w.val 0, ⟨Fin.tail w.val, by simpa only [List.ofFn_succ, Fin.tail_def] using w.property⟩⟩
  invFun w := ⟨Fin.cons w.1 w.2.val, by simpa only [List.ofFn_cons] using w.2.property⟩
  left_inv w := by apply Subtype.ext; funext i; exact Fin.cases rfl (fun j => rfl) i
  right_inv w := by cases w; rfl

 theorem wordCount_zero (s : S) : M.wordCount 0 s = 1 := by
  classical
  let e : M.Words 0 s ≃ (Fin 0 → V) := {
    toFun := Subtype.val
    invFun := fun w => ⟨w, by simp [Accept]⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  unfold wordCount
  rw [Fintype.card_congr e]
  simp

 theorem wordCount_succ (k : ℕ) (s : S) : M.wordCount (k + 1) s =
    ∑ a : V, (M.next s a).elim 0 (fun t => M.wordCount k t) := by
  classical
  unfold wordCount
  rw [Fintype.card_congr (M.splitWords k s), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro a _
  cases hn : M.next s a with
  | none => simp [Accept, hn]
  | some t =>
    simp only [Option.elim_some]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun w => by simp [Accept, hn])

 theorem geodesicGrowth_eq (k : ℕ) : geodesicGrowth G k = M.wordCount k M.initial := by
  classical
  let _ : Fintype (GeodesicWords G k) := inferInstanceAs (Fintype {w : Fin k → V // (system G).IsReduced (List.ofFn w)})
  unfold geodesicGrowth wordCount
  rw [Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun w => (M.accepts_iff_reduced (List.ofFn w)).symm)

#print axioms wordCount_succ
#print axioms geodesicGrowth_eq
end RACGNormal330264.Machine
