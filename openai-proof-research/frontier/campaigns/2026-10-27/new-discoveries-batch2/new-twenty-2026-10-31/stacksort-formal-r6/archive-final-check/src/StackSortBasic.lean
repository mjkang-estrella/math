import Mathlib.Data.List.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Topology BigOperators
noncomputable section
namespace StackSort

/-- Structural fuel makes the literal max-split map kernel executable. -/
def sortFuel (fuel : ℕ) (w : List ℕ) : List ℕ :=
  Nat.rec (fun _ => []) (fun _ rec w => match w with
    | [] => []
    | _ :: _ =>
      let m := w.foldr max 0
      rec (w.takeWhile (· != m)) ++ rec ((w.dropWhile (· != m)).drop 1) ++ [m]) fuel w

@[simp] theorem sortFuel_zero (w : List ℕ) : sortFuel 0 w = [] := rfl
@[simp] theorem sortFuel_succ_nil (k : ℕ) : sortFuel (k+1) [] = [] := rfl
 theorem sortFuel_succ_cons (k x : ℕ) (xs : List ℕ) :
    sortFuel (k+1) (x :: xs) =
      sortFuel k ((x :: xs).takeWhile (· != (x :: xs).foldr max 0)) ++
      sortFuel k (((x :: xs).dropWhile (· != (x :: xs).foldr max 0)).drop 1) ++
      [(x :: xs).foldr max 0] := rfl

def s (w : List ℕ) : List ℕ := sortFuel w.length w

/-- The literal finite domain consists of one-line words of [0,n). -/
def words (n : ℕ) : Finset (List ℕ) := (List.range n).permutations'.toFinset

def P (n : ℕ) : ℕ :=
  ((words n ×ˢ words n).filter (fun p => s p.1 = s p.2)).card

noncomputable def deg (n : ℕ) : ℝ := (P n : ℝ) / (n.factorial : ℝ)

def fibre (n : ℕ) (y : List ℕ) : Finset (List ℕ) :=
  (words n).filter (fun w => s w = y)

def maxFib (n : ℕ) : ℕ := (words n).sup (fun w => (fibre n (s w)).card)

noncomputable def roots (n : ℕ) : ℝ := deg n ^ (1 / (n : ℝ))
noncomputable def maxRoots (n : ℕ) : ℝ := (maxFib n : ℝ) ^ (1 / (n : ℝ))
def Conj : Prop := ∃ L : ℝ, Tendsto roots atTop (𝓝 L) ∧ L ∈ Set.Ioo 1.68 1.73
def ConjMax : Prop := ∃ L : ℝ, Tendsto maxRoots atTop (𝓝 L) ∧ L ∈ Set.Ioo 1.68 1.73

theorem mem_words {n : ℕ} {w : List ℕ} : w ∈ words n ↔ w.Perm (List.range n) := by
  simp [words, List.mem_permutations']

theorem P_eq_sum (n : ℕ) : P n = ∑ w ∈ words n, (fibre n (s w)).card := by
  simp only [P, fibre, Finset.card_filter, Finset.sum_product]
  exact Finset.sum_comm

theorem deg_eq_average (n : ℕ) :
    deg n = (∑ w ∈ words n, ((fibre n (s w)).card : ℝ)) / (n.factorial : ℝ) := by
  simp [deg, P_eq_sum]

theorem P_pos (n : ℕ) : 0 < P n := by
  apply Finset.card_pos.mpr
  exact ⟨(List.range n, List.range n), by simp [words]⟩

theorem deg_nonneg (n : ℕ) : 0 ≤ deg n := by
  unfold deg
  positivity

example : s [4,1,6,3,5,2] = [1,4,3,2,5,6] := by decide
theorem words_card (n : ℕ) : (words n).card = n.factorial := by
  rw [words, List.toFinset_card_of_nodup
    ((List.permutations_perm_permutations' _).nodup_iff.mp
      (List.nodup_permutations _ (List.nodup_range)))]
  rw [← (List.permutations_perm_permutations' (List.range n)).length_eq, List.length_permutations, List.length_range]

 theorem P_zero : P 0 = 1 := by decide
 theorem P_one : P 1 = 1 := by decide
 theorem P_two : P 2 = 4 := by decide
 theorem P_three : P 3 = 26 := by decide
end StackSort
