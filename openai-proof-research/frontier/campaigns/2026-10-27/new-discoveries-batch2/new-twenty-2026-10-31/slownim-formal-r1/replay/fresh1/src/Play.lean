import Basic
namespace SlowNim360653
-- Recursor form avoids compiler-generated recursive helpers.
def run {n l} (hl : 2 ≤ l) (s : Profile n l) (fuel : ℕ) : Pos n → ℕ → ℕ :=
  Nat.rec (fun _ _ => 0) (fun _ prev x t =>
    if Terminal x then 0 else 1 + prev (move x ((s ⟨t % l, Nat.mod_lt _ (by omega)⟩).choose x)) (t+1)) fuel
lemma run_zero {n l} (hl : 2 ≤ l) (s : Profile n l) (x : Pos n) (t) : run hl s 0 x t = 0 := rfl
lemma run_succ {n l} (hl : 2 ≤ l) (s : Profile n l) (k) (x : Pos n) (t) :
    run hl s (k+1) x t = if Terminal x then 0 else
      1 + run hl s k (move x ((s ⟨t % l, Nat.mod_lt _ (by omega)⟩).choose x)) (t+1) := rfl
lemma run_terminal {n l} (hl : 2 ≤ l) (s : Profile n l) (k) (x : Pos n) (t)
    (h : Terminal x) : run hl s k x t = 0 := by
  cases k <;> simp [run_zero, run_succ, h]
theorem run_bound {n l} (_hn : 2 ≤ n) (hl : 2 ≤ l) (s : Profile n l)
    (k) (x : Pos n) (t) : run hl s k x t * (n-1) ≤ mass x := by
  induction k generalizing x t with
  | zero => simp [run_zero]
  | succ k ih =>
    rw [run_succ]
    split
    · simp
    · rename_i h
      have hm := mass_move x ((s ⟨t % l, Nat.mod_lt _ (by omega)⟩).choose x)
        ((s _).valid x h)
      have hb := ih (move x ((s ⟨t % l, Nat.mod_lt _ (by omega)⟩).choose x)) (t+1)
      rw [Nat.add_mul]; omega
-- Once fuel exceeds the mass, its precise value does not affect the result.
theorem run_independent {n l} (_hn : 2 ≤ n) (hl : 2 ≤ l) (s : Profile n l)
    (a b) (x : Pos n) (t) (ha : mass x < a) (hb : mass x < b) :
    run hl s a x t = run hl s b x t := by
  induction a generalizing b x t with
  | zero => omega
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      rw [run_succ, run_succ]
      split
      · rfl
      · rename_i h
        have hm := mass_move x ((s ⟨t % l, Nat.mod_lt _ (by omega)⟩).choose x)
          ((s _).valid x h)
        have hdrop : mass (move x ((s ⟨t % l, Nat.mod_lt _ (by omega)⟩).choose x)) < mass x := by omega
        rw [ih b _ (t+1) (by omega) (by omega)]
def length {n l} (hl : 2 ≤ l) (s : Profile n l) (x : Pos n) : ℕ := run hl s (mass x + 1) x 0
theorem length_bound {n l} (hn : 2 ≤ n) (hl : 2 ≤ l) (s : Profile n l) (x : Pos n) :
    length hl s x ≤ mass x / (n-1) := by
  apply (Nat.le_div_iff_mul_le (by omega)).2
  exact run_bound hn hl s _ x 0
def loser {n l} (hl : 2 ≤ l) (s : Profile n l) (x : Pos n) := length hl s x % l
def payoff {n l} (hl : 2 ≤ l) (s : Profile n l) (x : Pos n) (C : ℚ) (p : Fin l) : ℚ :=
  if loser hl s x = p.val then -(C - length hl s x) else (C - length hl s x) / (l-1 : ℕ)
def Admissible {n l} (hl : 2 ≤ l) (x : Pos n) (C : ℚ) : Prop :=
  ∀ s : Profile n l, (length hl s x : ℚ) < C
def replace {n l} (s : Profile n l) (p : Fin l) (d : Strategy n) : Profile n l :=
  fun q => if q = p then d else s q
def IsNash {n l} (hl : 2 ≤ l) (x : Pos n) (C : ℚ) (s : Profile n l) : Prop :=
  ∀ p d, payoff hl (replace s p d) x C p ≤ payoff hl s x C p
def Conjecture : Prop := ∀ n (hn : 2 ≤ n) l (hl : 2 ≤ l) (x : Pos n) (C : ℚ),
  Admissible hl x C → IsNash hl x C (GMProfile hn l)
end SlowNim360653
