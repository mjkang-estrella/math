import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.Combinatorics.SimpleGraph.Basic
import Lean.Elab.Tactic.Omega

/- Actual presented groups and one direction of the normal-form bridge.
   This file does not claim the converse or a complete MathDB endpoint. -/
namespace RACGSemantics330264
variable {V : Type*} [DecidableEq V]

def matrix (G : SimpleGraph V) [DecidableRel G.Adj] : CoxeterMatrix V where
  M u v := if u = v then 1 else if G.Adj u v then 2 else 0
  isSymm := by
    change (fun u v => if v = u then 1 else if G.Adj v u then 2 else 0) = _
    funext u v
    by_cases h : u = v
    · subst v; rfl
    · simp [h, Ne.symm h, G.adj_comm]
  diagonal := by simp
  off_diagonal := by intros; simp_all; split <;> decide

abbrev RACG (G : SimpleGraph V) [DecidableRel G.Adj] := (matrix G).Group
abbrev system (G : SimpleGraph V) [DecidableRel G.Adj] := (matrix G).toCoxeterSystem

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem generators_commute {a b : V} (hab : G.Adj a b) :
    (system G).simple a * (system G).simple b =
      (system G).simple b * (system G).simple a := by
  have h := (system G).simple_mul_simple_pow a b
  have hm : matrix G a b = 2 := by simp [matrix, hab, hab.ne]
  rw [hm, pow_two] at h
  have h' := congrArg (fun x => (system G).simple a * x * (system G).simple b) h
  simpa only [mul_assoc, CoxeterSystem.simple_mul_simple_cancel_left,
    CoxeterSystem.simple_mul_simple_self, mul_one, one_mul] using h'.symm

theorem commute_word (a : V) (m : List V) (h : ∀ b ∈ m, G.Adj a b) :
    (system G).simple a * (system G).wordProd m =
      (system G).wordProd m * (system G).simple a := by
  induction m with
  | nil => simp
  | cons b m ih =>
    have hb := generators_commute G (h b (by simp))
    have hm := ih (by intro c hc; exact h c (by simp [hc]))
    simp only [CoxeterSystem.wordProd_cons]
    calc
      _ = ((system G).simple a * (system G).simple b) * (system G).wordProd m := by simp [mul_assoc]
      _ = ((system G).simple b * (system G).simple a) * (system G).wordProd m := by rw [hb]
      _ = _ := by rw [mul_assoc, hm, ← mul_assoc]

theorem cancel_commuting_pair (p m q : List V) (a : V)
    (h : ∀ b ∈ m, G.Adj a b) :
    (system G).wordProd (p ++ a :: (m ++ a :: q)) =
      (system G).wordProd (p ++ m ++ q) := by
  simp only [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_cons]
  rw [← mul_assoc ((system G).simple a), commute_word G a m h]
  simp only [mul_assoc, CoxeterSystem.simple_mul_simple_cancel_left]

theorem forbidden_pair_not_shortest (p m q : List V) (a : V)
    (h : ∀ b ∈ m, G.Adj a b) :
    ¬ (system G).IsReduced (p ++ a :: (m ++ a :: q)) := by
  intro hr
  have hb := (system G).length_wordProd_le (p ++ m ++ q)
  have he := cancel_commuting_pair G p m q a h
  rw [CoxeterSystem.IsReduced, he] at hr
  simp only [List.length_append, List.length_cons] at hr hb
  omega

/-- Words (not group elements) of length k that are shortest in the actual presentation. -/
def GeodesicWords (k : ℕ) := {w : Fin k → V // (system G).IsReduced (List.ofFn w)}

noncomputable def geodesicGrowth (k : ℕ) : ℕ := Nat.card (GeodesicWords G k)

#print axioms forbidden_pair_not_shortest
end RACGSemantics330264
