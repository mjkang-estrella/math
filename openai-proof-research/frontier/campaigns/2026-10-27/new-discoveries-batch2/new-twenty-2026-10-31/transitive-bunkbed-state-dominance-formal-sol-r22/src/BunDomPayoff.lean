import BunDomDominance
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
namespace BunDom
open Classical Bun Finset
noncomputable local instance (j : Nat) : DecidableEq (Fin (j+1)) := Classical.decEq _
def payoff (j : Nat) (s : State) : Int :=
  (rowSize j s.1 true : Int) * rowSize j s.2 false -
  (rowSize j s.1 false : Int) * rowSize j s.2 true
theorem payoff_flip (j : Nat) (s : State) : payoff j (flip s) = -payoff j s := by
  simp only [payoff, flip]
  ring
theorem payoff_formula (j : Nat) (s : State) :
    payoff j s = (2^(j+1) : Int) * ((2^(j+1-s.2) : Int) - 2^(j+1-s.1)) := by
  have ha : (2 : Nat)^(j+1-s.1) ≤ 2^(j+1) := by gcongr; omega
  have hb : (2 : Nat)^(j+1-s.2) ≤ 2^(j+1) := by gcongr; omega
  simp only [payoff, rowSize, Bool.false_eq_true, ite_false, ite_true]
  rw [Nat.cast_sub ha, Nat.cast_sub hb]
  push_cast
  ring
theorem payoff_pos (j : Nat) (s : State) (hs : s.2 < s.1) : 0 ≤ payoff j s := by
  rw [payoff_formula]
  apply mul_nonneg (by positivity)
  apply sub_nonneg.mpr
  gcongr
  omega
theorem rows_payoff (j : Nat) (R S : Finset Nat)
    (hR : ∀ i ∈ R, i ≤ j) (hS : ∀ i ∈ S, i ≤ j) :
    (Fintype.card {f : Fresh j // (freshInd j (fun i : Fin (j+1) => i.1 ∈ R)
      (fun i : Fin (j+1) => i.1 ∈ S) f).1 = true} : Int) -
    (Fintype.card {f : Fresh j // (freshInd j (fun i : Fin (j+1) => i.1 ∈ R)
      (fun i : Fin (j+1) => i.1 ∈ S) f).2 = true} : Int) = payoff j (R.card,S.card) := by
  have hc (l : Bool) : Fintype.card {f : Fresh j //
      (if l then (freshInd j (fun i : Fin (j+1) => i.1 ∈ R) (fun i : Fin (j+1) => i.1 ∈ S) f).2
      else (freshInd j (fun i : Fin (j+1) => i.1 ∈ R) (fun i : Fin (j+1) => i.1 ∈ S) f).1) = true} =
      ∑ x : Bool, ∑ y : Bool, ∑ z : Bool, rowSize j R.card x * rowSize j S.card y *
      (if (if l then (ind x y z).2 else (ind x y z).1) = true then 1 else 0) := by
    rw [Fintype.card_subtype, Finset.card_filter]
    unfold freshInd
    rw [rows_sum j (fun i : Fin (j+1) => i.1 ∈ R) (fun i : Fin (j+1) => i.1 ∈ S) (fun x y z => if (if l then (ind x y z).2 else (ind x y z).1) = true then 1 else 0)]
    simp only [rowCount_set j R hR, rowCount_set j S hS, rowSize]
  have h0 := hc false
  have h1 := hc true
  simp only [Bool.false_eq_true, ite_false, ite_true] at h0 h1
  rw [h0,h1]
  simp [ind, payoff]
  ring
end BunDom
