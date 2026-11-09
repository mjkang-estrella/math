import BunDomPins
import BunDomRecursion
namespace BunDom
open Bun Classical

noncomputable def entry (j : Nat) (R : Finset Nat) (l : Bool) (f : Fresh j) : Bool :=
  decide (∃ i : Fin (j+1), i.1 ∈ R ∧ f.1 i l = true)

theorem count_increment_zero {n j : Nat} (hn : j+1 < n) (p : Asg n j)
    (R S : Finset Nat) (hR : ∀ i ∈ R, i ≤ j) (hS : ∀ i ∈ S, i ≤ j) :
    Fintype.card {w : Asg n (j+1) // res n j w = p ∧
      ind (hor hn R false w) (hor hn S true w) (w (fresV hn)) = (false,false)} =
      2^(2*j+2-R.card-S.card) * 2 := by
  simp only [Fintype.card_subtype, Finset.card_filter]
  rw [Fintype.sum_equiv (assignmentEquiv hn)
    (fun w => if res n j w = p ∧ ind (hor hn R false w) (hor hn S true w)
      (w (fresV hn)) = (false,false) then 1 else 0)
    (fun q => if q.1 = p ∧ ind (entry j R false q.2) (entry j S true q.2)
      q.2.2 = (false,false) then 1 else 0)]
end BunDom
