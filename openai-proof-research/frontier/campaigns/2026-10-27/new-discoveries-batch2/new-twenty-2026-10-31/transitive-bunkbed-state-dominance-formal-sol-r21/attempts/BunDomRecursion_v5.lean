import BunDomFiber
import BunNewIndicators
import BunHorWitness
import Mathlib.Algebra.BigOperators.Finprod
namespace BunDom
open Bun Classical Finset

theorem res_join {n j : Nat} (hn : j+1 < n) (p : Asg n j) (f : Fresh j) :
    res n j (join (p,f)) = p := congrArg Prod.fst (split_join hn (p,f))

theorem hor_join {n j : Nat} (hn : j+1 < n) (p : Asg n j) (f : Fresh j)
    (R : Finset Nat) (l : Bool) :
    hor hn R l (join (p,f)) = true ↔
      ∃ i : Fin (j+1), i.1 ∈ R ∧ f.1 i l = true := by
  rw [hor_iff]
  constructor
  · rintro ⟨k,hk,hR,hw⟩
    refine ⟨⟨k,hk⟩,hR,?_⟩
    simpa [join, fresH, tmax, htok] using hw
  · rintro ⟨i,hR,hw⟩
    refine ⟨i.1,i.2,hR,?_⟩
    simpa [join, fresH, tmax, htok] using hw

theorem stf_join {n u j : Nat} (hn : j+1 < n) (hu : u ≤ j)
    (p : Asg n j) (f : Fresh j) :
    stf n u (j+1) (join (p,f)) =
      stepU (j+1) (stf n u j p).1 (stf n u j p).2
        (hor hn (stf n u j p).1 false (join (p,f)))
        (hor hn (stf n u j p).2 true (join (p,f))) f.2 := by
  have hlt : ¬ j+1 < u := by omega
  have heq : ¬ j+1 = u := by omega
  simp only [stf, dite_eq_right hlt, dite_eq_right heq, dite_eq_left hn]
  rw [res_join hn]
  congr 1
  simp [join, fresV, tmax]

noncomputable def stateCount (n u j a b : Nat) : Nat :=
  Fintype.card {w : Asg n j // ((stf n u j w).1.card, (stf n u j w).2.card) = (a,b)}


theorem count_transport {n j : Nat} (hn : j+1 < n) (P : Asg n (j+1) → Prop) :
    Fintype.card {w // P w} =
      ∑ p : Asg n j, ∑ f : Fresh j, if P (join (p,f)) then 1 else 0 := by
  rw [Fintype.card_subtype, Finset.card_filter]
  rw [Fintype.sum_equiv (assignmentEquiv hn)
    (fun w => if P w then 1 else 0)
    (fun q => if P (join q) then 1 else 0)
    (fun w => by change (if P w then 1 else 0) = if P (join (split hn w)) then 1 else 0; rw [join_split hn])]
  exact Fintype.sum_prod_type _

attribute [local irreducible] Bun.stf BunDom.join

theorem count_recursion_full {n u j a b : Nat} (hn : j+1 < n) :
    stateCount n u (j+1) a b =
      ∑ p : Asg n j, ∑ f : Fresh j,
        if ((stf n u (j+1) (join (p,f))).1.card,
            (stf n u (j+1) (join (p,f))).2.card) = (a,b) then 1 else 0 :=
by
  unfold stateCount
  exact count_transport hn (fun w => ((stf n u (j+1) w).1.card,
    (stf n u (j+1) w).2.card) = (a,b))
end BunDom
