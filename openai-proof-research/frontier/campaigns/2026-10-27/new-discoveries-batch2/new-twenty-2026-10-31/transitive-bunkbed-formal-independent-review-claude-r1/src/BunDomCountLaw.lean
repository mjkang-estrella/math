import BunDomActualCounts
import BunDomAbstract
namespace BunDom
open Classical Bun Finset
noncomputable local instance (j : Nat) : DecidableEq (Fin (j+1)) := Classical.decEq _
def rowSize (j a : Nat) (x : Bool) : Nat :=
  if x then 2^(j+1) - 2^(j+1-a) else 2^(j+1-a)
def nextSize (s : State) (d : Bool × Bool) : State :=
  (s.1 + d.1.toNat, s.2 + d.2.toNat)
noncomputable def kernel (j : Nat) (s q : State) : Nat :=
  ∑ x : Bool, ∑ y : Bool, ∑ z : Bool,
    rowSize j s.1 x * rowSize j s.2 y * (if nextSize s (ind x y z) = q then 1 else 0)
theorem stepU_sizes (m : Nat) (R S : Finset Nat) (hmR : m ∉ R) (hmS : m ∉ S)
    (x y z : Bool) :
    ((stepU m R S x y z).1.card, (stepU m R S x y z).2.card) =
      nextSize (R.card,S.card) (ind x y z) := by
  cases x <;> cases y <;> cases z <;> simp [stepU, ind, nextSize, hmR, hmS]
theorem fresh_state_count (j : Nat) (R S : Finset Nat)
    (hR : ∀ i ∈ R, i ≤ j) (hS : ∀ i ∈ S, i ≤ j) (q : State) :
    (∑ f : Fresh j, if
      ((stepU (j+1) R S (hit (fun i : Fin (j+1) => i.1 ∈ R) (fun i => f.1 i false))
      (hit (fun i : Fin (j+1) => i.1 ∈ S) (fun i => f.1 i true)) f.2).1.card,
      (stepU (j+1) R S (hit (fun i : Fin (j+1) => i.1 ∈ R) (fun i => f.1 i false))
      (hit (fun i : Fin (j+1) => i.1 ∈ S) (fun i => f.1 i true)) f.2).2.card) = q then 1 else 0) =
      kernel j (R.card,S.card) q := by
  have hmR : j+1 ∉ R := by intro h; have := hR _ h; omega
  have hmS : j+1 ∉ S := by intro h; have := hS _ h; omega
  simp_rw [stepU_sizes (j+1) R S hmR hmS]
  rw [rows_sum j (fun i : Fin (j+1) => i.1 ∈ R) (fun i : Fin (j+1) => i.1 ∈ S)
    (fun x y z => if nextSize (R.card,S.card) (ind x y z) = q then 1 else 0)]
  simp only [rowCount_set j R hR, rowCount_set j S hS, kernel, rowSize]
theorem transport_dec {n j : Nat} (hn : j+1 < n) (P : Asg n (j+1) → Prop) [DecidablePred P] :
    Fintype.card {w // P w} = ∑ p : Asg n j, ∑ f : Fresh j, if P (join (p,f)) then 1 else 0 := by
  rw [Fintype.card_subtype, Finset.card_filter]
  rw [Fintype.sum_equiv (assignmentEquiv hn)
    (fun w => if P w then 1 else 0)
    (fun q => if P (join q) then 1 else 0)
    (fun w => by change (if P w then 1 else 0) = if P (join (split hn w)) then 1 else 0; rw [join_split hn])]
  exact Fintype.sum_prod_type _
attribute [local irreducible] Bun.stf
set_option maxHeartbeats 800000 in
theorem count_law_uncompressed {n u j : Nat} (hn : j+1 < n) (hu : u ≤ j) (q : State) :
    stateCount n u (j+1) q.1 q.2 =
      ∑ p : Asg n j, kernel j ((stf n u j p).1.card, (stf n u j p).2.card) q := by
  unfold stateCount
  rw [transport_dec hn]
  apply Finset.sum_congr rfl
  intro p _
  have hr : ∀ i ∈ (stf n u j p).1, i ≤ j := fun i hi => stf_upper_support n u j i p false hi
  have hs : ∀ i ∈ (stf n u j p).2, i ≤ j := fun i hi => stf_upper_support n u j i p true hi
  rw [← fresh_state_count j _ _ hr hs]
  apply Finset.sum_congr rfl
  intro f _
  rw [stf_join hn hu, hor_join_hit hn, hor_join_hit hn]
end BunDom
