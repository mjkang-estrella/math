import BunDomPayoff
namespace BunDom
open Classical Bun Finset
noncomputable local instance (j : Nat) : DecidableEq (Fin (j+1)) := Classical.decEq _
theorem sum_by_state_int {ι : Type} [Fintype ι] (F : ι → State) (S : Finset State)
    (hS : ∀ i, F i ∈ S) (H : State → Int) :
    (∑ i, H (F i)) = ∑ s ∈ S, (Fintype.card {i // F i = s} : Int) * H s := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun i (_ : i ∈ (univ : Finset ι)) => hS i) (fun i => H (F i))]
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.card_subtype]
  calc
    _ = ∑ _i ∈ univ.filter (fun i => F i = s), H s := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(mem_filter.mp hi).2]
    _ = _ := by simp [mul_comm]
theorem step_mem_indicator (m : Nat) (R S : Finset Nat) (hmR : m ∉ R) (hmS : m ∉ S)
    (x y z l : Bool) : m ∈ sval l (stepU m R S x y z) ↔
      (if l then (ind x y z).2 else (ind x y z).1) = true := by
  cases x <;> cases y <;> cases z <;> cases l <;> simp [sval, stepU, ind, hmR, hmS]
attribute [local irreducible] Bun.stf BunDom.stateCount
theorem event_count {n u j : Nat} (hn : j+1 < n) (hu : u ≤ j) (l : Bool) :
    Fintype.card {w : Asg n (j+1) // j+1 ∈ sval l (stf n u (j+1) w)} =
      ∑ p : Asg n j, Fintype.card {f : Fresh j //
        (if l then (freshInd j (fun i : Fin (j+1) => i.1 ∈ (stf n u j p).1)
          (fun i : Fin (j+1) => i.1 ∈ (stf n u j p).2) f).2
        else (freshInd j (fun i : Fin (j+1) => i.1 ∈ (stf n u j p).1)
          (fun i : Fin (j+1) => i.1 ∈ (stf n u j p).2) f).1) = true} := by
  rw [transport_dec hn]
  apply Finset.sum_congr rfl
  intro p _
  have hmR : j+1 ∉ (stf n u j p).1 := by intro h; have := stf_upper_support n u j (j+1) p false h; omega
  have hmS : j+1 ∉ (stf n u j p).2 := by intro h; have := stf_upper_support n u j (j+1) p true h; omega
  rw [Fintype.card_subtype, card_filter]
  apply Finset.sum_congr rfl
  intro f _
  rw [stf_join hn hu, hor_join_hit hn, hor_join_hit hn]
  simp only [step_mem_indicator (j+1) _ _ hmR hmS, freshInd]
  split_ifs <;> rfl
set_option maxHeartbeats 1600000 in
theorem endpoint_step {n u j : Nat} (hn : j+1 < n) (hu : u ≤ j) :
    Fintype.card {w : Asg n (j+1) // j+1 ∈ sval true (stf n u (j+1) w)} ≤
    Fintype.card {w : Asg n (j+1) // j+1 ∈ sval false (stf n u (j+1) w)} := by
  have hpay := payoff_nonneg (box n) (box_closed n)
    (fun s => (stateCount n u j s.1 s.2 : Int)) (payoff j)
    (fun s hs hlt => by exact_mod_cast dominance n u j hu (by omega) s hs hlt)
    (payoff_flip j) (payoff_pos j)
  have hg := sum_by_state_int
    (fun p : Asg n j => ((stf n u j p).1.card,(stf n u j p).2.card))
    (box n) (sizes_mem_box n u j (by omega)) (payoff j)
  change (∑ p : Asg n j, payoff j ((stf n u j p).1.card,(stf n u j p).2.card)) =
    ∑ s ∈ box n, (stateCount n u j s.1 s.2 : Int) * payoff j s at hg
  rw [← hg] at hpay
  rw [event_count hn hu true, event_count hn hu false]
  apply Int.ofNat_le.mp
  rw [Nat.cast_sum, Nat.cast_sum]
  apply sub_nonneg.mp
  rw [← Finset.sum_sub_distrib]
  convert hpay using 1
  congr 1
  funext p
  have hr : ∀ i ∈ (stf n u j p).1, i ≤ j := fun i hi => stf_upper_support n u j i p false hi
  have hs : ∀ i ∈ (stf n u j p).2, i ≤ j := fun i hi => stf_upper_support n u j i p true hi
  simpa only [ite_true, Bool.false_eq_true, ite_false] using rows_payoff j _ _ hr hs
end BunDom
namespace Bun
 theorem state_endpoint : ∀ (n u j : Nat), u ≤ j → j < n →
    Fintype.card {w : Bun.Asg n j // j ∈ Bun.sval true (Bun.stf n u j w)} ≤
    Fintype.card {w : Bun.Asg n j // j ∈ Bun.sval false (Bun.stf n u j w)} := by
  intro n u j hu hj
  by_cases he : j = u
  · subst j; exact BunDom.source_inequality n u
  · cases j with
    | zero => omega
    | succ j => exact BunDom.endpoint_step hj (by omega)
end Bun
