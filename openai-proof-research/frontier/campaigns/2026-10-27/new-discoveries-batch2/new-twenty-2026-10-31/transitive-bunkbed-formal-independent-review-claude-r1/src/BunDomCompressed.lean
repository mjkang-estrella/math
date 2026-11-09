import BunDomCountLaw
namespace BunDom
open Classical Finset Bun
def box (n : Nat) : Finset State := (range (n+1)) ×ˢ (range (n+1))
theorem box_closed (n : Nat) (s : State) (hs : s ∈ box n) : flip s ∈ box n := by
  simpa only [box, mem_product, flip, and_comm] using hs
theorem sum_by_state {ι : Type} [Fintype ι] (F : ι → State) (S : Finset State)
    (hS : ∀ i, F i ∈ S) (H : State → Nat) :
    (∑ i, H (F i)) = ∑ s ∈ S, Fintype.card {i // F i = s} * H s := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun i (_ : i ∈ (univ : Finset ι)) => hS i) (fun i => H (F i))]
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.card_subtype]
  calc
    _ = ∑ _i ∈ univ.filter (fun i => F i = s), H s := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(mem_filter.mp hi).2]
    _ = _ := by simp [Nat.mul_comm]
attribute [local irreducible] Bun.stf
theorem sizes_mem_box (n u j : Nat) (hj : j < n) (p : Asg n j) :
    ((stf n u j p).1.card, (stf n u j p).2.card) ∈ box n := by
  have hb (l : Bool) : (sval l (stf n u j p)).card ≤ j+1 := by
    have hsub : sval l (stf n u j p) ⊆ range (j+1) := by
      intro i hi; exact mem_range.mpr (by have := stf_upper_support n u j i p l hi; omega)
    simpa using card_le_card hsub
  have h0 := hb false
  have h1 := hb true
  change (stf n u j p).1.card ≤ j+1 at h0
  change (stf n u j p).2.card ≤ j+1 at h1
  simp only [box, mem_product, mem_range]
  omega
set_option maxHeartbeats 800000 in
theorem count_law {n u j : Nat} (hn : j+1 < n) (hu : u ≤ j) (q : State) :
    stateCount n u (j+1) q.1 q.2 =
      ∑ s ∈ box n, stateCount n u j s.1 s.2 * kernel j s q := by
  rw [count_law_uncompressed hn hu]
  exact sum_by_state (fun p : Asg n j => ((stf n u j p).1.card,(stf n u j p).2.card))
    (box n) (sizes_mem_box n u j (by omega)) (fun s => kernel j s q)
end BunDom
