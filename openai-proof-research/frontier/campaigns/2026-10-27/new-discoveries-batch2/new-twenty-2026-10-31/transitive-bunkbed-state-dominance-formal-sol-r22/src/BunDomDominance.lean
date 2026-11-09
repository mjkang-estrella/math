import BunDomCompressed
import BunDomEndpoint
namespace BunDom
open Classical Bun Finset
theorem kernel_flip (j : Nat) (s q : State) : kernel j (flip s) (flip q) = kernel j s q := by
  rcases q with ⟨a,b⟩
  have hi (x y z : Bool) : ind y x z = ((ind x y z).2,(ind x y z).1) := by
    cases x <;> cases y <;> cases z <;> rfl
  unfold kernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  rw [hi]
  have he : nextSize (flip s) ((ind x y z).2,(ind x y z).1) = flip (a,b) ↔ nextSize s (ind x y z) = (a,b) := by
    simp only [nextSize, flip, Prod.mk.injEq]
    exact and_comm
  simp only [he]
  simp only [flip, Nat.mul_comm]
theorem kernel_cross (j : Nat) (s q : State) (hs : s.2 < s.1) (hq : q.1 < q.2) :
    kernel j s q = 0 := by
  unfold kernel
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  apply Finset.sum_eq_zero
  intro z _
  have he : nextSize s (ind x y z) ≠ q := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    cases x <;> cases y <;> cases z <;> simp [nextSize, ind] at h1 h2 <;> omega
  simp [he]
attribute [local irreducible] Bun.stf BunDom.stateCount
theorem source_below (n u a b : Nat) (hab : a < b) : stateCount n u u a b = 0 := by
  rw [stateCount, Fintype.card_eq_zero_iff]
  refine ⟨fun w => ?_⟩
  have h := w.2
  rw [stf_at_source] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [startST] at h1 h2
  split_ifs at h2 <;> simp_all <;> omega
theorem dominance (n u j : Nat) (hu : u ≤ j) (hjn : j < n) :
    ∀ s ∈ box n, s.2 < s.1 → stateCount n u j s.2 s.1 ≤ stateCount n u j s.1 s.2 := by
  induction j, hu using Nat.le_induction with
  | base =>
    intro s _ hs
    rw [source_below n u s.2 s.1 hs]
    exact Nat.zero_le _
  | succ j hu ih =>
    intro s _ hs
    have hd := ih (by omega)
    have hr (q : State) : (stateCount n u (j+1) q.1 q.2 : Int) =
        advance (box n) (fun s => (stateCount n u j s.1 s.2 : Int))
          (fun s q => (kernel j s q : Int)) q := by
      rw [count_law hjn hu]
      simp [advance]
    have h := reflection_step (box n) (box_closed n)
      (fun s => (stateCount n u j s.1 s.2 : Int)) (fun s q => (kernel j s q : Int))
      (fun _ _ => Int.natCast_nonneg _) (fun s q => by rw [kernel_flip])
      (fun s q hs hq => by rw [kernel_cross j s q hs hq]; rfl)
      (fun s hm hs => by exact_mod_cast hd s hm hs) s hs
    rw [← hr, ← hr] at h
    exact_mod_cast h
end BunDom
