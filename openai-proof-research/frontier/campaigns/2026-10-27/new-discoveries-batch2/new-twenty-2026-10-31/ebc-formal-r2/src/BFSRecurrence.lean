import BFSGeneral
namespace EBC337062
open SimpleGraph Finset
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
set_option backward.isDefEq.respectTransparency.types false

theorem sigma_comm (a b : V) : sigma G a b = sigma G b a := by
  classical
  rw [sigma_eq_walk_count, sigma_eq_walk_count]
  apply Finset.card_bij (fun w _ => w.reverse)
  · intro w hw
    apply G.mem_finsetWalkLength_iff.mpr
    simpa [G.dist_comm] using G.mem_finsetWalkLength_iff.mp hw
  · intro w _ p _ h
    exact Walk.reverse_injective h
  · intro w hw
    refine ⟨w.reverse, ?_, Walk.reverse_reverse w⟩
    apply G.mem_finsetWalkLength_iff.mpr
    simpa [G.dist_comm] using G.mem_finsetWalkLength_iff.mp hw

/-- General BFS recursion by removing the first edge. -/
theorem sigma_first_edge (conn : G.Connected) (a t : V) (hat : a ≠ t) :
    sigma G a t = ∑ b : G.neighborSet a,
      if G.dist b t + 1 = G.dist a t then sigma G b t else 0 := by
  classical
  have step : ∀ a b, G.Adj a b → G.dist a t ≤ G.dist b t + 1 := by
    intro a b hab
    have h := conn.dist_triangle (u := a) (v := b) (w := t)
    rw [G.dist_eq_one_iff_adj.mpr hab] at h
    omega
  have hn := conn.pos_dist_of_ne hat
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [sigma_eq_walk_count, hk, walk_count_succ]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : G.dist b t + 1 = k.succ
  · rw [ite_eq_left hb, sigma_eq_walk_count]
    have : G.dist b t = k := by omega
    rw [this]
  · rw [ite_eq_right hb]
    apply walk_count_zero_of_lt G t (fun b => G.dist b t) (G.dist_self (v := t)) step
    have := step a b b.property
    omega

/-- General BFS recursion by removing the last edge. -/
theorem sigma_last_edge (conn : G.Connected) (x y : V) (hxy : x ≠ y) :
    sigma G x y = ∑ z : G.neighborSet y,
      if G.dist x z + 1 = G.dist x y then sigma G x z else 0 := by
  rw [sigma_comm G x y, sigma_first_edge G conn y x hxy.symm]
  simp_rw [G.dist_comm (v := x), sigma_comm G _ x]
end EBC337062
