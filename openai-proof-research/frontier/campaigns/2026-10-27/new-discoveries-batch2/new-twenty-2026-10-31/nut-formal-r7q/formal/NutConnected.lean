import Nut
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
namespace Nut8
variable {V : Type} [Fintype V]

/-- A full one-dimensional adjacency kernel rules out every proper nonempty cut. -/
theorem nut_crossing (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Nut G)
    (S : Set V) (a b : V) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
  classical
  by_contra hcross
  have hc : ∀ x ∈ S, ∀ y ∉ S, ¬G.Adj x y := by simpa using hcross
  obtain ⟨_, hd, u, hu, hk, hf⟩ := hn
  let w : V → ℝ := fun x => if x ∈ S then u x else 0
  have hw : adjacency G w = 0 := by
    ext x
    have hx := congrFun hk x
    change (∑ y, G.adjMatrix ℝ x y * w y) = 0
    by_cases hxs : x ∈ S
    · calc
        _ = ∑ y, G.adjMatrix ℝ x y * u y := by
          apply Finset.sum_congr rfl
          intro y _
          by_cases hys : y ∈ S
          · simp [w, hys]
          · simp [w, hys, SimpleGraph.adjMatrix_apply, hc x hxs y hys]
        _ = 0 := hx
    · apply Finset.sum_eq_zero
      intro y _
      by_cases hys : y ∈ S
      · have hn : ¬G.Adj x y := fun h => hc y hys x hxs (G.adj_symm h)
        simp [w, hys, SimpleGraph.adjMatrix_apply, hn]
      · simp [w, hys]
  let uk : LinearMap.ker (adjacency G) := ⟨u,hk⟩
  let wk : LinearMap.ker (adjacency G) := ⟨w,hw⟩
  have huk : uk ≠ 0 := fun h => hu (congrArg Subtype.val h)
  obtain ⟨c, he⟩ := exists_smul_eq_of_finrank_eq_one hd huk wk
  have heq := congrArg Subtype.val he
  have heqb := congrFun heq b
  have hcz : c = 0 := by
    have : c * u b = 0 := by simpa [uk, wk, w, hb] using heqb
    exact (mul_eq_zero.mp this).resolve_right (hf b)
  have heqa := congrFun heq a
  exact hf a (by simpa [uk, wk, w, ha, hcz] using heqa.symm)

/-- Nut graphs are connected without any regularity or orbit assumptions. -/
theorem nut_connected (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Nut G) :
    G.Connected := by
  classical
  have hV : 0 < Fintype.card V := lt_of_lt_of_le (by decide : 0 < 2) hn.1
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, Fintype.card_pos_iff.mp hV⟩
  intro a b
  by_contra hab
  obtain ⟨x, hx, y, hy, hxy⟩ := nut_crossing G hn {x | G.Reachable a x}
    a b (SimpleGraph.Reachable.refl a) hab
  exact hy (hx.trans hxy.reachable)
end Nut8
