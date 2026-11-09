import Character
namespace Nut8
open Matrix

/-- In a three-term zero sum of nonzero values, two terms cannot cancel. -/
theorem three_sum_no_cancel {V : Type} [DecidableEq V] (S : Finset V)
    (hS : S.card = 3) (u : V → ℝ) (hu : ∑ z ∈ S, u z = 0)
    (hf : ∀ z ∈ S, u z ≠ 0) (x y : V) (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    u x + u y ≠ 0 := by
  have hy' : y ∈ S.erase x := Finset.mem_erase.mpr ⟨hxy.symm,hy⟩
  have hc : ((S.erase x).erase y).card = 1 := by
    rw [Finset.card_erase_of_mem hy', Finset.card_erase_of_mem hx, hS]
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp hc
  have hzS : z ∈ S := by
    have : z ∈ (S.erase x).erase y := by rw [hz]; simp
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase this)
  have hsx := Finset.sum_erase_add S u hx
  have hsy := Finset.sum_erase_add (S.erase x) u hy'
  rw [hz, Finset.sum_singleton] at hsy
  intro hcancel
  have : u z = 0 := by linarith
  exact hf z hzS this

/-- Cubicity and fullness exclude cancellation at any two distinct neighbors. -/
theorem cubic_kernel_no_cancel {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : Cubic G)
    (u : V → ℝ) (hu : adjacency G u = 0) (hf : ∀ v, u v ≠ 0)
    (v x y : V) (hx : G.Adj v x) (hy : G.Adj v y) (hxy : x ≠ y) :
    u x + u y ≠ 0 := by
  apply three_sum_no_cancel (G.neighborFinset v) (hc v) u
  · have h := congrFun hu v
    change (G.adjMatrix ℝ *ᵥ u) v = 0 at h
    simpa only [SimpleGraph.adjMatrix_mulVec_apply] using h
  · exact fun z _ => hf z
  · exact (G.mem_neighborFinset v x).mpr hx
  · exact (G.mem_neighborFinset v y).mpr hy
  · exact hxy
/-- Contributions to a fixed quotient entry have a common character sign. -/
theorem neighbor_character_coherent {m : ℕ} [NeZero m]
    (G : SimpleGraph (Fin 8 × ZMod m)) [DecidableRel G.Adj] (hc : Cubic G)
    (ε : ℤ) (he : ε = 1 ∨ ε = -1) (u : (Fin 8 × ZMod m) → ℝ)
    (hu : adjacency G u = 0) (hf : ∀ v, u v ≠ 0)
    (hchar : ∀ i b, u (i,b) = (character m ε b : ℝ) * u (i,0))
    (i j : Fin 8) (b c : ZMod m)
    (hb : G.Adj (i,0) (j,b)) (hc' : G.Adj (i,0) (j,c)) :
    character m ε b = character m ε c := by
  by_cases hbc : b = c
  · rw [hbc]
  have hne : (j,b) ≠ (j,c) := fun h => hbc (congrArg Prod.snd h)
  have hn := cubic_kernel_no_cancel G hc u hu hf (i,0) (j,b) (j,c) hb hc' hne
  rw [hchar j b, hchar j c] at hn
  rcases character_sign m ε he b with hb' | hb' <;>
    rcases character_sign m ε he c with hc'' | hc''
  · exact hb'.trans hc''.symm
  · exfalso; apply hn; simp [hb', hc'']
  · exfalso; apply hn; simp [hb', hc'']
  · exact hb'.trans hc''.symm
end Nut8

