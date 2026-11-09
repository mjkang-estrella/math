module
public import URMatchingWalkPositions
@[expose] public section
namespace URMatching
open scoped Classical
/-- Extract the distinct X and Y lists from an actual left-started even cycle.
The tail-nodup hypothesis is exactly the field of Walk.IsCycle. -/
theorem closed_walk_labels {N k : ℕ} (σ : PermutationTuples N 100) (u : Fin N)
    (p : (permutationGraph σ).Walk (.inl u) (.inl u))
    (hlen : p.length = 2*(k+1)) (hn : p.support.tail.Nodup) :
    ∃ x y : Fin (k+1) ↪ Fin N,
      (∀ i, p.getVert (2*(k+1)-2*i.val) = .inl (x i)) ∧
      (∀ i, p.getVert (2*(k+1)-(2*i.val+1)) = .inr (y i)) := by
  have hx : ∀ i : Fin (k+1), ∃ a : Fin N,
      p.getVert (2*(k+1)-2*i.val) = .inl a := by
    intro i
    have hi := i.isLt
    have hh := walk_position_parity σ p (2*(k+1)-2*i.val) (by omega)
    have heven : (2*(k+1)-2*i.val)%2 = 0 := by omega
    have hh' := hh.mpr heven
    cases he : p.getVert (2*(k+1)-2*i.val) with
    | inl a => exact ⟨a,rfl⟩
    | inr b => simp [he] at hh'
  have hy : ∀ i : Fin (k+1), ∃ a : Fin N,
      p.getVert (2*(k+1)-(2*i.val+1)) = .inr a := by
    intro i
    have hi := i.isLt
    have hh := walk_position_parity σ p (2*(k+1)-(2*i.val+1)) (by omega)
    have hodd : (2*(k+1)-(2*i.val+1))%2 ≠ 0 := by omega
    cases he : p.getVert (2*(k+1)-(2*i.val+1)) with
    | inr a => exact ⟨a,rfl⟩
    | inl b => exact False.elim (hodd (hh.mp (by simp [he])))
  let x : Fin (k+1) ↪ Fin N := ⟨fun i => Classical.choose (hx i), by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have he : p.getVert (2*(k+1)-2*i.val) = p.getVert (2*(k+1)-2*j.val) := by
      rw [Classical.choose_spec (hx i), Classical.choose_spec (hx j)]
      exact congrArg Sum.inl hij
    have hh := walk_tail_positions_injective p hn (by omega) (by omega) he
    apply Fin.ext
    omega⟩
  let y : Fin (k+1) ↪ Fin N := ⟨fun i => Classical.choose (hy i), by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have he : p.getVert (2*(k+1)-(2*i.val+1)) = p.getVert (2*(k+1)-(2*j.val+1)) := by
      rw [Classical.choose_spec (hy i), Classical.choose_spec (hy j)]
      exact congrArg Sum.inr hij
    have hh := walk_tail_positions_injective p hn (by omega) (by omega) he
    apply Fin.ext
    omega⟩
  exact ⟨x,y,fun i => Classical.choose_spec (hx i),fun i => Classical.choose_spec (hy i)⟩
end URMatching
