import Base
namespace Smyth1512
theorem rearr_perm {m : ℕ} (f : Fin m → ℕ) : (rearr f).Perm (List.ofFn f) :=
  List.perm_insertionSort _ _
theorem rearr_sorted {m : ℕ} (f : Fin m → ℕ) :
    (rearr f).Pairwise (fun x y => y ≤ x) := List.pairwise_insertionSort _ _
-- A nonempty instance, with a = b = 1, uses the identity injection.
theorem nonvacuity :
    ∃ γ : (U 1 1 × U 1 1) → (U 1 1 × U 1 1), Function.Injective γ ∧
      ∀ x, Dom (concat x.1.1 x.2.1) (concat (γ x).1.1 (γ x).2.1) := by
  exact ⟨id, Function.injective_id, fun _ => ⟨rfl, fun _ => le_rfl⟩⟩
theorem nonempty_control : Nonempty (U 1 1 × U 1 1) := by
  exact ⟨(⟨fun _ => 1, by simp [U]⟩, ⟨fun _ => 1, by simp [U]⟩)⟩
end Smyth1512
namespace Smyth1512
theorem generators_are_partitions :
    ∀ g ∈ gens, g.length = 5 ∧ g.sum = 39 ∧ g.Pairwise (fun x y => y ≤ x) := by decide
end Smyth1512
