import GraphClosure2_000
import GraphClosure1_000
namespace Nut8
theorem catalogue_closed_2 (a : ℕ) (ha : a ∈ GraphClosure1_000.targets) :
    ∃ cs, extensionClosed 2 a GraphClosure2_000.targets cs = true := by
  simp only [GraphClosure1_000.targets, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl
  · exact ⟨GraphClosure2_000.certificates0, GraphClosure2_000.closed0⟩
end Nut8
