import GraphClosure3_000
import GraphClosure2_000
namespace Nut8
theorem catalogue_closed_3 (a : ℕ) (ha : a ∈ GraphClosure2_000.targets) :
    ∃ cs, extensionClosed 3 a GraphClosure3_000.targets cs = true := by
  simp only [GraphClosure2_000.targets, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact ⟨GraphClosure3_000.certificates0, GraphClosure3_000.closed0⟩
  · exact ⟨GraphClosure3_000.certificates1, GraphClosure3_000.closed1⟩
end Nut8
