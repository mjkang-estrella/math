import GraphClosure4_000
import GraphClosure3_000
namespace Nut8
theorem catalogue_closed_4 (a : ℕ) (ha : a ∈ GraphClosure3_000.targets) :
    ∃ cs, extensionClosed 4 a GraphClosure4_000.targets cs = true := by
  simp only [GraphClosure3_000.targets, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨GraphClosure4_000.certificates0, GraphClosure4_000.closed0⟩
  · exact ⟨GraphClosure4_000.certificates1, GraphClosure4_000.closed1⟩
  · exact ⟨GraphClosure4_000.certificates2, GraphClosure4_000.closed2⟩
  · exact ⟨GraphClosure4_000.certificates3, GraphClosure4_000.closed3⟩
  · exact ⟨GraphClosure4_000.certificates4, GraphClosure4_000.closed4⟩
  · exact ⟨GraphClosure4_000.certificates5, GraphClosure4_000.closed5⟩
end Nut8
