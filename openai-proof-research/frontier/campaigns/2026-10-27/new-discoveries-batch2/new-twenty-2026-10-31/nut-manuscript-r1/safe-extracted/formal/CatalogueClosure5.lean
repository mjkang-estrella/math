import GraphClosure5_000
import GraphClosure5_001
import GraphClosure4_000
namespace Nut8
theorem catalogue_closed_5 (a : ℕ) (ha : a ∈ GraphClosure4_000.targets) :
    ∃ cs, extensionClosed 5 a GraphClosure5_000.targets cs = true := by
  simp only [GraphClosure4_000.targets, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨GraphClosure5_000.certificates0, GraphClosure5_000.closed0⟩
  · exact ⟨GraphClosure5_000.certificates1, GraphClosure5_000.closed1⟩
  · exact ⟨GraphClosure5_000.certificates2, GraphClosure5_000.closed2⟩
  · exact ⟨GraphClosure5_000.certificates3, GraphClosure5_000.closed3⟩
  · exact ⟨GraphClosure5_000.certificates4, GraphClosure5_000.closed4⟩
  · exact ⟨GraphClosure5_000.certificates5, GraphClosure5_000.closed5⟩
  · exact ⟨GraphClosure5_000.certificates6, GraphClosure5_000.closed6⟩
  · exact ⟨GraphClosure5_000.certificates7, GraphClosure5_000.closed7⟩
  · exact ⟨GraphClosure5_001.certificates8, GraphClosure5_001.closed8⟩
  · exact ⟨GraphClosure5_001.certificates9, GraphClosure5_001.closed9⟩
end Nut8
