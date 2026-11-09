import GraphClosure6_000
import GraphClosure6_001
import GraphClosure6_002
import GraphClosure6_003
import GraphClosure5_000
namespace Nut8
theorem catalogue_closed_6 (a : ℕ) (ha : a ∈ GraphClosure5_000.targets) :
    ∃ cs, extensionClosed 6 a GraphClosure6_000.targets cs = true := by
  simp only [GraphClosure5_000.targets, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨GraphClosure6_000.certificates0, GraphClosure6_000.closed0⟩
  · exact ⟨GraphClosure6_000.certificates1, GraphClosure6_000.closed1⟩
  · exact ⟨GraphClosure6_000.certificates2, GraphClosure6_000.closed2⟩
  · exact ⟨GraphClosure6_000.certificates3, GraphClosure6_000.closed3⟩
  · exact ⟨GraphClosure6_000.certificates4, GraphClosure6_000.closed4⟩
  · exact ⟨GraphClosure6_000.certificates5, GraphClosure6_000.closed5⟩
  · exact ⟨GraphClosure6_000.certificates6, GraphClosure6_000.closed6⟩
  · exact ⟨GraphClosure6_000.certificates7, GraphClosure6_000.closed7⟩
  · exact ⟨GraphClosure6_001.certificates8, GraphClosure6_001.closed8⟩
  · exact ⟨GraphClosure6_001.certificates9, GraphClosure6_001.closed9⟩
  · exact ⟨GraphClosure6_001.certificates10, GraphClosure6_001.closed10⟩
  · exact ⟨GraphClosure6_001.certificates11, GraphClosure6_001.closed11⟩
  · exact ⟨GraphClosure6_001.certificates12, GraphClosure6_001.closed12⟩
  · exact ⟨GraphClosure6_001.certificates13, GraphClosure6_001.closed13⟩
  · exact ⟨GraphClosure6_001.certificates14, GraphClosure6_001.closed14⟩
  · exact ⟨GraphClosure6_001.certificates15, GraphClosure6_001.closed15⟩
  · exact ⟨GraphClosure6_002.certificates16, GraphClosure6_002.closed16⟩
  · exact ⟨GraphClosure6_002.certificates17, GraphClosure6_002.closed17⟩
  · exact ⟨GraphClosure6_002.certificates18, GraphClosure6_002.closed18⟩
  · exact ⟨GraphClosure6_002.certificates19, GraphClosure6_002.closed19⟩
  · exact ⟨GraphClosure6_002.certificates20, GraphClosure6_002.closed20⟩
  · exact ⟨GraphClosure6_002.certificates21, GraphClosure6_002.closed21⟩
  · exact ⟨GraphClosure6_002.certificates22, GraphClosure6_002.closed22⟩
  · exact ⟨GraphClosure6_002.certificates23, GraphClosure6_002.closed23⟩
  · exact ⟨GraphClosure6_003.certificates24, GraphClosure6_003.closed24⟩
  · exact ⟨GraphClosure6_003.certificates25, GraphClosure6_003.closed25⟩
  · exact ⟨GraphClosure6_003.certificates26, GraphClosure6_003.closed26⟩
  · exact ⟨GraphClosure6_003.certificates27, GraphClosure6_003.closed27⟩
  · exact ⟨GraphClosure6_003.certificates28, GraphClosure6_003.closed28⟩
end Nut8
