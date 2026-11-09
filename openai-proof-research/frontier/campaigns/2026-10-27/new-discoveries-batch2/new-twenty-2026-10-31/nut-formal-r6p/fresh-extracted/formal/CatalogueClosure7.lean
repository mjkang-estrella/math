import GraphClosure7_000
import GraphClosure7_001
import GraphClosure7_002
import GraphClosure7_003
import GraphClosure7_004
import GraphClosure7_005
import GraphClosure7_006
import GraphClosure7_007
import GraphClosure6_000
namespace Nut8
theorem catalogue_closed_7 (a : ℕ) (ha : a ∈ GraphClosure6_000.targets) :
    ∃ cs, extensionClosed 7 a GraphClosure7_000.targets cs = true := by
  simp only [GraphClosure6_000.targets, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨GraphClosure7_000.certificates0, GraphClosure7_000.closed0⟩
  · exact ⟨GraphClosure7_000.certificates1, GraphClosure7_000.closed1⟩
  · exact ⟨GraphClosure7_000.certificates2, GraphClosure7_000.closed2⟩
  · exact ⟨GraphClosure7_000.certificates3, GraphClosure7_000.closed3⟩
  · exact ⟨GraphClosure7_000.certificates4, GraphClosure7_000.closed4⟩
  · exact ⟨GraphClosure7_000.certificates5, GraphClosure7_000.closed5⟩
  · exact ⟨GraphClosure7_000.certificates6, GraphClosure7_000.closed6⟩
  · exact ⟨GraphClosure7_000.certificates7, GraphClosure7_000.closed7⟩
  · exact ⟨GraphClosure7_001.certificates8, GraphClosure7_001.closed8⟩
  · exact ⟨GraphClosure7_001.certificates9, GraphClosure7_001.closed9⟩
  · exact ⟨GraphClosure7_001.certificates10, GraphClosure7_001.closed10⟩
  · exact ⟨GraphClosure7_001.certificates11, GraphClosure7_001.closed11⟩
  · exact ⟨GraphClosure7_001.certificates12, GraphClosure7_001.closed12⟩
  · exact ⟨GraphClosure7_001.certificates13, GraphClosure7_001.closed13⟩
  · exact ⟨GraphClosure7_001.certificates14, GraphClosure7_001.closed14⟩
  · exact ⟨GraphClosure7_001.certificates15, GraphClosure7_001.closed15⟩
  · exact ⟨GraphClosure7_002.certificates16, GraphClosure7_002.closed16⟩
  · exact ⟨GraphClosure7_002.certificates17, GraphClosure7_002.closed17⟩
  · exact ⟨GraphClosure7_002.certificates18, GraphClosure7_002.closed18⟩
  · exact ⟨GraphClosure7_002.certificates19, GraphClosure7_002.closed19⟩
  · exact ⟨GraphClosure7_002.certificates20, GraphClosure7_002.closed20⟩
  · exact ⟨GraphClosure7_002.certificates21, GraphClosure7_002.closed21⟩
  · exact ⟨GraphClosure7_002.certificates22, GraphClosure7_002.closed22⟩
  · exact ⟨GraphClosure7_002.certificates23, GraphClosure7_002.closed23⟩
  · exact ⟨GraphClosure7_003.certificates24, GraphClosure7_003.closed24⟩
  · exact ⟨GraphClosure7_003.certificates25, GraphClosure7_003.closed25⟩
  · exact ⟨GraphClosure7_003.certificates26, GraphClosure7_003.closed26⟩
  · exact ⟨GraphClosure7_003.certificates27, GraphClosure7_003.closed27⟩
  · exact ⟨GraphClosure7_003.certificates28, GraphClosure7_003.closed28⟩
  · exact ⟨GraphClosure7_003.certificates29, GraphClosure7_003.closed29⟩
  · exact ⟨GraphClosure7_003.certificates30, GraphClosure7_003.closed30⟩
  · exact ⟨GraphClosure7_003.certificates31, GraphClosure7_003.closed31⟩
  · exact ⟨GraphClosure7_004.certificates32, GraphClosure7_004.closed32⟩
  · exact ⟨GraphClosure7_004.certificates33, GraphClosure7_004.closed33⟩
  · exact ⟨GraphClosure7_004.certificates34, GraphClosure7_004.closed34⟩
  · exact ⟨GraphClosure7_004.certificates35, GraphClosure7_004.closed35⟩
  · exact ⟨GraphClosure7_004.certificates36, GraphClosure7_004.closed36⟩
  · exact ⟨GraphClosure7_004.certificates37, GraphClosure7_004.closed37⟩
  · exact ⟨GraphClosure7_004.certificates38, GraphClosure7_004.closed38⟩
  · exact ⟨GraphClosure7_004.certificates39, GraphClosure7_004.closed39⟩
  · exact ⟨GraphClosure7_005.certificates40, GraphClosure7_005.closed40⟩
  · exact ⟨GraphClosure7_005.certificates41, GraphClosure7_005.closed41⟩
  · exact ⟨GraphClosure7_005.certificates42, GraphClosure7_005.closed42⟩
  · exact ⟨GraphClosure7_005.certificates43, GraphClosure7_005.closed43⟩
  · exact ⟨GraphClosure7_005.certificates44, GraphClosure7_005.closed44⟩
  · exact ⟨GraphClosure7_005.certificates45, GraphClosure7_005.closed45⟩
  · exact ⟨GraphClosure7_005.certificates46, GraphClosure7_005.closed46⟩
  · exact ⟨GraphClosure7_005.certificates47, GraphClosure7_005.closed47⟩
  · exact ⟨GraphClosure7_006.certificates48, GraphClosure7_006.closed48⟩
  · exact ⟨GraphClosure7_006.certificates49, GraphClosure7_006.closed49⟩
  · exact ⟨GraphClosure7_006.certificates50, GraphClosure7_006.closed50⟩
  · exact ⟨GraphClosure7_006.certificates51, GraphClosure7_006.closed51⟩
  · exact ⟨GraphClosure7_006.certificates52, GraphClosure7_006.closed52⟩
  · exact ⟨GraphClosure7_006.certificates53, GraphClosure7_006.closed53⟩
  · exact ⟨GraphClosure7_006.certificates54, GraphClosure7_006.closed54⟩
  · exact ⟨GraphClosure7_006.certificates55, GraphClosure7_006.closed55⟩
  · exact ⟨GraphClosure7_007.certificates56, GraphClosure7_007.closed56⟩
  · exact ⟨GraphClosure7_007.certificates57, GraphClosure7_007.closed57⟩
  · exact ⟨GraphClosure7_007.certificates58, GraphClosure7_007.closed58⟩
  · exact ⟨GraphClosure7_007.certificates59, GraphClosure7_007.closed59⟩
  · exact ⟨GraphClosure7_007.certificates60, GraphClosure7_007.closed60⟩
  · exact ⟨GraphClosure7_007.certificates61, GraphClosure7_007.closed61⟩
  · exact ⟨GraphClosure7_007.certificates62, GraphClosure7_007.closed62⟩
  · exact ⟨GraphClosure7_007.certificates63, GraphClosure7_007.closed63⟩
end Nut8
