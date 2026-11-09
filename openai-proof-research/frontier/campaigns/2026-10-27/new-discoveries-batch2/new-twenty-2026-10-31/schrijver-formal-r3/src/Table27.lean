import Link27_000
import Link27_001
import Link27_002
import Link27_003
import Link27_004
import Link27_005
import Link27_006
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Schrijver
theorem table27_size : vertexMasks27.size = 819 := by decide
theorem table27_links (i : Fin 819) : maskAt27 i.val = vertexMasks27[i.val]! ∧ (i.val+1 < vertexMasks27.size → maskAt27 i.val < maskAt27 (i.val+1)) := by
  by_cases h0 : i.val < 128
  · exact tableLinkCheck_sound Link27_000_checked (by omega)
  by_cases h1 : i.val < 256
  · exact tableLinkCheck_sound Link27_001_checked (by omega)
  by_cases h2 : i.val < 384
  · exact tableLinkCheck_sound Link27_002_checked (by omega)
  by_cases h3 : i.val < 512
  · exact tableLinkCheck_sound Link27_003_checked (by omega)
  by_cases h4 : i.val < 640
  · exact tableLinkCheck_sound Link27_004_checked (by omega)
  by_cases h5 : i.val < 768
  · exact tableLinkCheck_sound Link27_005_checked (by omega)
  exact tableLinkCheck_sound Link27_006_checked (by have := i.isLt; omega)
theorem maskAt27_lookup (i : Fin 819) : maskAt27 i.val = vertexMasks27[i.val]! := (table27_links i).1

theorem maskAt27_injective : Function.Injective (fun i : Fin 819 => maskAt27 i.val) := by
  apply (bounded_strictMono maskAt27 ?_).injective
  intro i hi
  exact (table27_links ⟨i, by omega⟩).2 (by rw [table27_size]; exact hi)
end Schrijver
