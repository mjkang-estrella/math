import PathCoverage
import BridgeTransport
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem enumeration28_comparison : endMasks 28 12 = vertexMasks28 := by decide +kernel

theorem enumeration28_proved : Enumeration28 := by
  intro m
  constructor
  · intro h
    exact referenceMasks_complete.mpr (List.all_eq_true.mp vertexMasks28_valid m h)
  · intro h
    rw [← enumeration28_comparison]
    exact validMask_end_cover (by decide) (referenceMasks_complete.mp h)
end Schrijver
