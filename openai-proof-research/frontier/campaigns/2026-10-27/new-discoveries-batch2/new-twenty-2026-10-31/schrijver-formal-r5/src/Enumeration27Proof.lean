import PathCoverage
import BridgeTransport
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem enumeration27_comparison : endMasks 27 12 = vertexMasks27.toList := by decide +kernel

theorem enumeration27_proved : Enumeration27 := by
  intro m
  constructor
  · intro h
    exact referenceMasks_complete.mpr (List.all_eq_true.mp vertexMasks27_valid m h)
  · intro h
    rw [← enumeration27_comparison]
    exact validMask_end_cover (by decide) (referenceMasks_complete.mp h)
end Schrijver
