import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem attach3_8_6 : ∀ d : V, Fits (first 3 8 1 6 2 ++ dbl 8 d) → d = 1 := by decide +kernel
end ChainPrefix
