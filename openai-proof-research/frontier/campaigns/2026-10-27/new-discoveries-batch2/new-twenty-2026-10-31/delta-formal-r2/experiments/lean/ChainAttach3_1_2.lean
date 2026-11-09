import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem attach3_1_2 : ∀ d : V, Fits (first 3 1 8 2 6 ++ dbl 1 d) → d = 8 := by decide +kernel
end ChainPrefix
