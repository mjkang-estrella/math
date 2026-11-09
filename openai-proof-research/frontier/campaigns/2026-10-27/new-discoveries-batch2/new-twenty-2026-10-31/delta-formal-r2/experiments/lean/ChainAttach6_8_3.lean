import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem attach6_8_3 : ∀ d : V, Fits (first 6 8 1 3 4 ++ dbl 8 d) → d = 1 := by decide +kernel
end ChainPrefix
