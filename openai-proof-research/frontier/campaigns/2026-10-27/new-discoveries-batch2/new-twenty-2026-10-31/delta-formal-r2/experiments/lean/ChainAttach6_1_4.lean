import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem attach6_1_4 : ∀ d : V, Fits (first 6 1 8 4 3 ++ dbl 1 d) → d = 8 := by decide +kernel
end ChainPrefix
