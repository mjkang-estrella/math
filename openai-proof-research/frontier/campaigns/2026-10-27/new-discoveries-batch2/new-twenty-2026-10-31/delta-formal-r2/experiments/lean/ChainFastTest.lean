import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem test : all3 (fun b c m => !fastFits (first 3 b c 0 m)) = true := by decide +kernel
end ChainPrefix
