import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_091_checked : rotationChunkCheck 2912 32 #[9,21,9,9,23,9,25,14,14,14,14,14,14,17,14,14,14,14,19,19,9,9,21,21,9,23,23,25,16,16,16,16] #[127,71,134,135,64,142,56,10,22,33,43,52,60,83,111,121,130,138,78,156,192,193,72,150,201,65,143,57,9,21,32,42] = true := by decide
end Schrijver
