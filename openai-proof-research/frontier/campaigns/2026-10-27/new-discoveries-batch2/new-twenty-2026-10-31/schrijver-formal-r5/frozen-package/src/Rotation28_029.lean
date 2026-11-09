import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_029_checked : rotationChunkCheck 928 32 #[4,4,20,20,4,4,22,22,4,24,24,26,9,9,9,9,9,9,9,9,9,12,9,9,9,9,9,9,9,14,14,4] #[144,145,56,134,150,151,47,125,156,37,115,26,10,22,33,43,52,60,67,73,78,83,111,121,130,138,145,151,156,78,156,192] = true := by decide
end Schrijver
