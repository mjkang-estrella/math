import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_018_checked : rotationChunkCheck 576 32 #[2,27,16,2,2,2,2,27,18,18,2,2,27,20,20,2,27,22,22,27,24,24,26,7,7,7,7,7,7,7,7,7] #[138,107,64,142,143,144,145,108,56,134,150,151,109,47,125,156,110,37,115,111,26,104,14,10,22,33,43,52,60,67,73,78] = true := by decide
end Schrijver
