import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_005_checked : rotationChunkCheck 160 32 #[20,25,27,22,22,27,24,27,26,5,5,5,5,5,5,5,5,5,5,27,8,5,5,5,5,5,5,5,25,27,10,10] #[115,111,21,26,104,22,14,23,1,10,22,33,43,52,60,67,73,78,82,25,83,111,121,130,138,145,151,156,115,26,78,156] = true := by decide
end Schrijver
