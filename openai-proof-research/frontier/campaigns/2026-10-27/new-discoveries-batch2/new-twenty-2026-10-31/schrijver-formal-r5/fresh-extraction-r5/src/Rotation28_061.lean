import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_061_checked : rotationChunkCheck 1952 32 #[1,26,19,19,1,26,21,21,26,23,23,25,6,6,6,6,6,6,6,6,6,6,9,6,6,6,6,6,6,6,26,11] #[151,109,47,125,156,110,37,115,111,26,104,14,10,22,33,43,52,60,67,73,78,82,83,111,121,130,138,145,151,156,115,78] = true := by decide
end Schrijver
