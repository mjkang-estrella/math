import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_052_checked : rotationChunkCheck 1664 32 #[20,17,17,17,22,22,12,24,24,26,19,19,19,19,22,19,19,24,24,26,21,21,21,24,21,26,23,23,26,25,14,14] #[83,111,121,130,78,156,192,72,150,65,9,21,32,42,79,110,120,73,151,66,8,20,31,74,109,67,7,19,68,6,0,1] = true := by decide
end Schrijver
