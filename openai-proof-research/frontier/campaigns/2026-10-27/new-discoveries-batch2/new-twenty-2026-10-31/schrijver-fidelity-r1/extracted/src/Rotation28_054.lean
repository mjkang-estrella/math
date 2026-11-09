import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_054_checked : rotationChunkCheck 1728 32 #[14,26,19,19,19,19,22,19,19,24,24,26,21,21,21,24,21,26,23,23,26,25,16,16,16,16,16,16,16,16,16,16] #[125,71,10,22,33,43,83,111,121,78,156,72,9,21,32,79,110,73,8,20,74,7,0,1,2,3,4,13,14,15,16,25] = true := by decide
end Schrijver
