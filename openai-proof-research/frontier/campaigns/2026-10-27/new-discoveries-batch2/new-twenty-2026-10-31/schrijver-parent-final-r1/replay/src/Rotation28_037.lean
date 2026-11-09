import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_037_checked : rotationChunkCheck 1184 32 #[16,6,6,6,6,6,18,6,6,6,6,20,6,6,6,22,22,6,24,24,26,11,11,11,11,11,11,11,11,14,11,11] #[77,125,126,127,128,129,71,134,135,136,137,64,142,143,144,56,134,150,47,125,37,10,22,33,43,52,60,67,73,83,111,121] = true := by decide
end Schrijver
