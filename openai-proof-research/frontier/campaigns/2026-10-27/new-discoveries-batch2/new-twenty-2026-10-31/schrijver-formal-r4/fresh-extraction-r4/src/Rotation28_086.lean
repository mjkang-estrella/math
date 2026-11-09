import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_086_checked : rotationChunkCheck 2752 32 #[7,7,7,7,17,7,7,7,7,19,7,7,7,21,7,7,23,23,25,12,12,12,12,12,12,12,15,12,12,12,12,12] #[116,117,118,119,77,125,126,127,128,71,134,135,136,64,142,143,56,134,47,10,22,33,43,52,60,67,83,111,121,130,138,145] = true := by decide
end Schrijver
