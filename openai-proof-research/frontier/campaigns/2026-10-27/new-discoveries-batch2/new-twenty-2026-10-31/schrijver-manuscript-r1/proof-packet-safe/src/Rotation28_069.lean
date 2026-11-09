import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_069_checked : rotationChunkCheck 2208 32 #[3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] #[28,29,30,31,32,33,36,37,38,39,40,41,42,43,46,47,48,49,50,51,52,55,56,57,58,59,60,63,64,65,66,67] = true := by decide
end Schrijver
