import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_077_checked : rotationChunkCheck 2464 32 #[20,25,22,22,25,24,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5] #[105,33,3,15,34,2,0,1,2,3,4,5,6,7,8,9,13,14,15,16,17,18,19,20,21,25,26,27,28,29,30,31] = true := by decide
end Schrijver
