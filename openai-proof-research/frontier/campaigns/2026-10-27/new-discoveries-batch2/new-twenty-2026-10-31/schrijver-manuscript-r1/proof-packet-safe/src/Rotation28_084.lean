import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_084_checked : rotationChunkCheck 2688 32 #[25,24,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7] #[44,3,0,1,2,3,4,5,6,7,8,13,14,15,16,17,18,19,20,25,26,27,28,29,30,31,36,37,38,39,40,41] = true := by decide
end Schrijver
