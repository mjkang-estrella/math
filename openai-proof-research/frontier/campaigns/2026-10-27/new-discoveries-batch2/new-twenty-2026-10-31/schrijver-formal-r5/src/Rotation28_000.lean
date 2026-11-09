import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_000_checked : rotationChunkCheck 0 32 #[0,0,0,0,0,0,0,0,0,0,0,0,27,0,0,0,0,0,0,0,0,0,0,0,27,0,0,0,0,0,0,0] #[0,1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,17,18,19,20,21,22,23,1,25,26,27,28,29,30,31] = true := by decide
end Schrijver
