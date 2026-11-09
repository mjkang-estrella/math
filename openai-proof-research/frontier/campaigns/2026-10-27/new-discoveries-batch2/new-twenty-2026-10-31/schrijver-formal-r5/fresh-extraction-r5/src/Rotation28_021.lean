import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_021_checked : rotationChunkCheck 672 32 #[14,9,9,9,25,27,16,16,16,2,25,27,18,18,18,25,27,20,20,20,27,22,22,27,24,24,26,11,11,11,11,11] #[151,195,203,210,201,126,66,144,210,265,202,127,58,136,202,203,128,49,127,193,129,39,117,130,28,106,16,8,20,31,41,50] = true := by decide
end Schrijver
