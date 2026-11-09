import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_031_checked : rotationChunkCheck 992 32 #[11,14,11,11,11,11,11,11,16,16,11,11,11,27,18,18,18,4,27,20,20,20,27,22,22,22,24,24,26,13,13,13] #[72,79,110,120,129,137,144,150,73,151,195,203,210,201,66,144,210,265,202,58,136,202,203,49,127,193,39,117,28,8,20,31] = true := by decide
end Schrijver
