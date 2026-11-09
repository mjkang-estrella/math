import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_082_checked : rotationChunkCheck 2624 32 #[19,19,19,5,21,21,21,23,23,25,14,14,14,14,14,14,17,14,14,14,14,19,19,14,14,21,21,21,23,23,25,16] #[66,144,210,265,58,136,202,49,127,39,8,20,31,41,50,58,74,109,119,128,136,67,145,194,202,59,137,203,50,128,40,7] = true := by decide
end Schrijver
