import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_074_checked : rotationChunkCheck 2368 32 #[10,10,26,17,17,17,3,26,19,19,19,26,21,21,21,23,23,25,12,12,12,12,12,12,12,15,12,12,12,12,12,17] #[203,210,201,66,144,210,265,202,58,136,202,203,49,127,193,39,117,28,8,20,31,41,50,58,65,74,109,119,128,136,143,67] = true := by decide
end Schrijver
