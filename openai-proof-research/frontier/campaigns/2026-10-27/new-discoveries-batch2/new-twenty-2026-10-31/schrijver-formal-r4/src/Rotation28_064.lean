import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_064_checked : rotationChunkCheck 2048 32 #[26,17,17,17,24,26,19,19,19,26,21,21,26,23,23,25,10,10,10,10,10,10,10,10,13,10,10,10,10,10,26,15] #[127,58,136,202,203,128,49,127,193,129,39,117,130,28,106,16,8,20,31,41,50,58,65,71,74,109,119,128,136,143,134,67] = true := by decide
end Schrijver
