import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_045_checked : rotationChunkCheck 1440 32 #[18,15,15,15,15,20,20,15,15,22,22,22,24,24,26,17,17,17,17,17,20,17,17,17,22,22,17,24,24,26,19,19] #[79,110,120,129,137,73,151,195,203,66,144,210,58,136,49,8,20,31,41,50,74,109,119,128,67,145,194,59,137,50,7,19] = true := by decide
end Schrijver
