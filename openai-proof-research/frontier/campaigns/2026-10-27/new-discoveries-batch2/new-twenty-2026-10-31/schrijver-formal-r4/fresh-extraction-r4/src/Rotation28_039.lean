import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_039_checked : rotationChunkCheck 1248 32 #[16,13,13,13,13,13,18,18,13,13,13,20,20,20,6,22,22,22,24,24,26,15,15,15,15,15,15,18,15,15,15,15] #[79,110,120,129,137,144,73,151,195,203,210,66,144,210,265,58,136,202,49,127,39,8,20,31,41,50,58,74,109,119,128,136] = true := by decide
end Schrijver
