import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_088_checked : rotationChunkCheck 2816 32 #[21,23,23,25,16,16,16,16,16,19,16,16,16,21,21,16,23,23,25,18,18,18,18,21,18,18,23,23,25,20,20,20] #[210,58,136,49,8,20,31,41,50,74,109,119,128,67,145,194,59,137,50,7,19,30,40,68,108,118,60,138,51,6,18,29] = true := by decide
end Schrijver
