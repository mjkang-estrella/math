import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_009_checked : rotationChunkCheck 288 32 #[27,26,9,9,9,9,9,9,9,9,27,12,9,9,9,9,9,25,27,14,14,9,9,9,25,27,16,16,16,23,25,27] #[44,3,8,20,31,41,50,58,65,71,46,74,109,119,128,136,143,134,47,67,145,194,202,209,135,48,59,137,203,210,136,49] = true := by decide
end Schrijver
