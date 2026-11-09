import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_032_checked : rotationChunkCheck 1024 32 #[13,13,13,13,16,13,13,13,13,13,18,18,13,13,13,20,20,20,27,22,22,22,24,24,26,15,15,15,15,15,15,18] #[41,50,58,65,74,109,119,128,136,143,67,145,194,202,209,59,137,203,210,50,128,194,40,118,29,7,19,30,40,49,57,68] = true := by decide
end Schrijver
