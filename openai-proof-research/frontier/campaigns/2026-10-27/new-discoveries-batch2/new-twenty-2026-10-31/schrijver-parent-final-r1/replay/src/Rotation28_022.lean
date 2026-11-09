import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_022_checked : rotationChunkCheck 704 32 #[11,11,11,14,11,11,11,11,11,27,16,16,11,11,11,27,18,18,18,25,27,20,20,20,27,22,22,27,24,24,26,13] #[58,65,71,74,109,119,128,136,143,134,67,145,194,202,209,135,59,137,203,210,136,50,128,194,137,40,118,138,29,107,17,7] = true := by decide
end Schrijver
