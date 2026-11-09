import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_004_checked : rotationChunkCheck 128 32 #[0,0,0,25,27,12,0,0,0,0,0,25,27,14,0,0,0,0,25,27,16,16,0,0,25,27,18,18,0,25,27,20] #[128,129,130,106,16,71,134,135,136,137,138,107,17,64,142,143,144,145,108,18,56,134,150,151,109,19,47,125,156,110,20,37] = true := by decide
end Schrijver
