import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_060_checked : rotationChunkCheck 1920 32 #[1,1,1,1,1,1,1,26,11,1,1,1,1,1,1,26,13,1,1,1,1,1,26,15,1,1,1,1,26,17,17,1] #[115,116,117,118,119,120,121,105,77,125,126,127,128,129,130,106,71,134,135,136,137,138,107,64,142,143,144,145,108,56,134,150] = true := by decide
end Schrijver
