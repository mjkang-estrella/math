import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_043_checked : rotationChunkCheck 1376 32 #[11,11,14,8,8,8,8,8,8,16,8,8,8,8,8,18,8,8,8,8,20,8,8,8,22,8,8,24,24,26,13,13] #[68,74,86,104,105,106,107,108,109,82,115,116,117,118,119,77,125,126,127,128,71,134,135,136,64,142,143,56,134,47,10,22] = true := by decide
end Schrijver
