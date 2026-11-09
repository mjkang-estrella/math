import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_028_checked : rotationChunkCheck 896 32 #[4,4,4,4,4,4,4,4,12,4,4,4,4,4,4,4,14,4,4,4,4,4,4,16,4,4,4,4,4,18,4,4] #[104,105,106,107,108,109,110,111,82,115,116,117,118,119,120,121,77,125,126,127,128,129,130,71,134,135,136,137,138,64,142,143] = true := by decide
end Schrijver
