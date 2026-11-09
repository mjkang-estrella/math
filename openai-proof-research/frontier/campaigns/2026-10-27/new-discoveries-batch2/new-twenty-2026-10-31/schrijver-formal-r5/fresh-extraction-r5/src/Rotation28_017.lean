import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_017_checked : rotationChunkCheck 544 32 #[8,2,2,2,2,2,2,2,2,27,10,2,2,2,2,2,2,2,27,12,2,2,2,2,2,2,27,14,2,2,2,2] #[86,104,105,106,107,108,109,110,111,104,82,115,116,117,118,119,120,121,105,77,125,126,127,128,129,130,106,71,134,135,136,137] = true := by decide
end Schrijver
