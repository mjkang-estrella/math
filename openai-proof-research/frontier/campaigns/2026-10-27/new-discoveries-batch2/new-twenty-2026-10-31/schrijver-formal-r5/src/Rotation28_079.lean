import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_079_checked : rotationChunkCheck 2528 32 #[8,8,8,8,8,8,11,5,5,5,5,5,5,5,13,5,5,5,5,5,5,15,5,5,5,5,5,17,5,5,5,5] #[44,53,61,68,74,79,86,104,105,106,107,108,109,110,82,115,116,117,118,119,120,77,125,126,127,128,129,71,134,135,136,137] = true := by decide
end Schrijver
