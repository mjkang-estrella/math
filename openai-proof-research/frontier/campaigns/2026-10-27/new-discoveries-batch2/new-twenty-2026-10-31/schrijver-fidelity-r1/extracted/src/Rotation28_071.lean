import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_071_checked : rotationChunkCheck 2272 32 #[3,3,3,3,3,13,3,3,3,3,3,3,15,3,3,3,3,3,17,3,3,3,3,19,19,3,3,21,21,3,23,23] #[117,118,119,120,121,77,125,126,127,128,129,130,71,134,135,136,137,138,64,142,143,144,145,56,134,150,151,47,125,156,37,115] = true := by decide
end Schrijver
