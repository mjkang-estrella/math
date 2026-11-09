import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_012_checked : rotationChunkCheck 384 32 #[18,18,13,25,27,20,20,25,27,22,22,27,24,27,26,15,15,15,15,15,15,18,15,15,15,27,20,20,25,27,22,22] #[52,130,192,150,65,42,120,151,66,31,109,67,19,68,6,5,17,28,38,47,55,53,106,116,125,71,43,121,156,72,32,110] = true := by decide
end Schrijver
