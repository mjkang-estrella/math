import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_042_checked : rotationChunkCheck 1344 32 #[8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,24,8,26,11,11,11,11,11,11] #[27,28,29,30,31,36,37,38,39,40,41,46,47,48,49,50,55,56,57,58,63,64,65,55,71,46,11,23,34,44,53,61] = true := by decide
end Schrijver
