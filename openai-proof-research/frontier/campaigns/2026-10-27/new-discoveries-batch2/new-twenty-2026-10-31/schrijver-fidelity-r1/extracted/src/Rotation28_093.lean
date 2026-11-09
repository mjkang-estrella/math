import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_093_checked : rotationChunkCheck 2976 32 #[11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,14,14,14,14,14] #[1,2,3,4,5,6,13,14,15,16,17,18,25,26,27,28,29,36,37,38,39,46,47,48,55,56,63,11,23,34,44,53] = true := by decide
end Schrijver
