import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_035_checked : rotationChunkCheck 1120 32 #[6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6] #[18,19,20,21,25,26,27,28,29,30,31,32,36,37,38,39,40,41,42,46,47,48,49,50,51,55,56,57,58,59,63,64] = true := by decide
end Schrijver
