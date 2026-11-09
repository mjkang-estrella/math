import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_089_checked : rotationChunkCheck 2848 32 #[23,20,25,22,22,25,24,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9] #[61,107,52,5,17,53,4,0,1,2,3,4,5,6,7,13,14,15,16,17,18,19,25,26,27,28,29,30,36,37,38,39] = true := by decide
end Schrijver
