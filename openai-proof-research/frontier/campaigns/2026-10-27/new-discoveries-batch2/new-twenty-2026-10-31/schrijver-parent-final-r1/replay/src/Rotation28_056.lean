import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_056_checked : rotationChunkCheck 1792 32 #[18,18,18,21,21,21,24,18,26,23,23,26,25,20,20,20,20,20,20,23,23,26,25,22,22,22,25,24,1,1,1,1] #[25,26,36,11,23,34,86,104,82,10,22,83,9,0,1,2,13,14,25,11,23,86,10,0,1,13,11,0,0,1,2,3] = true := by decide
end Schrijver
