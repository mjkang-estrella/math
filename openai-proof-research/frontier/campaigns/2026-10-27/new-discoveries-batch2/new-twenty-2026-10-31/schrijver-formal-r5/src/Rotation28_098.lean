import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_098_checked : rotationChunkCheck 3136 32 #[15,23,15,25,20,20,20,23,20,25,22,22,25,24,17,17,17,17,17,17,17,17,17,17,20,20,20,23,17,25,22,22] #[105,82,115,77,10,22,33,83,111,78,9,21,79,8,0,1,2,3,13,14,15,25,26,36,11,23,34,86,104,82,10,22] = true := by decide
end Schrijver
