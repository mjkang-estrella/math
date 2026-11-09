import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_003_checked : rotationChunkCheck 96 32 #[3,3,3,3,3,3,27,6,0,0,0,0,0,0,0,0,25,27,8,0,0,0,0,0,0,0,25,27,10,0,0,0] #[61,68,74,79,83,86,13,86,104,105,106,107,108,109,110,111,104,14,82,115,116,117,118,119,120,121,105,15,77,125,126,127] = true := by decide
end Schrijver
