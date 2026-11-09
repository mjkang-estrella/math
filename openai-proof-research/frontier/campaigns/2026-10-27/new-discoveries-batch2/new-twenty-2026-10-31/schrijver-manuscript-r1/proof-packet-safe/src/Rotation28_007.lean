import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_007_checked : rotationChunkCheck 224 32 #[27,20,20,25,27,22,22,27,24,27,26,7,7,7,7,7,7,7,7,7,27,10,7,7,7,7,7,7,25,27,12,12] #[31,38,116,121,32,27,105,33,15,34,2,9,21,32,42,51,59,66,72,77,36,79,110,120,129,137,144,150,125,37,73,151] = true := by decide
end Schrijver
