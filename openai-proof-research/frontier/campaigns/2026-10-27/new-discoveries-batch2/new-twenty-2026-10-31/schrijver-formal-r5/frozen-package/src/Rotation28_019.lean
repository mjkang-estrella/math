import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_019_checked : rotationChunkCheck 608 32 #[7,10,7,7,7,7,7,7,7,27,12,12,2,2,2,2,25,27,14,14,2,2,2,25,27,16,16,2,2,25,27,18] #[82,83,111,121,130,138,145,151,156,115,78,156,192,193,194,195,192,116,72,150,201,202,203,193,117,65,143,209,210,194,118,57] = true := by decide
end Schrijver
