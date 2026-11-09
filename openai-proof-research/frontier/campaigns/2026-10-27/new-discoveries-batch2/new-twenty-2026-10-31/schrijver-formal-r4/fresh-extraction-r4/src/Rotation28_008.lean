import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_008_checked : rotationChunkCheck 256 32 #[7,7,7,23,25,27,14,14,14,0,23,25,27,16,16,16,23,25,27,18,18,18,25,27,20,20,25,27,22,22,27,24] #[195,203,210,201,126,38,66,144,210,265,202,127,39,58,136,202,203,128,40,49,127,193,129,41,39,117,130,42,28,106,43,16] = true := by decide
end Schrijver
