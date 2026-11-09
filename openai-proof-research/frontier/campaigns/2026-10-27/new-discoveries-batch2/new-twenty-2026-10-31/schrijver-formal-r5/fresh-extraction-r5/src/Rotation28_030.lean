import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_030_checked : rotationChunkCheck 960 32 #[4,4,4,27,16,16,4,4,4,27,18,18,4,4,27,20,20,20,27,22,22,22,24,24,26,11,11,11,11,11,11,11] #[193,194,195,192,72,150,201,202,203,193,65,143,209,210,194,57,135,201,195,48,126,192,38,116,27,9,21,32,42,51,59,66] = true := by decide
end Schrijver
