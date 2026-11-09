import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_006_checked : rotationChunkCheck 192 32 #[0,0,0,0,23,25,27,12,12,0,0,0,23,25,27,14,14,0,0,23,25,27,16,16,16,23,25,27,18,18,18,25] #[192,193,194,195,192,116,27,72,150,201,202,203,193,117,28,65,143,209,210,194,118,29,57,135,201,195,119,30,48,126,192,120] = true := by decide
end Schrijver
