import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_075_checked : rotationChunkCheck 2400 32 #[17,12,12,12,19,19,19,26,21,21,21,23,23,25,14,14,14,14,14,14,17,14,14,14,14,19,19,14,14,21,21,21] #[145,194,202,209,59,137,203,210,50,128,194,40,118,29,7,19,30,40,49,57,68,108,118,127,135,60,138,193,201,51,129,195] = true := by decide
end Schrijver
