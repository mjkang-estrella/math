import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_023_checked : rotationChunkCheck 736 32 #[13,13,13,13,13,13,16,13,13,13,13,13,18,18,13,13,27,20,20,20,27,22,22,27,24,24,26,15,15,15,15,15] #[19,30,40,49,57,64,68,108,118,127,135,142,60,138,193,201,143,51,129,195,144,41,119,145,30,108,18,6,18,29,39,48] = true := by decide
end Schrijver
