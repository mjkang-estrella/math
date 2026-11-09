import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_010_checked : rotationChunkCheck 320 32 #[18,18,18,25,27,20,20,25,27,22,22,27,24,27,26,11,11,11,11,11,11,11,27,14,11,11,11,11,11,27,16,16] #[50,128,194,137,50,40,118,138,51,29,107,52,17,53,4,7,19,30,40,49,57,64,55,68,108,118,127,135,142,56,60,138] = true := by decide
end Schrijver
