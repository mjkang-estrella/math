import StackSortCertificate
namespace StackSort
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem wrong_seed_rejected : P 3 ≠ 27 := by decide
theorem wrong_convention_rejected : s [4,1,6,3,5,2] ≠ [6,4,1,5,3,2] := by decide
theorem wrong_threshold_rejected : lower130 * 100 ^ 131 ≤ 4 * 131 * Nat.factorial 130 * 195 ^ 131 := by decide
def lower129 : ℕ := 220552062759138475692555207307310363983455800558178854371728159945941472702434721409914883328344467006873860916494052697326040160925910627118553407710715610920863713112901220146443120447546633716003606389904321838805244556469919228114299060853481144320
theorem wrong_base_rejected : lower129 * 100 ^ 130 ≤ 4 * 130 * Nat.factorial 129 * 173 ^ 130 := by decide
end StackSort
