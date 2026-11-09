import ASEPCheck
/-! Negative control that MUST FAIL to compile: claims a mutated certificate passes. -/
namespace ASEP
set_option maxRecDepth 100000
theorem bogus : chk (decode (certChunk0.head! + 128 ^ 22)) = true := by decide +kernel
end ASEP
