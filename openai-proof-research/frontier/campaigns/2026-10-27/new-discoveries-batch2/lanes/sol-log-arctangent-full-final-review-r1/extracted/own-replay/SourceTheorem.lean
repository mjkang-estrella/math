import MeanEPositive
import GapMonotonicity
set_option autoImplicit false
set_option warningAsError true
namespace LogArctangentSource
/-- The literal two-branch inequality of published Conjecture 37. -/
theorem source_conjecture37 : SourceClaim :=
  sourceClaim_of_E_pos (fun _ ht => LogArctangentMean.E_pos ht)
end LogArctangentSource
