import SSA5.Endpoint
open Filter Topology
namespace SSA
example : ¬ limsup (rateSeq 5 (TCDominant 5)) atTop <
    limsup (rateSeq 5 (TCDominant 5)) atTop := lt_irrefl _
example : ¬ (1299 * (10^20 : ℕ) ≤ 400 *
    (vS [.T,.A,.C,.A,.A] + vS [.T,.A,.C,.A,.C] +
     vS [.T,.A,.C,.A,.G] + vS [.T,.A,.C,.A,.T])) := by decide +kernel
end SSA
