import ASEPVertex

/-! Negative control (expected to FAIL): the tight-cut list without its first cut `{0,3}` does not
cover all cuts tight at `x*`, so the completeness fact used by the checker breaks. -/

open ASEP

set_option maxRecDepth 100000 in
example : ∀ S : Finset (Fin 8), 2 ≤ S.card → S.card ≤ 6 → fluxN S = 4 →
    ∃ l ∈ tightCutList.tail, S = l.toFinset := by decide +kernel
