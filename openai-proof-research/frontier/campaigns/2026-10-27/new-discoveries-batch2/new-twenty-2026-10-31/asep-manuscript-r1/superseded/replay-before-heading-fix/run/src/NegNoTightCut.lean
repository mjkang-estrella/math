import ASEPVertex

/-! Negative control (expected to FAIL): `x*` does have tight cuts (`4 x*(δ(S)) = 4`). -/

open ASEP

set_option maxRecDepth 100000 in
example : ∀ S : Finset (Fin 8), 2 ≤ S.card → S.card ≤ 6 → 5 ≤ fluxN S := by decide +kernel
