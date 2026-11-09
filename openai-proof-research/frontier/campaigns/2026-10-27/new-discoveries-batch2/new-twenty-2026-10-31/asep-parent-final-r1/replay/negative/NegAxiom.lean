import AuditLib

/-! Negative control (expected to FAIL): the audit command rejects a theorem that depends on a new axiom. -/

axiom neg_cheat : False

theorem neg_uses_cheat : (2 : Nat) + 2 = 5 := neg_cheat.elim

#assert_std_axioms neg_uses_cheat
