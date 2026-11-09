import re
p='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/flat-balance-independent-audit-pi-r6/audit/ControlsIndPos.lean'
s=open(p).read()
s=s.replace("""example (k : ℕ) (hk : 0 < k) : cliqueCount EmptyGraph k = 0 := by
  have h0 : Fintype.card (Fin 0) = 0 := by simp
  omega""","""example (k : ℕ) (hk : 0 < k) : cliqueCount EmptyGraph k = 0 := by
  have h0 : Fintype.card (Fin 0) = 0 := by simp
  exact cliqueCount_of_card_lt EmptyGraph (by omega)""")
old=s[s.index('/-- P10.'):]
new='''/-- P10. Real-cast bridge: the real absolute difference of the clique sums
is exactly 4 (the true discrepancy value, through the cast bridge). -/
example : |(Nat.cast (oddCliqueSum K33) : ℝ) - (Nat.cast (evenCliqueSum K33) : ℝ)| = 4 := by
  rw [evenCliqueSum_K33, oddCliqueSum_K33]; norm_num

/-- P11. The real cast of the discrepancy itself is 4 (no truncation). -/
example : (Nat.cast (discrepancyNat K33) : ℝ) = 4 := by
  rw [discrepancyNat_K33]; norm_num

end FlatBalance.IndControl
'''
s=s[:s.index('/-- P10.')]+new
open(p,'w').write(s)
print("patched")
