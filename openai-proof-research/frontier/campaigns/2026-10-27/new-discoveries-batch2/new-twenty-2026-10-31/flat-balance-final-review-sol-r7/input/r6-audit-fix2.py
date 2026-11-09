p='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/flat-balance-independent-audit-pi-r6/audit/ControlsIndPos.lean'
s=open(p).read()
s=s.replace("    rw [if_neg hz]","    simp only [hz, if_true, ite_false]") if 0 else s
s=s.replace("    rw [if_neg hz]","    simp [hz]")
s=s.replace("    rw [if_pos hp, cliqueCount_zero]","    simp [hp, cliqueCount_zero]")
s=s.replace("  rw [oddCliqueSum_K33, evenCliqueSum_K33]; omega","  rw [oddCliqueSum_K33, evenCliqueSum_K33]")
s=s.replace("  rw [evenCliqueSum_K33, oddCliqueSum_K33]; norm_num","  rw [evenCliqueSum_K33, oddCliqueSum_K33]\n  push_cast\n  norm_num")
open(p,'w').write(s)
print('ok')
