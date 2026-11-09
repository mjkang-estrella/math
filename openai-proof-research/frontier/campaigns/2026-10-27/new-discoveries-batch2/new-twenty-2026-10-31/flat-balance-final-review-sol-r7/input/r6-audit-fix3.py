p='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/flat-balance-independent-audit-pi-r6/audit/ControlsIndPos.lean'
s=open(p).read()
s=s.replace('import FlatBalanceBridges\n','import FlatBalanceBridges\nimport Mathlib.Tactic.Linarith  -- audit-only: Real-cast norm_num support\n',1)
open(p,'w').write(s)
print('ok')
