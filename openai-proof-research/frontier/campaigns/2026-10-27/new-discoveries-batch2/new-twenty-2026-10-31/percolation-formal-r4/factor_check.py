from pathlib import Path
import json
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4');S=R/'check-factoring/src'
rows=json.loads((R/'normalized-trimmed.json').read_text())['steps'][12000:12500]
def cl(c):return '['+','.join(f'({abs(x)-1},{str(x<0).lower()})' for x in c)+']'
base=['namespace Percolation.NReplay','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
out=['import NReplay023']+base
for i,c,hs in rows:out+=[f'def cl_{i} : CNF.NClause := {cl(c)}']
out+=['end Percolation.NReplay'];(S/'NDefs024.lean').write_text('\n'.join(out)+'\n')
mods=['NDefs024']
for k in range(5):
 name=f'NCheck024_{k}';out=[f'import {mods[-1]}']+base
 for i,c,hs in rows[100*k:100*k+100]:out+=[f'theorem rc_{i} : CNF.rup cl_{i} [{",".join(f"cl_{h}" for h in hs)}] = true := by decide']
 out+=['end Percolation.NReplay'];(S/(name+'.lean')).write_text('\n'.join(out)+'\n');mods+=[name]
(R/'check-factoring/order.txt').write_text('\n'.join(mods)+'\n')
print('generated',mods)
