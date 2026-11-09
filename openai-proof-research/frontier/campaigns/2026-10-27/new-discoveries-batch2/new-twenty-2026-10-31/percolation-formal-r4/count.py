import json
from pathlib import Path
r=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4')
a=json.loads((r/'normalized-trimmed.json').read_text())['steps']
for n in [500,1000,2000,5000,10000,20000,129671]:print(n,len({h for _,_,hs in a[:n] for h in hs if h<=14698}))
