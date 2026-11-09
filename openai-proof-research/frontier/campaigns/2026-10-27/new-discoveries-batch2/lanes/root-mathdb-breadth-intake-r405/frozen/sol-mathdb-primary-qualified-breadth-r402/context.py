from pathlib import Path
import json
O=Path(__file__).resolve().parent; B=O.parent.parent;R=O.parents[6]
j=json.loads((B/'ledger.json').read_text());print('ledger', {k:j[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']})
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 j=json.loads((O.parent/'root-mathdb-accepted-exclusions-r304'/n).read_text());print(n,json.dumps(j,ensure_ascii=False)[:2500])
print('upstream',Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/upstream.json').read_text()[:1500])
