from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent; B=L.parent
paths=[Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources')/n for n in ['upstream.json','CONTENTS.md','preprints-tree.json']]
paths += [B/'sol-wide-analysis-scout-r221'/n for n in ['freeze-history.json','history-screen.json','sources/sol-fresh-analytic-wide-scout-r219--alias-history.json','sources/sol-fresh-analytic-wide-scout-r219--candidate-history.json','sources/sol-fresh-analytic-wide-scout-r219--target-history.json','sources/sol-fresh-analytic-wide-scout-r219--history-analytic.json']]
rows=[]
for p in paths:
 if p.is_file(): rows.append({'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(L/'registry-freeze.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':rows,'note':'upstream and first 30 lines of CONTENTS had administrative orientation read before this binding; no novelty conclusion from that read'},indent=2)+'\n')
print(json.dumps(rows,indent=2))
