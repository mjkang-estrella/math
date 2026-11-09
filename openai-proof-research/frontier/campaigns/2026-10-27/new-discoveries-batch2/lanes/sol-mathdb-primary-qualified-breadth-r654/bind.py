from pathlib import Path
import json,hashlib,re
B=Path(__file__).resolve().parents[2]; O=Path(__file__).resolve().parent; I=B/'lanes/root-mathdb-breadth-intake-r653'; R=B/'lanes/pi-mathdb-full-corpus-inventory-r301'
f=json.loads((O/'flat-bindings.json').read_text())
def bind(p,expected=None):
 p=p.resolve();d={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size}
 if expected:assert d=={'sha256':expected['sha256'],'size':expected.get('bytes',expected.get('size'))},str(p)
 f[str(p)]=d
m=json.loads((R/'manifest.json').read_text());chunks=[x for x in m['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(m['frozen_inputs'])==8
for x in chunks+m['frozen_inputs']:bind(R/x['path'],x)
for p in [B/'ledger.json',B/'prior-campaign-context.json',B/'lanes/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',B/'lanes/root-mathdb-accepted-exclusions-r304/historical-dispositions.json',B/'lanes/root-mathdb-cayley-review-intake-r363/DECISION.md']:bind(p)
(O/'flat-bindings.json').write_text(json.dumps(f,indent=2)+'\n')
# Only parse scientific rows selected by exact numeric ID, not unrelated statements.
ids=set(json.loads((I/'reserved-ids-r654.json').read_text())['ids']); rows=[]
for x in chunks:
 p=R/x['path']
 for ln,line in enumerate(p.open(),1):
  mm=re.search(r'"(?:mathdb_id|id)"\s*:\s*(\d+)',line)
  if mm and int(mm[1]) in ids:
   r=json.loads(line); rows.append({'chunk':str(p),'line':ln,'record':r,'canonical_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(rows)==50,len(rows)
(O/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('record keys',rows[0]['record'].keys())
for x in rows:print(json.dumps(x['record'],ensure_ascii=False))
