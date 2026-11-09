from pathlib import Path
import json,hashlib,datetime
ROOT=Path('/home/mj-kang/Documents/Dev/math'); BASE=ROOT/'openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2'; LANES=BASE/'lanes'; OUT=LANES/'sol-mathdb-primary-qualified-breadth-r402'
seeds=list((LANES/'root-mathdb-breadth-intake-r401').glob('*.json'))+[LANES/'pi-mathdb-full-corpus-inventory-r301/manifest.json', LANES/'root-mathdb-cayley-review-intake-r363/disposition.json']
seeds+=list((LANES/'root-mathdb-accepted-exclusions-r304').glob('*.json'))
seeds += [BASE/'ledger.json',BASE/'prior-campaign-context.json',ROOT/'openai-proof-research/sources/upstream.json',ROOT/'openai-proof-research/sources/CONTENTS.md',ROOT/'openai-proof-research/sources/preprints-tree.json']
seen={}; unresolved=set()
def strings(x):
 if isinstance(x,str):yield x
 elif isinstance(x,list):
  for a in x:yield from strings(a)
 elif isinstance(x,dict):
  for k,v in x.items():yield k;yield from strings(v)
queue=list(seeds)
while queue:
 p=queue.pop();p=p.resolve()
 if str(p) in seen or not p.is_file():continue
 b=p.read_bytes();seen[str(p)]={'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 if p.suffix!='.json':continue
 try:j=json.loads(b)
 except Exception:continue
 for s in strings(j):
  if len(s)>600 or '\n' in s or s.startswith(('http:','https:')):continue
  if '/' not in s and not s.endswith(('.json','.jsonl','.md','.py')):continue
  candidates=[Path(s),ROOT/s,BASE/s,LANES/s,p.parent/s]
  hit=next((a for a in candidates if a.is_file()),None)
  if hit:queue.append(hit)
  elif '/' in s:unresolved.add(s)
(OUT/'frozen-references.json').write_text(json.dumps({'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'references':sorted(seen.values(),key=lambda x:x['path']),'unresolved_pathlike_strings':sorted(unresolved)},indent=2)+'\n')
print('Frozen',len(seen),'files; unresolved',len(unresolved))
