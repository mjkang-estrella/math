from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
B=L.parent.parent
R=B.parents[3]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
refs=[]
for pattern in ('*r245/SCOUTING.md','*r246/SCOUTING.md','*r247/SCOUTING.md','*r248/SCOUTING.md'):
 for p in B.joinpath('lanes').glob(pattern):
  h=sha(p); q=L/'frozen'/p.parent.name/p.name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
  assert sha(q)==sha(p)==h
  refs.append(dict(original=str(p),copy=str(q),sha256=h,kind='scientific'))
for p in (B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',R/'AGENTS.md',R/'sources/upstream.json',R/'sources/CONTENTS.md'):
 if p.exists():
  q=L/'administrative'/p.name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
  refs.append(dict(original=str(p),copy=str(q),sha256=sha(q),kind='administrative-snapshot'))
(L/'freeze.json').write_text(json.dumps(dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(),references=refs),indent=2))
for x in refs:
 if x['kind']=='scientific':
  print('\nFILE',x['copy']); print(Path(x['copy']).read_text())
print('ADMIN KEYS')
for name in ('ledger.json','prior-campaign-context.json'):
 d=json.loads((L/'administrative'/name).read_text());print(name,json.dumps(d)[:18000])
