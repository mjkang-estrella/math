import json,hashlib,sys,resource,signal
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(220)
D=Path(__file__).resolve().parent;R=D.parents[5];B=D.parent
if sys.argv[1]=='before':
 paths=[R/'AGENTS.md',B.parent/'AGENTS.md',B.parent/'ledger.json',B.parent/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md']
 for name in ['sol-fresh-finite-optimization-r26','sol-polyomino57-preliminary-review-r1','sol-polyomino57-current-prior-review-r2','sol-polyomino57-compressed-review-r1','root-polyomino57-full-formal-adoption-r1']:
  paths += [p for p in (B/name).rglob('*') if p.is_file() and not any(x in p.relative_to(B/name).parts for x in ['input','input-copy','__pycache__'])]
 paths += [p for p in (B/'sol-steiner-reflection-preliminary-review-r1'/'live').rglob('*') if p.is_file()]
 rows={str(p):dict(bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths}
 (D/'hash-before.json').write_text(json.dumps(rows,indent=2));print(len(rows))
else:
 rows=json.loads((D/'hash-before.json').read_text());bad=[]
 for p,m in rows.items():
  b=Path(p).read_bytes()
  if len(b)!=m['bytes'] or hashlib.sha256(b).hexdigest()!=m['sha256']:bad.append(p)
 (D/'hash-after.json').write_text(json.dumps(dict(checked=len(rows),mismatches=bad),indent=2));print(len(rows),bad)
