from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent; B=L.parent.parent; P=L.parent
roots=[P/'root-mathdb-breadth-intake-r371',P/'pi-mathdb-full-corpus-inventory-r301',P/'root-mathdb-accepted-exclusions-r304',P/'root-mathdb-cayley-review-intake-r363']
files=[]
for r in roots:
 if 'r301' in r.name:
  files += [p for p in r.rglob('*') if p.is_file() and ('corpus' in p.parts or p.parent==r)]
 else: files += [p for p in r.iterdir() if p.is_file()]
files += [P/x/'reserved-ids.json' for x in ['root-mathdb-gram-intake-r359','root-mathdb-breadth-intake-r369']]
files += [B/'ledger.json',B/'prior-campaign-context.json']
rows=[]
for p in sorted(set(files)):
 b=p.read_bytes(); rows.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
(L/'bindings.json').write_text(json.dumps(dict(frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),mode='flat in-place references; metadata only read before freeze',files=rows),indent=2)+'\n')
print('bound',len(rows),'files')
