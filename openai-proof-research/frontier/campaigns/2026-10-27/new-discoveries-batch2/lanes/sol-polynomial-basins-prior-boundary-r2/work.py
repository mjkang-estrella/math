from pathlib import Path
import hashlib,json,datetime,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
R=L.parent/'sol-polynomial-basins-breadth-depth-r237'
P=L.parent/'sol-polynomial-basins-preliminary-review-r1'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,o): p.write_text(json.dumps(o,indent=2)+'\n')
records=[]
paths=[R/'PROOF.md',R/'routine-proof.md',R/'source-bindings.json',R/'provenance.json',R/'FAILURES.md',P/'review.md',P/'provenance.json',P/'body-retrieval.json',P/'retrieval-receipts.json',P/'failures.md']
paths+=list((P/'independent-sources').glob('*'))
paths+= [p for p in (R/'sources').glob('*') if any(s in p.name for s in ['borisov','follow','precursor'])]
for p in paths:
 if not p.is_file(): continue
 h=sha(p); q=L/'frozen'/h/p.name; q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists(): shutil.copyfile(p,q)
 assert sha(p)==sha(q)==h
 records.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h,bytes=p.stat().st_size))
dump(L/'freeze-before.json',dict(utc=str(datetime.datetime.now(datetime.timezone.utc)),files=records))
admin=[]
for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md']:
 if p.exists():
  q=L/'administrative'/p.name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q);admin.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=sha(q)))
dump(L/'administrative-snapshots.json',admin)
print(json.dumps(records,indent=2))
