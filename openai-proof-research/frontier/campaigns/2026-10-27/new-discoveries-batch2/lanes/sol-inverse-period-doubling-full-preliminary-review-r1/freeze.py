from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent; B=L.parent.parent
R=L.parent/'sol-inverse-period-doubling-base2-r242'
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
paths=[R/n for n in ['PROOF.md','PRIOR-ART.md','FAILURES.md','RUN.md','SUMMARY.md','checks.py','checks-result.json','provenance.json','retrieval.json','thin-retrieval.json']]
paths += [Path(r['original']) for r in json.loads((R/'bindings.json').read_text())]
for p in dict.fromkeys(paths):
 q=L/'frozen'/p.relative_to(L.parent);q.parent.mkdir(parents=True,exist_ok=True)
 before=h(p);shutil.copyfile(p,q);assert before==h(p)==h(q)
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=before))
(L/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[2]/'AGENTS.md']:
 if p.exists():
  q=L/'administrative'/p.name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
print(json.dumps({'frozen_files':len(rows),'administrative':'snapshots only'}))
