from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent; B=L.parent.parent; P=L.parent/'sol-inverse-period-doubling-breadth-depth-r240'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
paths=[P/x for x in ['discovery.md','checks.py','checks-result.json','bindings.jsonl','provenance.json','retrieval.jsonl','FAILURES.md']]
paths+=[P/'downloads'/x for x in ['current-stip8.pdf','durand.pdf','inverse-current.xml','durand-search.xml','merta-general.pdf','merta-bs.pdf']]
paths+=[P/'texts'/x for x in ['stip8.txt','durand.txt','merta-general.txt','merta-bs.txt']]
for p in paths:
 if not p.is_file():continue
 d=L/'frozen'/p.relative_to(P);d.parent.mkdir(parents=True,exist_ok=True); before=h(p);shutil.copyfile(p,d);assert before==h(p)==h(d); rows.append({'original':str(p),'copy':str(d.relative_to(L)),'sha256':before})
for p in [B/'ledger.json',B/'prior-campaign-context.json',B/'AGENTS.md',B.parents[3]/'AGENTS.md']:
 if p.exists():
  d=L/'administrative'/p.name;d.parent.mkdir(exist_ok=True);shutil.copyfile(p,d)
(L/'bindings.json').write_text(json.dumps(rows,indent=2))
print('frozen',len(rows))
