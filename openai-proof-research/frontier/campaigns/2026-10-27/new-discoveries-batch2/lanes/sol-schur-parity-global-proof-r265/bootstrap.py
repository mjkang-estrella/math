from pathlib import Path
import hashlib,json,shutil,datetime
L=Path(__file__).resolve().parent; B=L.parent.parent; R=L.parent/'sol-wide-finite-structural-mechanisms-r262'
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for root,names in [(R,['SUMMARY.md','discovery.md','progress.md','SCOUTING.md','provenance.json','provenance-status.json','schur-checks.json','triangle-packing.json','mechanism2.py','attack.py','exact_checks.py','schur-prior.json','schur2.json','retrieval.jsonl']), (L.parent/'root-scout-r262-triage',['SUMMARY.md','discovery.md','progress.md'])]:
 for name in names:
  p=root/name
  if not p.exists():continue
  q=L/'frozen'/root.name/name;q.parent.mkdir(parents=True,exist_ok=True)
  before=h(p);shutil.copyfile(p,q);assert before==h(p)==h(q)
  rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=before,kind='scientific'))
for p in sorted((R/'sources').rglob('*')):
 if not p.is_file():continue
 if not p.name.startswith(('1904.01925v2.','1609.07639v2.')):continue
 q=L/'frozen'/'sources'/p.relative_to(R/'sources');q.parent.mkdir(parents=True,exist_ok=True)
 before=h(p);shutil.copyfile(p,q);assert before==h(p)==h(q)
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=before,kind='scientific'))
for name in ['ledger.json','prior-campaign-context.json','AGENTS.md']:
 p=B/name;q=L/'admin'/name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h(q),kind='administrative-snapshot'))
(L/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
