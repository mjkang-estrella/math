from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
R=B.parents[3]
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
(L/'admin').mkdir(exist_ok=True)
admin=[]
for p in [R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json']:
 q=L/'admin'/('ancestor-AGENTS.md' if p==R/'AGENTS.md' else p.name)
 shutil.copyfile(p,q);admin.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=digest(q)))
(L/'admin-bindings.json').write_text(json.dumps(admin,indent=2))
refs=[]
old=L.parent/'sol-wide-specialist-arithmetic-scout-r274'
for p in sorted(old.rglob('*')):
 if p.is_file() and ('sources' in p.parts or p.name in ['discovery.md','SCOUTING.md','SUMMARY.md','bindings.json','history.json','access.jsonl','source-receipts.json']):
  h=digest(p);refs.append(dict(path=str(p),sha256=h,sha256_after=digest(p),immutable_reference=True))
(L/'source-bindings.json').write_text(json.dumps(refs,indent=2))
print('Frozen',len(refs),'immutable references; admin snapshots',len(admin))
for name in ['discovery.md','SCOUTING.md','SUMMARY.md','bindings.json']:
 print('\nFILE',name,'\n',(old/name).read_text()[:35000])
