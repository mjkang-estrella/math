from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent; B=L.parent.parent; S=L.parent/'sol-wide-finite-mechanism-scout-r258'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
for folder,files in [('scientific',[p for p in S.rglob('*') if p.is_file() and 'administrative' not in p.parts and 'frozen' not in p.parts]),('administrative',[B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md'])]:
 for p in files:
  rel=p.relative_to(S) if folder=='scientific' else Path(p.name if p.parent==B else 'ancestor-AGENTS.md')
  dst=L/folder/rel;dst.parent.mkdir(parents=True,exist_ok=True)
  before=h(p);shutil.copyfile(p,dst);after=h(p)
  assert before==after==h(dst)
  records.append(dict(original=str(p),copy=str(dst.relative_to(L)),sha256=before,kind=folder))
(L/'freeze-bindings.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({'frozen_files':len(records)}))
