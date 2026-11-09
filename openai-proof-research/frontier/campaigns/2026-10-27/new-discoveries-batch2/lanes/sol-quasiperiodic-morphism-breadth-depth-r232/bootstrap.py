import pathlib,hashlib,json,shutil
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
R=B/'lanes/sol-wide-certifiable-structures-r229'
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
bindings=[]
for name in ['SUMMARY.md','SCOUTING.md','ATTACK.md','PROOF.md','discovery.md','progress.md','provenance.json','history-screen.json','old-alias-screen.json']:
 p=R/name
 if p.exists():
  q=L/'frozen'/name;q.parent.mkdir(parents=True,exist_ok=True);before=h(p);shutil.copyfile(p,q);assert before==h(p)==h(q);bindings.append({'original':str(p),'copy':str(q),'sha256':before})
for p in (R/'primary').glob('*'):
 if p.is_file():
  q=L/'frozen/primary'/p.name;q.parent.mkdir(parents=True,exist_ok=True);before=h(p);shutil.copyfile(p,q);assert before==h(p)==h(q);bindings.append({'original':str(p),'copy':str(q),'sha256':before})
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 p=B/name;q=L/'administrative'/name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
(L/'frozenbindings.json').write_text(json.dumps(bindings,indent=2))
print('Frozen',len(bindings),'scientific files before reading')
for name in ['SUMMARY.md','ATTACK.md','PROOF.md','SCOUTING.md']:
 p=L/'frozen'/name
 print('\nFILE',name,'\n',p.read_text()[:22000])
