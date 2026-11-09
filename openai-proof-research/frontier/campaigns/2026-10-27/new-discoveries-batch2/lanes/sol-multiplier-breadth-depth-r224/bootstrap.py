import pathlib,hashlib,json,shutil
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for lane,names in [('sol-wide-analytic-scout-r223',['SCOUTING.md','source-map.json','history-screen.json','freeze.json','provenance.json']),('sol-wide-algebra-scout-r222',['SCOUTING.md','progress.md','SUMMARY.md'])]:
 for name in names:
  p=B/'lanes'/lane/name
  if not p.exists():continue
  h=sha(p);q=L/'frozen'/lane/name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
  assert sha(p)==sha(q)==h
  rows.append(dict(original=str(p),copy=str(q),sha256=h))
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 p=B/name;q=L/'administrative'/name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
(L/'freeze.json').write_text(json.dumps(rows,indent=2))
print(json.dumps(rows,indent=2))
