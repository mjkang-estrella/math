import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent;B=L.parent
ids=set(json.loads((B/'root-mathdb-breadth-intake-r389/reserved-ids.json').read_text())['ids']);out=[]
for x in json.loads((L/'corpus-bindings.json').read_text())['refs']:
 p=pathlib.Path(x['path'])
 for line in p.open():
  r=json.loads(line)
  if int(r['mathdb_id']) in ids:
   out.append({'chunk':str(p),'record':r})
assert len(out)==50
(L/'statements.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
for x in out:print(json.dumps(x['record'],ensure_ascii=False))
