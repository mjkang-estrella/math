import pathlib,json,hashlib
O=pathlib.Path(__file__).resolve().parent;L=O.parent;F=L/'root-mathdb-linear-two-tree-review-intake-r501/frozen/sol-mathdb-linear-two-tree-source-prior-review-r498'
refs=json.loads((F/'flat-original-bindings.json').read_text())['files']
rows=[]
for r in refs:
 if any(s in r['path'] for s in ('1712.05883.pdf','1712.05883.txt','P3-337963','helper_guard.py','AGENTS.md','ledger.json','prior-campaign-context.json','upstream.json')):
  p=pathlib.Path(r['path']);b=p.read_bytes();a=dict(path=str(p.resolve()),size=len(b),sha256=hashlib.sha256(b).hexdigest())
  assert all(a[k]==r[k] for k in ('size','sha256')),str(p)
  rows.append(a)
for p in [L.parents[4]/'AGENTS.md']:
 pass
(O/'source-actual-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Bound',len(rows),'actual external inputs')
