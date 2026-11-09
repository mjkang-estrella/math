from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
R=L.parent/'sol-zeckendorf-cell-concentration-formal-r7'
rows=json.loads((L/'freeze.json').read_text())
for n in ['pins.json','immutable-references.json','replay-receipt.json','verification-receipt.json']:
 p=R/n; data=p.read_bytes(); q=L/'frozen'/R.name/n; q.write_bytes(data)
 h=hashlib.sha256(data).hexdigest(); assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h))
for r in json.loads((R/'immutable-references.json').read_text()):
 for k in ['original','copy']: assert hashlib.sha256(Path(r[k]).read_bytes()).hexdigest()==r['sha256']
(L/'freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
for n in ['Literal','Terminal','Law','Cells','Product','Prefix','Marks','Boards','Injection','Abundance','Tail','Concentration','Inventory','Audit']:
 (L/(n+'.lean')).write_bytes((L/'frozen'/R.name/(n+'.lean')).read_bytes())
for n in ['runner.py','pins.json','immutable-references.json']:
 (L/n).write_bytes((L/'frozen'/R.name/n).read_bytes())
print('setup verified')
