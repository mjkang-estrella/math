from pathlib import Path
import sys,json,hashlib
L=Path(__file__).resolve().parent
B=L/'bindings.json';rows=json.loads(B.read_text())
for arg in sys.argv[1:]:
 p=Path(arg).resolve();data=p.read_bytes();h=hashlib.sha256(data).hexdigest()
 q=L/'references'/p.name
 if q.exists():assert q.read_bytes()==data
 else:q.write_bytes(data)
 assert p.read_bytes()==q.read_bytes()==data
 row=dict(original=str(p),copy=str(q.relative_to(L)),sha256=h)
 if row not in rows:rows.append(row)
B.write_text(json.dumps(rows,indent=2)+'\n')
