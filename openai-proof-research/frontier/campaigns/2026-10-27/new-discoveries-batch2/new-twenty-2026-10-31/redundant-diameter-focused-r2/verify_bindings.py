"""Read-only input verification. Usage: python verify_bindings.py [new-output.json]."""
from pathlib import Path
import hashlib,json,datetime,sys
p=Path(__file__).resolve().parent
f=p/'frozen-inputs.json'; bindings=json.loads(f.read_text()); rows=[]
for name,expected in bindings.items():
 q=Path(name); actual=hashlib.sha256(q.read_bytes()).hexdigest() if q.is_file() else None
 rows.append(dict(path=name,expected=expected,actual=actual,match=actual==expected))
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),count=len(rows),manifest_sha256=hashlib.sha256(f.read_bytes()).hexdigest(),mismatches=[r['path'] for r in rows if not r['match']],files=rows)
if len(sys.argv)>1:
 with (p/sys.argv[1]).open('x') as h:json.dump(out,h,indent=2)
print(json.dumps({k:v for k,v in out.items() if k!='files'}))
raise SystemExit(bool(out['mismatches']))
