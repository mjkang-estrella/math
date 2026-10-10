import sys,json,hashlib
from pathlib import Path
p=Path(sys.argv[1]); field=None
if '--field' in sys.argv:
 i=sys.argv.index('--field'); field=sys.argv[i+1]; del sys.argv[i:i+2]
b=p.read_bytes(); t=b.decode(); t=json.loads(t)[field] if field else t
lines=t.splitlines(); start=int(sys.argv[2]) if len(sys.argv)>2 else 1; end=min(int(sys.argv[3]),len(lines)) if len(sys.argv)>3 else len(lines)
out='\n'.join(lines[start-1:end]); rec={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'field':field,'start':start,'end':end,'total':len(lines),'range_sha256':hashlib.sha256(out.encode()).hexdigest(),'raw_lf':b.count(b'\n'),'terminal_lf':b.endswith(b'\n')}
m=Path('frontier/sources/i138_nonlinear_dynamics_discovery/read-manifest.json'); data=json.loads(m.read_text()) if m.exists() else [];data.append(rec);m.write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(rec));print(out)
