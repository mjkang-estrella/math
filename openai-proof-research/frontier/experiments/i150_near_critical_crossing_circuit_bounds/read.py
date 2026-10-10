"""Author-side bounded display with exact supplied ranges; never called by offline verifier."""
from pathlib import Path
import sys,json,hashlib
S=Path('frontier/sources/i150_near_critical_crossing_circuit_bounds')
p=Path(sys.argv[1]);t=p.read_text();a=int(sys.argv[2]) if len(sys.argv)>2 else 0;b=min(len(t),int(sys.argv[3])) if len(sys.argv)>3 else len(t)
part=t[a:b];m=S/'read-manifest.json';rows=json.loads(m.read_text()) if m.exists() else []
rows.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,char_start=a,char_end=b,total_characters=len(t),range_sha256=hashlib.sha256(part.encode()).hexdigest(),ending=part[-160:],raw_lf=t.count('\n'),splitlines=len(t.splitlines()),terminal_lf=t.endswith('\n'),display_status='supplied',convention='UTF-8 strict; zero-based half-open Unicode character ranges; LF and splitlines recorded separately'))
m.write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n');print(f'PATH {p} RANGE {a}:{b} TOTAL {len(t)}');print(part)
