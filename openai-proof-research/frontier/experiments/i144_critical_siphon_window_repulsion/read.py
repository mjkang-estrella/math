import sys,json,hashlib,bisect
from pathlib import Path
S=Path('frontier/sources/i144_critical_siphon_window_repulsion')
p=Path(sys.argv[1]);a=int(sys.argv[2]);b=int(sys.argv[3]);raw=p.read_bytes();t=raw.decode();b=min(b,len(t));part=t[a:b]
print(part)
r=dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),char_start=a,char_end=b,total_characters=len(t),range_sha256=hashlib.sha256(part.encode()).hexdigest(),ending=part[-160:],raw_lf=t.count('\n'),splitlines=len(t.splitlines()),terminal_lf=t.endswith('\n'),display_status='supplied')
m=S/'read-manifest.json';rows=json.loads(m.read_text()) if m.exists() else [];rows.append(r);m.write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
