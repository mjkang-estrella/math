"""Acquisition-time reading ledger; not used by offline verifier."""
import sys,json,hashlib
from pathlib import Path
p=Path(sys.argv[1]); b=p.read_bytes();raw=b.decode(); field=sys.argv[4] if len(sys.argv)>4 else None
text=json.loads(raw)[field] if field else raw
if not isinstance(text,str):text=json.dumps(text,indent=2,ensure_ascii=False)
lines=text.splitlines(); a=int(sys.argv[2]);z=min(int(sys.argv[3]),len(lines));assert 1<=a<=z
part='\n'.join(lines[a-1:z]); row=dict(local=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),lf_count=b.count(b'\n'),splitlines_count=len(raw.splitlines()),ends_lf=b.endswith(b'\n'),field=field,decoded_lines=len(lines),start=a,end=z,range_sha256=hashlib.sha256(part.encode()).hexdigest())
m=Path('frontier/sources/i132_discrete_probability_discovery/read-manifest.json');data=json.loads(m.read_text());data.append(row);m.write_text(json.dumps(data,indent=2)+'\n')
print(f'{p} field={field} lines={a}-{z}/{len(lines)}\n'+part)
