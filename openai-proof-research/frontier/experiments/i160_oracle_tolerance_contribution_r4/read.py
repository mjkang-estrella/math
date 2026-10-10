import sys,json,hashlib
from pathlib import Path
S=Path('frontier/sources/i160_oracle_tolerance_contribution_r4')
p=Path(sys.argv[1]); a=int(sys.argv[2]); z=int(sys.argv[3]); raw=p.read_bytes(); lines=raw.decode().splitlines(); assert 1<=a<=z<=len(lines),(a,z,len(lines))
piece='\n'.join(lines[a-1:z]); print('\n'.join(f'{i}: {v}' for i,v in enumerate(lines[a-1:z],a)))
f=S/'read-log.json'; log=json.loads(f.read_text()) if f.exists() else []; log.append(dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest(),start=a,end=z,total=len(lines),ending=lines[z-1],passage_sha256=hashlib.sha256(piece.encode()).hexdigest(),convention='Python splitlines; join LF without appended LF')); f.write_text(json.dumps(log,indent=2)+'\n')
