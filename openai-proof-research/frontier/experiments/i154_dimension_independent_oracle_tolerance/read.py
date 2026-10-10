"""Display a requested passage and record its actual requested range; truncations must be recovered separately."""
from pathlib import Path
import sys,json,hashlib
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i154_dimension_independent_oracle_tolerance'
p=sys.argv[1];
if ':' in p:
 k,s=p.split(':',1);p=json.loads((S/'source-aliases.json').read_text())[k]+'/build/'+s
b=(R/p).read_bytes();ls=b.decode().splitlines();a=int(sys.argv[2]) if len(sys.argv)>2 else 1;z=int(sys.argv[3]) if len(sys.argv)>3 else len(ls)
assert 1<=a<=z<=len(ls)
s='\n'.join(ls[a-1:z]);print(p, a,z,len(ls));print(s)
f=S/'display-log.json';x=json.loads(f.read_text()) if f.exists() else []
x.append(dict(local=p,start=a,end=z,line_count=len(ls),file_sha256=hashlib.sha256(b).hexdigest(),passage_sha256=hashlib.sha256(s.encode()).hexdigest(),ending=ls[z-1],convention='splitlines; LF join without appended LF'))
f.write_text(json.dumps(x,indent=2)+'\n')
