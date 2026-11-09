import sys,json,hashlib
from pathlib import Path
r=Path(__file__).resolve().parent
ident,name,a,z=sys.argv[1:];p=r/'packet/private/primary'/ident/'files'/name
b=p.read_bytes();a=int(a);z=len(b) if z=='end' else int(z)
assert 0<=a<z<=len(b)
print(f'PRIMARY {ident}/{name} [{a},{z})/{len(b)} SHA256 {hashlib.sha256(b).hexdigest()}\n')
print(b[a:z].decode())
with (r/'packet/private/primary-displays.jsonl').open('a') as f:f.write(json.dumps({'id':ident,'file':name,'start':a,'end':z,'kind':'display; semantic acknowledgment in notes'})+'\n')
