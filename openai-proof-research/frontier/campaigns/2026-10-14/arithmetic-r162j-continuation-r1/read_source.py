import sys,json,hashlib
from pathlib import Path
r=Path(__file__).resolve().parent
p=r/'packet/private'
records=json.loads((p/'canonical-authentication.json').read_text())
family,tail,start,end=sys.argv[1:]
rec=next(x for x in records if ('/The-Kakeya-' in x['path'])==(family=='k3') and x['path'].endswith('/'+tail))
b=(r/rec['local']).read_bytes(); a=int(start); z=len(b) if end=='end' else int(end)
assert 0<=a<z<=len(b)
print(f"SOURCE {family}/{tail} [{a},{z}) / {len(b)} bytes SHA256 {rec['sha256']}\n")
print(b[a:z].decode())
with (p/'displays.jsonl').open('a') as f: f.write(json.dumps({'path':rec['path'],'start':a,'end':z,'kind':'display; semantic acknowledgement in notes','sha256':hashlib.sha256(b[a:z]).hexdigest()})+'\n')
