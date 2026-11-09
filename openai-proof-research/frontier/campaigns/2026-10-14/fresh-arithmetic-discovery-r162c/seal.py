"""Create this round's selected-packet seal once. Never updates an existing seal."""
from pathlib import Path
import hashlib,json

r=Path(__file__).resolve().parent
p=r/'packet'
assert not (r/'MANIFEST.json').exists(), 'selected packet already sealed'
assert not (r/'ANCHORS.json').exists(), 'detached anchors already exist'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
entries=[]
for f in sorted(p.rglob('*')):
    assert not f.is_symlink()
    if f.is_file():entries.append({'path':f.relative_to(p).as_posix(),'bytes':f.stat().st_size,'sha256':sha(f)})
data={'schema':1,'scope':'Arithmetic162c exact selected packet','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','files':entries}
with (r/'MANIFEST.json').open('x') as f:f.write(json.dumps(data,indent=2)+'\n')
anchors={name:sha(r/path) for name,path in {'FINAL':'packet/FINAL.md','MANIFEST':'MANIFEST.json','REPORT':'REPORT.md','VERIFIER':'verify_packet.py'}.items()}
with (r/'ANCHORS.json').open('x') as f:f.write(json.dumps(anchors,indent=2)+'\n')
print(json.dumps(anchors,indent=2))
