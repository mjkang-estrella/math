from pathlib import Path
import hashlib,json,zipfile,re
l=Path(__file__).resolve().parent
before=json.loads((l/'before.json').read_text())
after={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in before}
(l/'after.json').write_text(json.dumps(after,indent=2)+'\n')
assert before==after
z=next(p for p in before if p.endswith('pdtar-source.zip'))
assert before[z]=='3a599c52f33e8fcbed9294de07b9b6a549606b7d6bd693fdfd834304a67173b4'
packet=zipfile.ZipFile(z)
unchanged={n:hashlib.sha256((l/'extracted'/n).read_bytes()).hexdigest() for n in packet.namelist()}
assert all((l/'extracted'/n).read_bytes()==packet.read(n) for n in packet.namelist())
(l/'extracted-source-hashes.json').write_text(json.dumps(unchanged,indent=2)+'\n')
print('Input hashes identical:',len(before),'; all extracted packet files unchanged:',len(unchanged))
