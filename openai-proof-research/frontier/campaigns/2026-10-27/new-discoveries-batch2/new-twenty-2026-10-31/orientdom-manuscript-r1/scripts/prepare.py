from pathlib import Path
import hashlib,json,shutil,zipfile,stat
R=Path.cwd(); P=R.parent
names=['expanded-corpus-r178','orientdom-review-r1','orientdom-priorart-r1','orientdom-parent-final-r1','orientdom-root-ruling-r1.json','orientdom-root-ruling-r2.json']
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
files=[]
for n in names:
 p=P/n; files.extend(sorted(p.rglob('*')) if p.is_dir() else [p])
m={str(p.relative_to(P)):dict(sha256=digest(p),bytes=p.stat().st_size) for p in files if p.is_file()}
(R/'inputs-before.json').write_text(json.dumps(m,indent=2)+'\n')
for n in names:
 p=P/n; q=R/'inputs'/n
 if p.is_dir(): shutil.copytree(p,q)
 else: q.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(p,q)
packet=R/'inputs/expanded-corpus-r178/Lean-packet.zip'
assert digest(packet)=='3d9361bef2cc188b191519cd9718e4d983ccbe6b17df8dec6448dcf5228ab1d6'
shutil.copyfile(packet,R/'Lean-packet.zip')
extract=R/'packet-safe-extraction'; extract.mkdir(); members=[]
with zipfile.ZipFile(packet) as z:
 assert sum(i.file_size for i in z.infolist())<64*1024**2
 for i in z.infolist():
  p=Path(i.filename); mode=i.external_attr>>16
  assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(mode) and '\\' not in i.filename
  dest=extract/p; assert dest.resolve().is_relative_to(extract.resolve())
  if i.is_dir(): dest.mkdir(parents=True,exist_ok=True)
  else:
   dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(z.read(i)); members.append(dict(path=i.filename,sha256=digest(dest),bytes=i.file_size))
(R/'receipts/packet-extraction.json').write_text(json.dumps(dict(status='PASS',packet_sha256=digest(packet),members=members,executed_code=False),indent=2)+'\n')
raw=R/'inputs/expanded-corpus-r178/raw/360905.jsonl'; shutil.copyfile(raw,R/'MathDB-360905.raw.jsonl')
(R/'receipts/raw.json').write_text(json.dumps(dict(source='expanded-corpus-r178/raw/360905.jsonl',sha256=digest(raw),bytes=raw.stat().st_size),indent=2)+'\n')
print('Frozen files:',len(m)); print('packet:',members)
