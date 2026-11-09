from pathlib import Path
import hashlib,json,shutil,zipfile,stat
R=Path(__file__).resolve().parent.parent; P=R.parent
(R/'receipts').mkdir(exist_ok=True)
h=lambda b:hashlib.sha256(b).hexdigest()
files=[]
for lane in ['expanded-corpus-r151','smyth-review-r1']:
 for f in (P/lane).rglob('*'):
  if f.is_file() and not any(x in f.relative_to(P/lane).parts for x in ['tmp','__pycache__']): files.append(f)
F=P/'smyth-formal-r1'
for name in ['SUMMARY.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','results.json','source-only.zip']:
 files.append(F/name)
files+=list((F/'src').glob('*.lean'))+list((F/'replay'/'logs').glob('*'))+list((F/'logs').glob('*'))
files.append(P/'smyth-root-ruling-r1.json')
files += [P/'AGENTS.md',P.parent/'AGENTS.md',R.parents[6]/'AGENTS.md'] if False else []
files += [R/'TASK.txt',P/'AGENTS.md',P.parent/'AGENTS.md',Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md')]
# Mutable parent work is snapshotted only when its final JSON receipts exist.
for name in ['replay-result.json','registry-refresh.json']:
 f=P/'smyth-parent-final-r1'/name
 if f.exists(): files.append(f)
manifest={str(f):{'sha256':h(f.read_bytes()),'bytes':f.stat().st_size} for f in sorted(set(files))}
(R/'inputs-before.json').write_text(json.dumps(manifest,indent=2)+'\n')
for f in sorted(set(files)):
 if f.is_relative_to(P): rel=f.relative_to(P)
 else: rel=Path('instructions')/f.parent.name/f.name
 dest=R/'evidence'/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dest)
packet=R/'source-only.zip';shutil.copyfile(F/'source-only.zip',packet)
assert h(packet.read_bytes())=='82e134f245cd795d51695f1a1be8a15b4167212ff4742d18f2a2f0c5ce7ac0c2'
with zipfile.ZipFile(packet) as z:
 names=z.namelist();total=0
 for item in z.infolist():
  p=Path(item.filename)
  assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(item.external_attr>>16)
  total+=item.file_size
 assert total<100*1024**2 and len(names)==len(set(names))
 dest=R/'packet-extracted';z.extractall(dest)
 for item in z.infolist():
  if not item.is_dir(): assert (dest/item.filename).read_bytes()==z.read(item)
 (R/'receipts'/'packet-safe-extraction.json').write_text(json.dumps({'safe':True,'entries':len(names),'lean_modules':sum(n.endswith('.lean') for n in names),'uncompressed_bytes':total,'sha256':h(packet.read_bytes()),'executed':False},indent=2)+'\n')
print('Frozen files',len(manifest),'packet validated and extracted without execution')
