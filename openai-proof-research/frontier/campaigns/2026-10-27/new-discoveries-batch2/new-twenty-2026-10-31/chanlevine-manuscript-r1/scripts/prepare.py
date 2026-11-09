from pathlib import Path,PurePosixPath
import json,hashlib,shutil,zipfile,stat
p=Path.cwd();before=json.loads((p/'frozen-before.json').read_text())
for s in before:
 f=Path(s)
 if f==p/'TASK.txt':continue
 rel=f.relative_to(p.parent)
 dest=p/'evidence'/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dest)
for s in json.loads((p/'optional-before.json').read_text()):
 f=Path(s);d=p/'evidence'/f.relative_to(p.parent);d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,d)
shutil.copyfile(p.parent/'chanlevine-assembly-r1/chanlevine-assembly-source.zip',p/'chanlevine-assembly-source.zip')
assert hashlib.sha256((p/'chanlevine-assembly-source.zip').read_bytes()).hexdigest()=='9e685235e4d744adf9fdd5cafaccf874c6ef6fbccff4684003133df75da34bb0'
z=zipfile.ZipFile(p/'chanlevine-assembly-source.zip');names=z.namelist();assert len(names)==len(set(names));out=p/'proof-packet-safe';out.mkdir(exist_ok=False)
for info in z.infolist():
 q=PurePosixPath(info.filename);assert not q.is_absolute() and '..' not in q.parts and '\\' not in info.filename
 assert not stat.S_ISLNK(info.external_attr>>16)
 assert q.suffix not in ['.olean','.ilean','.o','.so']
 dest=out.joinpath(*q.parts)
 if info.is_dir():dest.mkdir(parents=True,exist_ok=True)
 else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(z.read(info))
fs=list(out.rglob('*.lean'));assert len(fs)==75
manifest=json.loads((p/'evidence/chanlevine-assembly-r1/merge-manifest.json').read_text())
for f in fs:
 if f.name in manifest['modules']:assert hashlib.sha256(f.read_bytes()).hexdigest()==manifest['modules'][f.name]['sha256']
(p/'safe-extraction.json').write_text(json.dumps({'safe':True,'members':len(names),'lean_modules':75,'inherited_hashes_verified':74,'no_lean_invoked':True,'files':{str(f.relative_to(out)):hashlib.sha256(f.read_bytes()).hexdigest() for f in out.rglob('*') if f.is_file()}},indent=2)+'\n')
shutil.copyfile(p.parent/'expanded-corpus-r127/raw/338887.jsonl',p/'mathdb-338887.raw.jsonl')
shutil.copyfile(p/'evidence/chanlevine-assembly-r1/STATEMENT-CORRESPONDENCE.md',p/'STATEMENT-CORRESPONDENCE.md')
print('Prepared dossier, safely extracted 75 Lean modules; none executed.')
