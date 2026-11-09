import hashlib,json,pathlib,zipfile
r=pathlib.Path(__file__).resolve().parent.parent
frozen=json.loads((r/'frozen-before.json').read_text())
for name,h in frozen.items():
 assert hashlib.sha256((r/'formal'/name).read_bytes()).hexdigest()==h
 assert hashlib.sha256((r.parent/'chanlevine-formal-r3a/formal'/name).read_bytes()).hexdigest()==h
(r/'frozen-after.json').write_text(json.dumps(frozen,indent=2))
files=sorted((r/'formal').glob('*.lean'))+sorted((r/'scripts').glob('*.py'))
files += [r/n for n in ['SUMMARY.md','REPRODUCE.md','frozen-before.json','frozen-after.json']]
z=r/'chanlevine-round4a-source.zip'
with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED) as out:
 for p in files: out.write(p,p.relative_to(r))
fresh=r/'fresh-extraction-final'; assert not fresh.exists(); fresh.mkdir()
with zipfile.ZipFile(z) as src:
 for i in src.infolist():
  p=pathlib.PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts
 src.extractall(fresh)
for p in files: assert p.read_bytes()==(fresh/p.relative_to(r)).read_bytes()
print('safe source-only archive and fresh byte-identical extraction',hashlib.sha256(z.read_bytes()).hexdigest())
