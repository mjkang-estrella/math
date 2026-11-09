import hashlib,json,pathlib,zipfile
r=pathlib.Path(__file__).resolve().parent.parent
before=json.loads((r/'frozen-before.json').read_text())
after={name:hashlib.sha256((r/'formal'/name).read_bytes()).hexdigest() for name in before}
assert before==after and len(before)==36
(r/'frozen-after.json').write_text(json.dumps(after,indent=2)+'\n')
files=sorted((r/'formal').glob('*.lean'))+sorted((r/'scripts').glob('*.py'))
files += [r/n for n in ['SUMMARY.md','REPRODUCE.md','frozen-before.json','frozen-after.json']]
z=r/'chanlevine-round7c-source.zip'
with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED) as out:
 for p in files:out.write(p,p.relative_to(r))
fresh=r/'fresh-extraction'
assert not fresh.exists()
fresh.mkdir()
with zipfile.ZipFile(z) as inp:
 for n in inp.namelist():
  p=pathlib.PurePosixPath(n)
  assert not p.is_absolute() and '..' not in p.parts
 inp.extractall(fresh)
 for n in inp.namelist():assert inp.read(n)==(fresh/n).read_bytes()
print(z,hashlib.sha256(z.read_bytes()).hexdigest())
