import pathlib,zipfile,hashlib,json
lane=pathlib.Path(__file__).resolve().parent.parent
files=sorted(lane.glob('StackSort*.lean'))+sorted((lane/'scripts').glob('*.sh'))+sorted((lane/'scripts').glob('*.py'))
files += [lane/n for n in ['SUMMARY.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','numeric.json']]
files=[p for p in files if p.name not in ['build_deps.py']]
manifest={str(p.relative_to(lane)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(lane/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
files.append(lane/'source-manifest.json')
with zipfile.ZipFile(lane/'stacksort-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files:z.write(p,str(p.relative_to(lane)))
out=lane/'fresh-extraction'
assert not out.exists()
out.mkdir()
for n in ['logs','tmp','cache']: (out/n).mkdir()
with zipfile.ZipFile(lane/'stacksort-source.zip') as z:
 for info in z.infolist():
  p=pathlib.PurePosixPath(info.filename)
  assert not p.is_absolute() and '..' not in p.parts
 z.extractall(out)
for p in (out/'scripts').glob('*.sh'):p.chmod(0o755)
for n,h in manifest.items():assert hashlib.sha256((out/n).read_bytes()).hexdigest()==h
print('safe source-only archive, fresh empty extraction, hashes verified',len(manifest),'files')
