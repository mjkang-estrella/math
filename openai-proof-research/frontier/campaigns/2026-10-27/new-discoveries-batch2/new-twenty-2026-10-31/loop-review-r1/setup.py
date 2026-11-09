import pathlib,hashlib,json,zipfile,shutil
D=pathlib.Path(__file__).resolve().parent; S=D.parent/'expanded-corpus-r76'
for p in ['scripts','receipts','logs','extracted','sources']: (D/p).mkdir(exist_ok=True)
h={str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(S.rglob('*')) if p.is_file()}
(D/'receipts/input-before.json').write_text(json.dumps(h,indent=2))
with zipfile.ZipFile(S/'380362-proof-source.zip') as z:
 for a in z.infolist():
  p=pathlib.PurePosixPath(a.filename)
  assert not p.is_absolute() and '..' not in p.parts and (a.external_attr>>16)&0o170000 != 0o120000
 z.extractall(D/'extracted')
for p in ['limited.py','replay_lean.py']: shutil.copyfile(S/'scripts'/p,D/'scripts'/p)
(D/'receipts/packet.json').write_text(json.dumps({'sha256':h['380362-proof-source.zip'],'members':z.namelist()},indent=2))
