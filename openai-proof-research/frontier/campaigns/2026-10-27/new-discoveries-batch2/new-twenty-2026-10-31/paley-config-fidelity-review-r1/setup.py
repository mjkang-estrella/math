import pathlib,json,hashlib,zipfile,stat
D=pathlib.Path(__file__).resolve().parent; A=D.parent/'expanded-corpus-r49'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
f=json.loads((D/'frozen-inputs.json').read_text())['files']; bad={p:{'expected':s,'actual':sha(pathlib.Path(p)) if pathlib.Path(p).exists() else None} for p,s in f.items() if not pathlib.Path(p).exists() or sha(pathlib.Path(p))!=s}
(D/'integrity-before.json').write_text(json.dumps({'bindings':len(f),'mismatches':bad},indent=2));print('bindings',len(f),'mismatches',bad)
Z=A/'proof-packet.zip';print('ZIP',sha(Z)); E=D/'extracted';E.mkdir(exist_ok=False)
rec=[]
with zipfile.ZipFile(Z) as z:
 for i in z.infolist():
  p=pathlib.PurePosixPath(i.filename); mode=i.external_attr>>16
  assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(mode)
  assert not any(i.filename.endswith(x) for x in ['.olean','.ilean','.so','.a','.o','.dll'])
  if i.is_dir():continue
  b=z.read(i);b.decode('utf8');o=E/p;o.parent.mkdir(parents=True,exist_ok=True);o.write_bytes(b);rec.append({'path':str(p),'sha256':sha(o)})
(D/'extraction.json').write_text(json.dumps(rec,indent=2))
for name in ['MANIFEST.json','environment.json']:
 print(name,(A/name).read_text()[:1500])
print('sources',*[str(p.relative_to(A)) for p in (A/'sources').rglob('*') if p.is_file()],sep='\n')
