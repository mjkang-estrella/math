from pathlib import Path,PurePosixPath
import hashlib,json,zipfile,re,stat
root=Path('.').resolve();packet=root/'nut-source-only.zip';sha=lambda b:hashlib.sha256(b).hexdigest()
expected='e4710a538ed6ef60e6649fcb288dd873db52ce613eeddca564627f39c96ef402'
assert sha(packet.read_bytes())==expected
out=root/'safe-extracted';out.mkdir(exist_ok=True)
with zipfile.ZipFile(packet) as z:
 names=z.namelist();assert len(names)==len(set(names));assert sum(i.file_size for i in z.infolist())<512*1024**2
 for i in z.infolist():
  p=PurePosixPath(i.filename);assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename
  assert not stat.S_ISLNK(i.external_attr>>16)
  assert not i.filename.endswith(('.olean','.ilean','.so','.dll','.dylib'))
  target=out.joinpath(*p.parts);assert target.is_relative_to(root)
  if i.is_dir():target.mkdir(parents=True,exist_ok=True)
  else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(z.read(i))
manifest=json.loads((out/'source-manifest.json').read_text())
for name,h in manifest.items():assert sha((out/name).read_bytes())==h,(name,'manifest mismatch')
assert set(manifest)==set(n for n in names if n!='source-manifest.json')
frozen=json.loads(Path('inputs-before.json').read_text());modules={};hits=[]
for p in sorted((out/'formal').glob('*.lean')):
 h=sha(p.read_bytes());key='nut-formal-r7q/formal/'+p.name;assert frozen[key]==h
 modules[p.name]=h
 # Remove nested Lean comments and string literals before searching actual commands.
 s=p.read_text();clean=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2;continue
  if depth and s[i:i+2]=='-/':depth-=1;i+=2;continue
  if depth:i+=1;continue
  if s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j;continue
  if s[i]=='"':
   i+=1
   while i<len(s):
    if s[i]=='\\':i+=2
    elif s[i]=='"':i+=1;break
    else:i+=1
   clean.append(' ');continue
  clean.append(s[i]);i+=1
 for m in re.finditer(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',''.join(clean)):
  hits.append({'file':p.name,'token':m.group()})
assert not hits,hits
Path('MODULE-HASHES.json').write_text(json.dumps(modules,indent=2)+'\n')
receipt=dict(status='PASS',scope='safe source extraction and manifest replay ONLY; no Lean execution',archive_sha256=expected,archive_members=len(names),source_manifest_files=len(manifest),lean_modules=len(modules),frozen_module_identity=True,unsafe_paths=[],forbidden_command_hits=hits,full_lean_replay_performed=False)
Path('receipts/extraction-replay.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
