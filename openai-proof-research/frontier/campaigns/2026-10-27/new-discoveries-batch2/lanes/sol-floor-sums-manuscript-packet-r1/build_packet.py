from pathlib import Path
import hashlib,json,tarfile,gzip,zipfile,io,shutil
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if (L/'SOURCE-MANIFEST.json').exists():
 # Standalone rebuild from an extracted distribution, without lane history.
 manifest=json.loads((L/'SOURCE-MANIFEST.json').read_text())
 assert all(sha(L/n)==h for n,h in manifest.items())
 data={n:(L/n).read_bytes() for n in manifest}
 data['SOURCE-MANIFEST.json']=(L/'SOURCE-MANIFEST.json').read_bytes()
 for stem in ['source-packet','rebuild']:
  with (L/(stem+'.tar.gz')).open('wb') as raw:
   with gzip.GzipFile(filename='',fileobj=raw,mode='wb',mtime=0) as gz:
    with tarfile.open(fileobj=gz,mode='w',format=tarfile.USTAR_FORMAT) as t:
     for n,b in sorted(data.items()):
      m=tarfile.TarInfo(n);m.size=len(b);m.mode=0o644;m.uid=m.gid=m.mtime=0;t.addfile(m,io.BytesIO(b))
  with zipfile.ZipFile(L/(stem+'.zip'),'w',compression=zipfile.ZIP_STORED) as z:
   for n,b in sorted(data.items()):
    m=zipfile.ZipInfo(n,(1980,1,1,0,0,0));m.create_system=3;m.external_attr=0o100644<<16;z.writestr(m,b)
 assert sha(L/'source-packet.tar.gz')==sha(L/'rebuild.tar.gz')
 assert sha(L/'source-packet.zip')==sha(L/'rebuild.zip')
 print(json.dumps(dict(standalone_rebuild='PASS',tar_sha256=sha(L/'source-packet.tar.gz'),zip_sha256=sha(L/'source-packet.zip'))))
 raise SystemExit(0)
assert json.loads((L/'replay/full-audit-receipt.json').read_text())['status']=='PASS'
files={}
for folder,prefix in [('packet','formal'),('sources','sources'),('certificate','certificate')]:
 for p in (L/folder).rglob('*'):
  if p.is_file():
   assert p.suffix not in ['.olean','.ilean','.ir','.pyc'];files[prefix+'/'+p.relative_to(L/folder).as_posix()]=p
for n in ['paper.md','README.md','VERIFICATION.md','FAILURES.md','build_packet.py','verify_final.py']:
 files[n]=L/n
for p in (L/'frozen').glob('*/*'):
 if p.is_file() and p.suffix=='.md':files['provenance/'+p.parent.name+'/'+p.name]=p
for folder,names in {
 'sol-floor-sums-source-prior-review-r2':['exactcoverage.json','chronology.json','immutable-references.json'],
 'sol-floor-sums-full-formal-review-r4':['semantic-review.json','structural-review.json','independent-replay-receipt.json','immutable-references.json'],
 'sol-floor-sums-dag-assembly-formal-r3':['assembly-inventory.json']}.items():
 for n in names:
  p=L/'frozen'/folder/n
  if p.exists():files['provenance/'+folder+'/'+n]=p
files['provenance/input-bindings.json']=L/'bindings.json'
files['provenance/source-inspection.json']=L/'source-inspection.json'
files['evidence/full-audit-receipt.json']=L/'replay/full-audit-receipt.json'
for n in ['pdf-marker.log','pdf-marker-attempt02.log','stopped-replay-receipt.json']:files['evidence/'+n]=L/n
data={n:p.read_bytes() for n,p in sorted(files.items())}
manifest={n:hashlib.sha256(b).hexdigest() for n,b in data.items()}
data['SOURCE-MANIFEST.json']=(json.dumps(manifest,sort_keys=True,indent=2)+'\n').encode()
def build(tarpath,zippath):
 with tarpath.open('wb') as raw:
  with gzip.GzipFile(filename='',fileobj=raw,mode='wb',mtime=0) as gz:
   with tarfile.open(fileobj=gz,mode='w',format=tarfile.USTAR_FORMAT) as t:
    for n,b in sorted(data.items()):
     m=tarfile.TarInfo(n);m.size=len(b);m.mode=0o644;m.uid=m.gid=m.mtime=0;t.addfile(m,io.BytesIO(b))
 with zipfile.ZipFile(zippath,'w',compression=zipfile.ZIP_STORED) as z:
  for n,b in sorted(data.items()):
   m=zipfile.ZipInfo(n,(1980,1,1,0,0,0));m.create_system=3;m.external_attr=0o100644<<16;z.writestr(m,b)
build(L/'source-packet.tar.gz',L/'source-packet.zip')
build(L/'rebuild.tar.gz',L/'rebuild.zip')
assert sha(L/'source-packet.tar.gz')==sha(L/'rebuild.tar.gz')
assert sha(L/'source-packet.zip')==sha(L/'rebuild.zip')
E=L/'final-extracted';E.mkdir(exist_ok=True)
with tarfile.open(L/'source-packet.tar.gz') as t:t.extractall(E,filter='data')
assert {p.relative_to(E).as_posix() for p in E.rglob('*') if p.is_file()}==set(data)
for n,b in data.items():assert (E/n).read_bytes()==b
with zipfile.ZipFile(L/'source-packet.zip') as z:
 assert set(z.namelist())==set(data)
 for n,b in data.items():assert z.read(n)==b
# No owned mathematical file may differ from the original archive or replay.
with tarfile.open(L/'frozen/input/source-only.tar.gz') as t:
 for m in t:
  if m.name.endswith('.lean'):
   b=t.extractfile(m).read();assert b==(E/'formal'/m.name).read_bytes()==(L/'replay'/m.name).read_bytes()
out=dict(status='PASS',members=len(data),tar_sha256=sha(L/'source-packet.tar.gz'),zip_sha256=sha(L/'source-packet.zip'),double_build_byte_identical=True,extracted_all_member_bytes_equal=True,all_460_lean_files_unchanged=True,no_owned_objects=True)
(L/'archive-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
