from pathlib import Path
import hashlib,json,datetime,zipfile,re,io
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'MANIFEST.json').read_text())
assert 'MANIFEST.json' not in manifest and 'verification-receipt.json' not in manifest
for f,h in manifest.items():assert sha(L/f)==h,f
bindings=[]
for f in ['source-bindings.json','mathlib-bindings.json']:
 for r in json.loads((L/f).read_text()):
  # Administrative inputs are immutable snapshots, not live scientific premises.
  if r['copy'].startswith('administrative/'):continue
  assert sha(Path(r['original']))==r['sha256']==sha(L/r['copy']),r
  bindings.append(r)
for m in ['Literal','InstanceG','InstanceH','Rank','Hulls','Geometry']:
 assert sha(L/f'{m}.lean')==sha(L/'frozen/hulls'/f'{m}.lean'),m
for pin in json.loads((L/'pins.json').read_text()):
 p=Path(pin['path']);g=p/'.git'
 if g.is_file():g=(p/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 head=(g/'HEAD').read_text().strip()
 if head.startswith('ref: '):
  ref=head[5:];r=g/ref
  head=r.read_text().strip() if r.exists() else next(s.split()[0] for s in (g/'packed-refs').read_text().splitlines() if s.endswith(' '+ref))
 assert head==pin['revision'],pin
assert len(json.loads((L/'pins.json').read_text()))==9
assert sha(Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'))=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
assert not any(p.suffix in ['.olean','.ilean','.o','.ir','.c'] or '.olean.' in p.name for p in L.rglob('*') if p.is_file())
D=L/'replay/fresh'
with zipfile.ZipFile(L/'source.zip') as z:
 for name in z.namelist():assert z.read(name)==(D/name).read_bytes(),name
for f,h in json.loads((D/'archive-files.json').read_text()).items():assert sha(D/f)==sha(L/f)==h,f
buffer=io.BytesIO()
with zipfile.ZipFile(buffer,'w',compression=zipfile.ZIP_DEFLATED) as z:
 for f in sorted(list(json.loads((D/'archive-files.json').read_text()))+['archive-files.json']):
  info=zipfile.ZipInfo(f,(2026,10,30,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16;z.writestr(info,(L/f).read_bytes())
assert hashlib.sha256(buffer.getvalue()).hexdigest()==sha(L/'source.zip')
replay=json.loads((L/'replay-receipt.json').read_text());assert replay['status']=='PASS' and replay['archive_sha256']==sha(L/'source.zip')
audit=json.loads((L/'audit.json').read_text());assert audit['status']=='PASS' and audit['partial_flags']==False and audit['unsafe_flags']==False
inherited=set(json.loads((L/'frozen/hulls/owned-declarations.json').read_text()))
assert len(inherited)==785 and inherited<=set(json.loads((L/'owned-declarations.json').read_text()))
for m in json.loads((L/'mathematical-modules.json').read_text()):
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|partial)\b',(L/f'{m}.lean').read_text()),m
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='Actual G/H real vertex completeness and hull/section hulls; full-source/novelty HOLD',manifest_sha256=sha(L/'MANIFEST.json'),files=len(manifest),scientific_bindings=len(bindings),package_pins=9,owned=audit['owned'],compiler_calls=replay['compiler_calls'],counts_changed=False)
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
