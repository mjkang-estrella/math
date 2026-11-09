from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'MANIFEST.json').read_text())
for f,h in manifest.items():assert sha(L/f)==h,f
assert 'MANIFEST.json' not in manifest and 'verification-receipt.json' not in manifest
bindings=[]
for f in ['source-bindings.json','mathlib-bindings.json']:
 for row in json.loads((L/f).read_text()):
  assert sha(Path(row['original']))==row['sha256']==sha(L/row['copy']),row
  bindings.append(row)
for name in ['Literal.lean','InstanceG.lean','InstanceH.lean']:
 assert sha(L/name)==sha(L/'frozen/sol-fullerene-rational-polytope-formal-r1'/name)
for pin in json.loads((L/'pins.json').read_text()):
 p=Path(pin['path']);g=p/'.git'
 if g.is_file():g=(p/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 head=(g/'HEAD').read_text().strip()
 if head.startswith('ref: '):
  ref=head[5:];r=g/ref
  head=r.read_text().strip() if r.exists() else next(x.split()[0] for x in (g/'packed-refs').read_text().splitlines() if x.endswith(' '+ref))
 assert head==pin['revision'],pin
assert len(json.loads((L/'pins.json').read_text()))==9
assert sha(Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'))=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
assert not any(p.suffix in ['.olean','.ilean','.o','.ir','.c'] or '.olean.' in p.name for p in L.rglob('*') if p.is_file())
replay=json.loads((L/'replay-receipt.json').read_text());assert replay['status']=='PASS' and replay['archive_sha256']==sha(L/'geometry-source.zip')
receipt=dict(status='PASS',scope='Integrity and replay of staged incomplete geometry; not vertex-list completeness',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'MANIFEST.json'),files=len(manifest),bindings=len(bindings),pins=9,counts_changed=False,novelty='HOLD',owned_declarations=replay['owned_declarations'])
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
