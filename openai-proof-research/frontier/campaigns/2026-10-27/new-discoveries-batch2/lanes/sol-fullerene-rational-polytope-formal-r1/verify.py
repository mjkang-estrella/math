from pathlib import Path
import json,hashlib,datetime,zipfile
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'MANIFEST.json').read_text())
assert set(m)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
for s,d in m.items():assert h(L/s)==d['sha256'] and (L/s).stat().st_size==d['bytes'],s
rows=json.loads((L/'source-bindings.json').read_text())
for r in rows:
 assert h(L/r['copy'])==r['sha256'],r['copy']
 if r['kind']!='administrative':assert h(Path(r['original']))==r['sha256'],r['original']
assert h(L/'primary/prior--fullerenes.pdf')=='244ea62bb54ea6ac818a924f16c5729629dc0d36c6e756e57da110ef4105eb64'
lib=json.loads((L/'mathlib-bindings.json').read_text())
for r in lib:assert h(Path(r['path']))==r['sha256'],r['path']
for pin in json.loads((L/'pins.json').read_text()):
 p=Path(pin['path'])/'.git'
 if p.is_file():p=(p.parent/p.read_text().strip().removeprefix('gitdir: ')).resolve()
 head=(p/'HEAD').read_text().strip()
 if head.startswith('ref: '):
  ref=head[5:];head=(p/ref).read_text().strip() if (p/ref).exists() else next(x.split()[0] for x in (p/'packed-refs').read_text().splitlines() if x.endswith(' '+ref))
 assert head==pin['revision'],pin['name']
r=json.loads((L/'replay-receipt.json').read_text());assert r['status']=='PASS' and r['archive_sha256']==h(L/'geometry-source.zip')
with zipfile.ZipFile(L/'geometry-source.zip') as z:
 for s,sha in json.loads(z.read('archive-files.json')).items():assert hashlib.sha256(z.read(s)).hexdigest()==sha==h(L/s)
assert not [p for p in L.rglob('*') if p.suffix in ['.olean','.ilean','.ir','.o','.c'] or '.olean.' in p.name]
receipt=dict(status='PASS',scope='Integrity of staged partial geometry; not source-class completion',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=h(L/'MANIFEST.json'),files=len(m),scientific_original_copy_bindings=sum(r['kind']!='administrative' for r in rows),mathlib_sources=len(lib),package_pins=9,replay='PASS',owned_declarations=r['owned_declarations'],counts_changed=False,novelty='HOLD')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
