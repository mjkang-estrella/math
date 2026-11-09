from pathlib import Path
import hashlib,json,tarfile
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mf=json.loads((L/'manifest.json').read_text())
assert 'manifest.json' not in mf and 'verification-receipt.json' not in mf
assert all(sha(L/n)==h for n,h in mf.items())
assert set(mf)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
for f in ['freeze.json','primary-freeze.json','library-freeze.json','extra-freeze.json']:
 for r in json.loads((L/f).read_text()):
  assert sha(L/r['copy'])==r['sha256']
  if not r['copy'].startswith('administrative/'):assert sha(Path(r['original']))==r['sha256']
pins=json.loads((L/'pins.json').read_text())
assert sha(Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'))==pins['lean_sha256']
assert sha(Path(pins['manifest_original']))==pins['manifest_sha256']
rr=json.loads((L/'fresh-replay/replay-receipt.json').read_text())
assert rr['component_status']=='PASS' and rr['source_endpoint_status']=='NOT_PROVED'
for pin in pins['packages']:
 p=Path(pins['manifest_original']).parent/'.lake/packages'/pin['name'];gd=p/'.git'
 if gd.is_file():gd=(p/gd.read_text().strip().removeprefix('gitdir: ')).resolve()
 h=(gd/'HEAD').read_text().strip()
 if h.startswith('ref: '):
  ref=h[5:]
  h=(gd/ref).read_text().strip() if (gd/ref).exists() else next(x.split()[0] for x in (gd/'packed-refs').read_text().splitlines() if x.endswith(' '+ref))
 assert h==pin['rev']==rr['package_heads'][pin['name']]
ar=json.loads((L/'archive-receipt.json').read_text());assert sha(L/'source-only.tar.gz')==ar['sha256']
with tarfile.open(L/'source-only.tar.gz') as t:
 assert sorted(t.getnames())==ar['members']
 for m in t:
  assert not m.name.endswith(('.olean','.ilean')) and m.mtime==0 and m.uid==m.gid==0
  assert t.extractfile(m).read()==(L/m.name).read_bytes()==(L/'fresh-replay'/m.name).read_bytes()
for n in ['FiniteCore.lean','IntegerLeaf.lean']:assert (L/n).read_bytes()==(L/'frozen'/n).read_bytes()
r={'verification':'PASS','component':'PASS','source_endpoint':'NOT_PROVED','actual_declarations':rr['actual_declaration_count'],'generated_partial_declarations':rr['generated_partial_declarations'],'compiler_and_nine_pins':'UNCHANGED','all_scientific_original_copy_bindings':'PASS','administrative':'SNAPSHOTS_ONLY','archive_sha256':ar['sha256'],'manifest_sha256':sha(L/'manifest.json'),'counts':'9/39/next40 unchanged','independent_clock_realization':'NOT_PROVED','chronological_word_law':'NOT_PROVED','expectation_identity':'NOT_PROVED'}
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
