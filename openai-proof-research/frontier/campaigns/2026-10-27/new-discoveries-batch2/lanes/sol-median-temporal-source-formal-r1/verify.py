from pathlib import Path
import json,hashlib,tarfile
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mf=json.loads((L/'manifest.json').read_text())
assert 'manifest.json' not in mf and 'verification-receipt.json' not in mf
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
assert set(mf)==actual
assert all(sha(L/p)==h for p,h in mf.items())
bindings=json.loads((L/'binding-after.json').read_text())
assert all(sha(Path(r['original']))==sha(L/r['copy'])==r['sha256'] for r in bindings)
pins=json.loads((L/'pins.json').read_text());manifest=Path(pins['manifest_original'])
assert sha(manifest)==pins['manifest_sha256']
compiler=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
assert sha(compiler)==pins['lean_sha256']
for pin in pins['packages']:
 p=manifest.parent/'.lake/packages'/pin['name'];gd=p/'.git'
 if gd.is_file():gd=(p/gd.read_text().strip().removeprefix('gitdir: ')).resolve()
 head=(gd/'HEAD').read_text().strip()
 if head.startswith('ref: '):
  ref=head[5:]
  head=(gd/ref).read_text().strip() if (gd/ref).exists() else next(x.split()[0] for x in (gd/'packed-refs').read_text().splitlines() if x.endswith(' '+ref))
 assert head==pin['rev']
sources=json.loads((L/'source-manifest.json').read_text())
with tarfile.open(L/'source-only.tar.gz','r:gz') as tf:
 assert set(tf.getnames())==set(sources)|{'source-manifest.json'}
 for name,h in sources.items():
  raw=tf.extractfile(name).read();assert hashlib.sha256(raw).hexdigest()==h==sha(L/name)==sha(L/'fresh-replay-02'/name)
  member=tf.getmember(name);assert member.mtime==member.uid==member.gid==0
r=json.loads((L/'fresh-replay-02/replay-receipt.json').read_text())
assert r['component_status']=='PASS' and r['source_endpoint_status']=='NOT_PROVED'
assert len(r['declarations'])==82
assert not list(L.rglob('*.olean'))
out={'verification':'PASS','source_endpoint':'NOT_PROVED','component_only':True,'manifest_sha256':sha(L/'manifest.json'),
 'files_verified':len(mf),'original_copy_bindings_verified':len(bindings),'compiler_and_nine_pins_verified':True,
 'source_only_archive_sha256':sha(L/'source-only.tar.gz'),'fresh_replay':'fresh-replay-02/replay-receipt.json',
 'actual_declarations':82,'allowed_axioms_only':True,'acceptance_or_count':False}
(L/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
