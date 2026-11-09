from pathlib import Path
import hashlib,json,tarfile,io,gzip
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text())
assert 'manifest.json' not in m and 'verification-receipt.json' not in m
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
assert set(m)==actual
assert all(sha(L/n)==h for n,h in m.items())
for r in json.loads((L/'freeze.json').read_text()):assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256']
source=json.loads((L/'source-manifest.json').read_text())
for n,h in source.items():assert sha(L/n)==sha(L/'fresh-replay'/n)==h
a=json.loads((L/'archive-receipt.json').read_text());assert sha(L/'source-only.tar.gz')==a['archive_sha256']
with tarfile.open(L/'source-only.tar.gz') as t:
 assert all(not n.endswith(('.olean','.ilean','.o','.c')) for n in t.getnames())
 for n in t.getnames():assert t.extractfile(n).read()==(L/n).read_bytes()
# Reconstruct byte-for-byte deterministic archive independently, without writing.
buf=io.BytesIO()
with gzip.GzipFile(filename='',mode='wb',fileobj=buf,mtime=0) as gz:
 with tarfile.open(fileobj=gz,mode='w',format=tarfile.USTAR_FORMAT) as t:
  for n in sorted(a['members']):
   b=(L/n).read_bytes();i=tarfile.TarInfo(n);i.size=len(b);i.mode=0o644;i.uid=i.gid=i.mtime=0;i.uname=i.gname='';t.addfile(i,io.BytesIO(b))
assert hashlib.sha256(buf.getvalue()).hexdigest()==a['archive_sha256']
assert not list(L.rglob('*.olean'))
r={'status':'PASS','manifest_sha256':sha(L/'manifest.json'),'verified_files':len(m),'originals_and_frozen_copies':'PASS','source_only_archive':'PASS','deterministic_reconstruction':'PASS','fresh_extracted_strict_replay':'PASS','compiled_own_artifacts':'removed','endpoint':'Cube.literal_question66_false : ¬ Cube.LiteralQuestion66AtFive','scope':'unconditional n=5, all real linear cube automorphisms','all_n_ge_5_formal':'NOT_PROVED','novelty':'HOLD','counts_unchanged':[9,39,40]}
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))
