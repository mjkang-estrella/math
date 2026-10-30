from pathlib import Path
import hashlib,json,datetime,io,contextlib
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r175'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n');counts={}
for name in ['scientific-freeze.json','finalmanifest.json']:
 j=json.loads((S/name).read_text())
 for path,r in j['records'].items():
  p=S/path;assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],path
 counts[name]=len(j['records'])
 if name=='finalmanifest.json':assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(j['excludes'])==set(j['records'])
for path,h in json.loads((S/'primary-hashes.json').read_text()).items():assert sha(S/path)==h
binding=json.loads((S/'guard-binding.json').read_text());assert sha(Path(binding['path']))==binding['sha256']
code=(S/'checks.py').read_text();(P/'checks.py.txt').write_text(code)
out=io.StringIO()
with contextlib.redirect_stdout(out):exec(compile(code,str(S/'checks.py'),'exec'),{'__file__':str(S/'checks.py'),'__name__':'root_private_replay'})
(P/'checks.json').write_text(out.getvalue());assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
for r in freeze:
 p=Path(r['path']);assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified=counts,frozen_files=len(freeze),private_exact_replay='byte-identical',qualification='Finite rational controls and source-byte integrity; no uniform-risk estimator or source refutation.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
