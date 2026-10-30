from pathlib import Path
import hashlib,json,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-dsbs-published-source-prior-review-r2'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
code=(S/'verify.py').read_text()
# Run the inspected assertions and exact rational controls without any receipt writes.
prefix,tail=code.split("if '--check-only' not in sys.argv:",1)
assert tail.startswith("\n (L/'after-hashes.json').write_text")
(P/'readonly-review-check.py.txt').write_text(prefix)
ns={'__file__':str(S/'verify.py'),'__name__':'root_readonly_check'}
exec(compile(prefix,str(S/'verify.py'),'exec'),ns)
for r in json.loads((S/'finalmanifest.json').read_text()):
 p=S/r['path'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256']
for r in freeze:
 p=Path(r['path']);assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256']
out=dict(ns['out'],frozen_files=len(freeze),review_verifier_sha256=sha(S/'verify.py'),root_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),write_policy='Original verifier assertions replayed read-only; all original files unchanged.')
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
