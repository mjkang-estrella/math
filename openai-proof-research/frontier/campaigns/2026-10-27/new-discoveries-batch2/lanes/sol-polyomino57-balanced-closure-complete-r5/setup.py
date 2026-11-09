from pathlib import Path
import shutil,hashlib,json,zipfile,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(45)
L=Path(__file__).resolve().parent;R=L.parent/'sol-polyomino57-full-closure-formal-r4'
inputs={R/'source-only-r4.zip':'ebef50b76b817c50d3416b16fda6fa0d7abb4aff801d364c23903d851cc6ba70',L.parent/'sol-polyomino57-efficient-certificate-r2/source-only-certificate.zip':'da1721fa1a693fe48f8669a3e8ec4c848f3f9acb05d430029cf26c40c1a76a5f',L.parent/'sol-polyomino57-successor-closure-formal-r3/source-only-closure.zip':'c774f8de22384c57b7c0731e795fd18e7e645328dc772cdf631798dfa38575ea'}
for p,h in inputs.items():assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()==h
(L/'input-hashes.json').write_text(json.dumps({str(p):h for p,h in inputs.items()},indent=2))
W=L/'work';W.mkdir(exist_ok=True)
for p in (R/'fresh-extracted/formal').glob('*.lean'):shutil.copyfile(p,W/p.name)
for p in (R/'fresh-extracted/work').glob('*.olean'):shutil.copyfile(p,W/p.name)
for name in ['pins.json','run.py']:shutil.copyfile(R/'fresh-extracted'/name,L/name)
for name in ['data','closure-path-data']:shutil.copytree(R/name,L/name,dirs_exist_ok=True)
